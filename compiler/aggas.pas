{
    Copyright (c) 1998-2006 by the Free Pascal team

    This unit implements the generic part of the GNU assembler
    (v2.8 or later) writer

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

 ****************************************************************************
}
{ Base unit for writing GNU assembler output.
}
unit aggas;

{$i fpcdefs.inc}

interface

    uses
      cclasses,
      globtype,globals,
      aasmbase,aasmtai,aasmdata,aasmcpu,
      assemble;

    type
      TCPUInstrWriter = class;
      {# This is a derived class which is used to write
         GAS styled assembler.
      }

      { TGNUAssembler }

      TGNUAssembler=class(texternalassembler)
      protected
        function sectionname(atype:TAsmSectiontype;const aname:string;aorder:TAsmSectionOrder):string;virtual;
        function sectionattrs_coff(atype:TAsmSectiontype):string;virtual;
        function sectionalignment_aix(atype:TAsmSectiontype;secalign: byte):string;
        procedure WriteSection(atype:TAsmSectiontype;const aname:string;aorder:TAsmSectionOrder;secalign:byte);
        procedure WriteExtraHeader;virtual;
        procedure WriteExtraFooter;virtual;
        procedure WriteInstruction(hp: tai);
        procedure WriteWeakSymbolDef(s: tasmsymbol); virtual;
        procedure WriteAixStringConst(hp: tai_string);
        procedure WriteAixIntConst(hp: tai_const);
        procedure WriteDirectiveName(dir: TAsmDirective); virtual;
       public
        function MakeCmdLine: TCmdStr; override;
        procedure WriteTree(p:TAsmList);override;
        procedure WriteAsmList;override;
        destructor destroy; override;
       private
        setcount: longint;
        procedure WriteDecodedSleb128(a: int64);
        procedure WriteDecodedUleb128(a: qword);
        function NextSetLabel: string;
       protected
        InstrWriter: TCPUInstrWriter;
      end;


      {# This is the base class for writing instructions.

         The WriteInstruction() method must be overridden
         to write a single instruction to the assembler
         file.
      }
      TCPUInstrWriter = class
        constructor create(_owner: TGNUAssembler);
        procedure WriteInstruction(hp : tai); virtual; abstract;
       protected
        owner: TGNUAssembler;
      end;


      { TAppleGNUAssembler }

      TAppleGNUAssembler=class(TGNUAssembler)
       protected
        function sectionname(atype:TAsmSectiontype;const aname:string;aorder:TAsmSectionOrder):string;override;
        procedure WriteWeakSymbolDef(s: tasmsymbol); override;

       end;


      TAoutGNUAssembler=class(TGNUAssembler)
        function sectionname(atype:TAsmSectiontype;const aname:string;aorder:TAsmSectionOrder):string;override;
       end;


implementation

    uses
      SysUtils,
      cutils,cfileutl,systems,
      fmodule,finput,verbose,
      itcpugas,cpubase;

    const
      line_length = 70;

    var
      symendcount  : longint;

    type
{$ifdef cpuextended}
      t80bitarray = array[0..9] of byte;
{$endif cpuextended}
      t64bitarray = array[0..7] of byte;
      t32bitarray = array[0..3] of byte;

{****************************************************************************}
{                          Support routines                                  }
{****************************************************************************}

    function single2str(d : single) : string;
      var
         hs : string;
      begin
         str(d,hs);
      { replace space with + }
         if hs[1]=' ' then
          hs[1]:='+';
         single2str:='0d'+hs
      end;

    function double2str(d : double) : string;
      var
         hs : string;
      begin
         str(d,hs);
      { replace space with + }
         if hs[1]=' ' then
          hs[1]:='+';
         double2str:='0d'+hs
      end;

    function extended2str(e : extended) : string;
      var
         hs : string;
      begin
         str(e,hs);
      { replace space with + }
         if hs[1]=' ' then
          hs[1]:='+';
         extended2str:='0d'+hs
      end;


  { convert floating point values }
  { to correct endian             }
  procedure swap64bitarray(var t: t64bitarray);
    var
     b: byte;
    begin
      b:= t[7];
      t[7] := t[0];
      t[0] := b;

      b := t[6];
      t[6] := t[1];
      t[1] := b;

      b:= t[5];
      t[5] := t[2];
      t[2] := b;

      b:= t[4];
      t[4] := t[3];
      t[3] := b;
   end;


   procedure swap32bitarray(var t: t32bitarray);
    var
     b: byte;
    begin
      b:= t[1];
      t[1]:= t[2];
      t[2]:= b;

      b:= t[0];
      t[0]:= t[3];
      t[3]:= b;
    end;


    const
      ait_const2str : array[aitconst_128bit..aitconst_half16bit] of string[20]=(
        #9'.fixme128'#9,#9'.quad'#9,#9'.long'#9,#9'.short'#9,#9'.byte'#9,
        #9'.sleb128'#9,#9'.uleb128'#9,
        #9'.rva'#9,#9'.secrel32'#9,#9'.quad'#9,#9'.long'#9,#9'.short'#9
      );

{****************************************************************************}
{                          GNU Assembler writer                              }
{****************************************************************************}

    destructor TGNUAssembler.Destroy;
      begin
        InstrWriter.free;
        inherited destroy;
      end;


    function TGNUAssembler.MakeCmdLine: TCmdStr;
      begin
        result := inherited MakeCmdLine;
        // MWE: disabled again. It generates dwarf info for the generated .s
        //      files as well. This conflicts with the info we generate
        // if target_dbg.id = dbg_dwarf then
        //  result := result + ' --gdwarf-2';
      end;


    function TGNUAssembler.NextSetLabel: string;
      begin
        inc(setcount);
        result := target_asm.labelprefix+'$set$'+tostr(setcount);
      end;

    function is_smart_section(atype:TAsmSectiontype):boolean;
      begin
        { For bss we need to set some flags that are target dependent,
          it is easier to disable it for smartlinking. It doesn't take up
          filespace }
        result:=not(target_info.system in systems_darwin) and
           create_smartlink_sections and
           (atype<>sec_toc) and
           (atype<>sec_user) and
           { on embedded systems every byte counts, so smartlink bss too }
           ((atype<>sec_bss) or (target_info.system in systems_embedded));
      end;

    function TGNUAssembler.sectionname(atype:TAsmSectiontype;const aname:string;aorder:TAsmSectionOrder):string;
      const
        secnames : array[TAsmSectiontype] of string[length('__DATA, __datacoal_nt,coalesced')] = ('','',
          '.text',
          '.data',
{ why doesn't .rodata work? (FK) }
{ sometimes we have to create a data.rel.ro instead of .rodata, e.g. for  }
{ vtables (and anything else containing relocations), otherwise those are }
{ not relocated properly on e.g. linux/ppc64. g++ generates there for a   }
{ vtable for a class called Window:                                       }
{ .section .data.rel.ro._ZTV6Window,"awG",@progbits,_ZTV6Window,comdat    }
{ TODO: .data.ro not yet working}
{$if defined(arm) or defined(powerpc)}
          '.rodata',
{$else arm}
          '.data',
{$endif arm}
{$if defined(m68k)} { Amiga/m68k GNU AS doesn't seem to like .rodata (KB) }
          '.data',
{$else}
          '.rodata',
{$endif}
          '.bss',
          '.threadvar',
          '.pdata',
          '', { stubs }
          '__DATA,__nl_symbol_ptr',
          '__DATA,__la_symbol_ptr',
          '__DATA,__mod_init_func',
          '__DATA,__mod_term_func',
          '.stab',
          '.stabstr',
          '.idata$2','.idata$4','.idata$5','.idata$6','.idata$7','.edata',
          '.eh_frame',
          '.debug_frame','.debug_info','.debug_line','.debug_abbrev',
          '.fpc',
          '.toc',
          '.init',
          '.fini',
          '.objc_class',
          '.objc_meta_class',
          '.objc_cat_cls_meth',
          '.objc_cat_inst_meth',
          '.objc_protocol',
          '.objc_string_object',
          '.objc_cls_meth',
          '.objc_inst_meth',
          '.objc_cls_refs',
          '.objc_message_refs',
          '.objc_symbols',
          '.objc_category',
          '.objc_class_vars',
          '.objc_instance_vars',
          '.objc_module_info',
          '.objc_class_names',
          '.objc_meth_var_types',
          '.objc_meth_var_names',
          '.objc_selector_strs',
          '.objc_protocol_ext',
          '.objc_class_ext',
          '.objc_property',
          '.objc_image_info',
          '.objc_cstring_object',
          '.objc_sel_fixup',
          '__DATA,__objc_data',
          '__DATA,__objc_const',
          '.objc_superrefs',
          '__DATA, __datacoal_nt,coalesced',
          '.objc_classlist',
          '.objc_nlclasslist',
          '.objc_catlist',
          '.obcj_nlcatlist',
          '.objc_protolist'
        );
        secnames_pic : array[TAsmSectiontype] of string[length('__DATA, __datacoal_nt,coalesced')] = ('','',
          '.text',
          '.data.rel',
          '.data.rel',
          '.data.rel',
          '.bss',
          '.threadvar',
          '.pdata',
          '', { stubs }
          '__DATA,__nl_symbol_ptr',
          '__DATA,__la_symbol_ptr',
          '__DATA,__mod_init_func',
          '__DATA,__mod_term_func',
          '.stab',
          '.stabstr',
          '.idata$2','.idata$4','.idata$5','.idata$6','.idata$7','.edata',
          '.eh_frame',
          '.debug_frame','.debug_info','.debug_line','.debug_abbrev',
          '.fpc',
          '.toc',
          '.init',
          '.fini',
          '.objc_class',
          '.objc_meta_class',
          '.objc_cat_cls_meth',
          '.objc_cat_inst_meth',
          '.objc_protocol',
          '.objc_string_object',
          '.objc_cls_meth',
          '.objc_inst_meth',
          '.objc_cls_refs',
          '.objc_message_refs',
          '.objc_symbols',
          '.objc_category',
          '.objc_class_vars',
          '.objc_instance_vars',
          '.objc_module_info',
          '.objc_class_names',
          '.objc_meth_var_types',
          '.objc_meth_var_names',
          '.objc_selector_strs',
          '.objc_protocol_ext',
          '.objc_class_ext',
          '.objc_property',
          '.objc_image_info',
          '.objc_cstring_object',
          '.objc_sel_fixup',
          '__DATA, __objc_data',
          '__DATA, __objc_const',
          '.objc_superrefs',
          '__DATA, __datacoal_nt,coalesced',
          '.objc_classlist',
          '.objc_nlclasslist',
          '.objc_catlist',
          '.obcj_nlcatlist',
          '.objc_protolist'
        );
      var
        sep     : string[3];
        secname : string;
      begin
        if (cs_create_pic in current_settings.moduleswitches) and
           not(target_info.system in systems_darwin) then
          secname:=secnames_pic[atype]
        else
          secname:=secnames[atype];
{$ifdef m68k}
        { old Amiga GNU AS doesn't support .section .fpc }
        if (atype=sec_fpc) and (target_info.system = system_m68k_amiga) then
            secname:=secnames[sec_data];
{$endif}
        if (atype=sec_fpc) and (Copy(aname,1,3)='res') then
          begin
            result:=secname+'.'+aname;
            exit;
          end;

        if (atype=sec_threadvar) and
          (target_info.system in (systems_windows+systems_wince)) then
          secname:='.tls';

        { go32v2 stub only loads .text and .data sections, and allocates space for .bss.
          Thus, data which normally goes into .rodata and .rodata_norel sections must
          end up in .data section }
        if (atype in [sec_rodata,sec_rodata_norel]) and
          (target_info.system=system_i386_go32v2) then
          secname:='.data';

        { section type user gives the user full controll on the section name }
        if atype=sec_user then
          secname:=aname;

        if is_smart_section(atype) and (aname<>'') then
          begin
            case aorder of
              secorder_begin :
                sep:='.b_';
              secorder_end :
                sep:='.z_';
              else
                sep:='.n_';
            end;
            result:=secname+sep+aname
          end
        else
          result:=secname;
      end;


    function TGNUAssembler.sectionattrs_coff(atype:TAsmSectiontype):string;
      begin
        case atype of
          sec_code, sec_init, sec_fini, sec_stub:
            result:='x';

          { TODO: must be individual for each section }
          sec_user:
            result:='d';

          sec_data, sec_data_lazy, sec_data_nonlazy, sec_fpc,
          sec_idata2, sec_idata4, sec_idata5, sec_idata6, sec_idata7:
            result:='d';

          { TODO: these need a fix to become read-only }
          sec_rodata, sec_rodata_norel:
            result:='d';

          sec_bss:
            result:='b';

          { TODO: Somewhat questionable. FPC does not allow initialized threadvars,
            so no sense to mark it as containing data. But Windows allows it to
            contain data, and Linux even has .tdata and .tbss }
          sec_threadvar:
            result:='b';

          sec_pdata, sec_edata, sec_eh_frame, sec_toc:
            result:='r';

          sec_stab,sec_stabstr,
          sec_debug_frame,sec_debug_info,sec_debug_line,sec_debug_abbrev:
            result:='n';
        else
          result:='';  { defaults to data+load }
        end;
      end;


    function TGNUAssembler.sectionalignment_aix(atype:TAsmSectiontype;secalign: byte): string;
      var
        l: longint;
      begin
        if (secalign=0) or
           not(atype in [sec_code,sec_bss,sec_rodata_norel,sec_rodata,sec_data]) then
          begin
            result:='';
            exit;
          end;
        if not ispowerof2(secalign,l) then
          internalerror(2012022201);
        result:=tostr(l);
      end;


    procedure TGNUAssembler.WriteSection(atype:TAsmSectiontype;const aname:string;aorder:TAsmSectionOrder;secalign:byte);
      var
        s : string;
      begin
        AsmLn;
        case target_info.system of
         system_i386_OS2,
         system_i386_EMX,
         system_m68k_amiga,  { amiga has old GNU AS (2.14), which blews up from .section (KB) }
         system_m68k_linux: ;
         system_powerpc_darwin,
         system_i386_darwin,
         system_i386_iphonesim,
         system_powerpc64_darwin,
         system_x86_64_darwin,
         system_arm_darwin,
         system_powerpc_aix,
         system_powerpc64_aix:
           begin
             if (atype in [sec_stub,sec_objc_data,sec_objc_const,sec_data_coalesced]) then
               AsmWrite('.section ');
           end
         else
          AsmWrite('.section ');
        end;
        s:=sectionname(atype,aname,aorder);
        AsmWrite(s);
        case atype of
          sec_fpc :
            if aname = 'resptrs' then
              AsmWrite(', "a", @progbits');
          sec_stub :
            begin
              case target_info.system of
                { there are processor-independent shortcuts available    }
                { for this, namely .symbol_stub and .picsymbol_stub, but }
                { they don't work and gcc doesn't use them either...     }
                system_powerpc_darwin,
                system_powerpc64_darwin:
                  if (cs_create_pic in current_settings.moduleswitches) then
                    AsmWriteln('__TEXT,__picsymbolstub1,symbol_stubs,pure_instructions,32')
                  else
                    AsmWriteln('__TEXT,__symbol_stub1,symbol_stubs,pure_instructions,16');
                system_i386_darwin,
                system_i386_iphonesim:
                  AsmWriteln('__IMPORT,__jump_table,symbol_stubs,self_modifying_code+pure_instructions,5');
                system_arm_darwin:
                  if (cs_create_pic in current_settings.moduleswitches) then
                    AsmWriteln('.section __TEXT,__picsymbolstub4,symbol_stubs,none,16')
                  else
                    AsmWriteln('.section __TEXT,__symbol_stub4,symbol_stubs,none,12')
                { darwin/x86-64 uses RIP-based GOT addressing, no symbol stubs }
                else
                  internalerror(2006031101);
              end;
            end;
        else
          { GNU AS won't recognize '.text.n_something' section name as belonging
            to '.text' and assigns default attributes to it, which is not
            always correct. We have to fix it.

            TODO: This likely applies to all systems which smartlink without
            creating libraries }
          if (target_info.system in [system_i386_win32,system_x86_64_win64]) and
            is_smart_section(atype) and (aname<>'') then
            begin
              s:=sectionattrs_coff(atype);
              if (s<>'') then
                AsmWrite(',"'+s+'"');
            end
         else if target_info.system in systems_aix then
           begin
             s:=sectionalignment_aix(atype,secalign);
             if s<>'' then
               AsmWrite(','+s);
           end;
        end;
        AsmLn;
        LastSecType:=atype;
      end;


    procedure TGNUAssembler.WriteDecodedUleb128(a: qword);
      var
        i,len : longint;
        buf   : array[0..63] of byte;
      begin
        len:=EncodeUleb128(a,buf);
        for i:=0 to len-1 do
          begin
            if (i > 0) then
              AsmWrite(',');
            AsmWrite(tostr(buf[i]));
          end;
      end;


    procedure TGNUAssembler.WriteDecodedSleb128(a: int64);
      var
        i,len : longint;
        buf   : array[0..255] of byte;
      begin
        len:=EncodeSleb128(a,buf);
        for i:=0 to len-1 do
          begin
            if (i > 0) then
              AsmWrite(',');
            AsmWrite(tostr(buf[i]));
          end;
      end;


    procedure TGNUAssembler.WriteTree(p:TAsmList);

      function needsObject(hp : tai_symbol) : boolean;
        begin
          needsObject :=
              (
                assigned(hp.next) and
                 (tai(hp.next).typ in [ait_const,ait_datablock,
                  ait_real_32bit,ait_real_64bit,ait_real_80bit,ait_comp_64bit])
              ) or
              (hp.sym.typ=AT_DATA);

        end;


      procedure doalign(alignment: byte; use_op: boolean; fillop: byte; out last_align: longint);
        var
          i: longint;
        begin
          last_align:=alignment;
          if alignment>1 then
            begin
              if not(target_info.system in (systems_darwin+systems_aix)) then
                begin
                  AsmWrite(#9'.balign '+tostr(alignment));
                  if use_op then
                    AsmWrite(','+tostr(fillop))
{$ifdef x86}
                  { force NOP as alignment op code }
                  else if LastSecType=sec_code then
                    AsmWrite(',0x90');
{$endif x86}
                end
              else
                begin
                  { darwin and aix as only support .align }
                  if not ispowerof2(alignment,i) then
                    internalerror(2003010305);
                  AsmWrite(#9'.align '+tostr(i));
                  last_align:=i;
                end;
              AsmLn;
            end;
        end;

    var
      ch       : char;
      hp       : tai;
      constdef : taiconst_type;
      s,t      : string;
      i,pos,l  : longint;
      InlineLevel : cardinal;
      last_align : longint;
      co       : comp;
      sin      : single;
      d        : double;
{$ifdef cpuextended}
      e        : extended;
{$endif cpuextended}
      do_line  : boolean;

      sepChar : char;
      replaceforbidden: boolean;
    begin
      if not assigned(p) then
       exit;
      replaceforbidden:=target_asm.dollarsign<>'$';

      last_align := 2;
      InlineLevel:=0;
      { lineinfo is only needed for al_procedures (PFV) }
      do_line:=(cs_asm_source in current_settings.globalswitches) or
               ((cs_lineinfo in current_settings.moduleswitches)
                 and (p=current_asmdata.asmlists[al_procedures]));
      hp:=tai(p.first);
      while assigned(hp) do
       begin
         prefetch(pointer(hp.next)^);
         if not(hp.typ in SkipLineInfo) then
          begin
            current_filepos:=tailineinfo(hp).fileinfo;
            { no line info for inlined code }
            if do_line and (inlinelevel=0) then
              WriteSourceLine(hp as tailineinfo);
          end;

         case hp.typ of

           ait_comment :
             Begin
               AsmWrite(target_asm.comment);
               AsmWritePChar(tai_comment(hp).str);
               AsmLn;
             End;

           ait_regalloc :
             begin
               if (cs_asm_regalloc in current_settings.globalswitches) then
                 begin
                   AsmWrite(#9+target_asm.comment+'Register ');
                   repeat
                     AsmWrite(std_regname(Tai_regalloc(hp).reg));
                     if (hp.next=nil) or
                        (tai(hp.next).typ<>ait_regalloc) or
                        (tai_regalloc(hp.next).ratype<>tai_regalloc(hp).ratype) then
                       break;
                     hp:=tai(hp.next);
                     AsmWrite(',');
                   until false;
                   AsmWrite(' ');
                   AsmWriteLn(regallocstr[tai_regalloc(hp).ratype]);
                 end;
             end;

           ait_tempalloc :
             begin
               if (cs_asm_tempalloc in current_settings.globalswitches) then
                 WriteTempalloc(tai_tempalloc(hp));
             end;

           ait_align :
             begin
               doalign(tai_align_abstract(hp).aligntype,tai_align_abstract(hp).use_op,tai_align_abstract(hp).fillop,last_align);
             end;

           ait_section :
             begin
               if tai_section(hp).sectype<>sec_none then
                 if replaceforbidden then
                   WriteSection(tai_section(hp).sectype,ReplaceForbiddenAsmSymbolChars(tai_section(hp).name^),tai_section(hp).secorder,tai_section(hp).secalign)
                 else
                   WriteSection(tai_section(hp).sectype,tai_section(hp).name^,tai_section(hp).secorder,tai_section(hp).secalign)
               else
                 begin
{$ifdef EXTDEBUG}
                   AsmWrite(target_asm.comment);
                   AsmWriteln(' sec_none');
{$endif EXTDEBUG}
                end;
             end;

           ait_datablock :
             begin
               if (target_info.system in systems_darwin) then
                 begin
                   { On Mac OS X you can't have common symbols in a shared library
                     since those are in the TEXT section and the text section is
                     read-only in shared libraries (so it can be shared among different
                     processes). The alternate code creates some kind of common symbols
                     in the data segment.
                   }
                   if tai_datablock(hp).is_global then
                     begin
                       asmwrite('.globl ');
                       asmwriteln(tai_datablock(hp).sym.name);
                       asmwriteln('.data');
                       asmwrite('.zerofill __DATA, __common, ');
                       asmwrite(tai_datablock(hp).sym.name);
                       asmwriteln(', '+tostr(tai_datablock(hp).size)+','+tostr(last_align));
                       if not(LastSecType in [sec_data,sec_none]) then
                         writesection(LastSecType,'',secorder_default,1 shl last_align);
                     end
                   else
                     begin
                       asmwrite(#9'.lcomm'#9);
                       asmwrite(tai_datablock(hp).sym.name);
                       asmwrite(','+tostr(tai_datablock(hp).size));
                       asmwrite(','+tostr(last_align));
                       asmln;
                     end;
                 end
               else if target_info.system in systems_aix then
                 begin
                   if tai_datablock(hp).is_global then
                     begin
                       asmwrite(#9'.globl ');
                       asmwriteln(ReplaceForbiddenAsmSymbolChars(tai_datablock(hp).sym.name));
                       asmwrite(ReplaceForbiddenAsmSymbolChars(tai_datablock(hp).sym.name));
                       asmwriteln(':');
                       asmwrite(#9'.space ');
                       asmwriteln(tostr(tai_datablock(hp).size));
                       if not(LastSecType in [sec_data,sec_none]) then
                         writesection(LastSecType,'',secorder_default,1 shl last_align);
                     end
                   else
                     begin
                       asmwrite(#9'.lcomm ');
                       asmwrite(ReplaceForbiddenAsmSymbolChars(tai_datablock(hp).sym.name));
                       asmwrite(',_data.bss_[RW],');
                       asmwrite(tostr(tai_datablock(hp).size)+',');
                       asmwriteln(tostr(last_align));
                     end;
                 end
               else
                 begin
{$ifdef USE_COMM_IN_BSS}
                   if writingpackages then
                     begin
                       { The .comm is required for COMMON symbols. These are used
                         in the shared library loading. All the symbols declared in
                         the .so file need to resolve to the data allocated in the main
                         program (PFV) }
                       if tai_datablock(hp).is_global then
                         begin
                           asmwrite(#9'.comm'#9);
                           if replaceforbidden then
                             asmwrite(ReplaceForbiddenAsmSymbolChars(tai_datablock(hp).sym.name))
                           else
                             asmwrite(tai_datablock(hp).sym.name);
                           asmwrite(','+tostr(tai_datablock(hp).size));
                           asmwrite(','+tostr(last_align));
                           asmln;
                         end
                       else
                         begin
                           asmwrite(#9'.lcomm'#9);
                           if replaceforbidden then
                             asmwrite(ReplaceForbiddenAsmSymbolChars(tai_datablock(hp).sym.name));
                           else
                             asmwrite(tai_datablock(hp).sym.name);
                           asmwrite(','+tostr(tai_datablock(hp).size));
                           asmwrite(','+tostr(last_align));
                           asmln;
                         end
                     end
                   else
{$endif USE_COMM_IN_BSS}
                     begin
                       if Tai_datablock(hp).is_global then
                         begin
                           asmwrite(#9'.globl ');
                           if replaceforbidden then
                             asmwriteln(ReplaceForbiddenAsmSymbolChars(Tai_datablock(hp).sym.name))
                           else
                             asmwriteln(Tai_datablock(hp).sym.name);
                         end;
                       if (target_info.system <> system_arm_linux) then
                         sepChar := '@'
                       else
                         sepChar := '%';
                       if replaceforbidden then
                         begin
                           if (tf_needs_symbol_type in target_info.flags) then
                             asmwriteln(#9'.type '+ReplaceForbiddenAsmSymbolChars(Tai_datablock(hp).sym.name)+','+sepChar+'object');
                           if (tf_needs_symbol_size in target_info.flags) and (tai_datablock(hp).size > 0) then
                              asmwriteln(#9'.size '+ReplaceForbiddenAsmSymbolChars(Tai_datablock(hp).sym.name)+','+tostr(Tai_datablock(hp).size));
                           asmwrite(ReplaceForbiddenAsmSymbolChars(Tai_datablock(hp).sym.name))
                         end
                       else
                         begin
                           if (tf_needs_symbol_type in target_info.flags) then
                             asmwriteln(#9'.type '+Tai_datablock(hp).sym.name+','+sepChar+'object');
                           if (tf_needs_symbol_size in target_info.flags) and (tai_datablock(hp).size > 0) then
                             asmwriteln(#9'.size '+Tai_datablock(hp).sym.name+','+tostr(Tai_datablock(hp).size));
                           asmwrite(Tai_datablock(hp).sym.name);
                         end;
                       asmwriteln(':');
                       asmwriteln(#9'.zero '+tostr(Tai_datablock(hp).size));
                     end;
                 end;
             end;

           ait_const:
             begin
               constdef:=tai_const(hp).consttype;
               case constdef of
{$ifndef cpu64bitaddr}
                 aitconst_128bit :
                    begin
                      internalerror(200404291);
                    end;

                 aitconst_64bit :
                    begin
                      if assigned(tai_const(hp).sym) then
                        internalerror(200404292);
                      if not(target_info.system in systems_aix) then
                        begin
                          AsmWrite(ait_const2str[aitconst_32bit]);
                          if target_info.endian = endian_little then
                            begin
                              AsmWrite(tostr(longint(lo(tai_const(hp).value))));
                              AsmWrite(',');
                              AsmWrite(tostr(longint(hi(tai_const(hp).value))));
                            end
                          else
                            begin
                              AsmWrite(tostr(longint(hi(tai_const(hp).value))));
                              AsmWrite(',');
                              AsmWrite(tostr(longint(lo(tai_const(hp).value))));
                            end;
                        end
                      else
                        WriteAixIntConst(tai_const(hp));
                      AsmLn;
                    end;
{$endif cpu64bitaddr}
                 aitconst_uleb128bit,
                 aitconst_sleb128bit,
{$ifdef cpu64bitaddr}
                 aitconst_128bit,
                 aitconst_64bit,
{$endif cpu64bitaddr}
                 aitconst_32bit,
                 aitconst_16bit,
                 aitconst_8bit,
                 aitconst_rva_symbol,
                 aitconst_secrel32_symbol,
                 aitconst_darwin_dwarf_delta32,
                 aitconst_darwin_dwarf_delta64,
                 aitconst_half16bit:
                   begin
                     { the AIX assembler (and for compatibility, the GNU
                       assembler when targeting AIX) automatically aligns
                       .short/.long/.llong to a multiple of 2/4/8 bytes. We
                       don't want that, since this may be data inside a packed
                       record -> use .vbyte instead (byte stream of fixed
                       length) }
                     if (target_info.system in systems_aix) and
                        (constdef in [aitconst_128bit,aitconst_64bit,aitconst_32bit,aitconst_16bit]) and
                        not assigned(tai_const(hp).sym) then
                       begin
                         WriteAixIntConst(tai_const(hp));
                       end
                     else if (target_info.system in systems_darwin) and
                        (constdef in [aitconst_uleb128bit,aitconst_sleb128bit]) then
                       begin
                         AsmWrite(ait_const2str[aitconst_8bit]);
                         case tai_const(hp).consttype of
                           aitconst_uleb128bit:
                             WriteDecodedUleb128(qword(tai_const(hp).value));
                           aitconst_sleb128bit:
                             WriteDecodedSleb128(int64(tai_const(hp).value));
                         end
                       end
                     else
                       begin
                         if not(target_info.system in systems_aix) or
                            (constdef<>aitconst_64bit) then
                           AsmWrite(ait_const2str[constdef])
                         else
                           { can't use .llong, because that forces 8 byte
                             alignnment and we sometimes store addresses on
                             4-byte aligned addresses (e.g. in the RTTI) }
                           AsmWrite('.vbyte'#9'8,');
                         l:=0;
                         t := '';
                         repeat
                           if assigned(tai_const(hp).sym) then
                             begin
                               if assigned(tai_const(hp).endsym) then
                                 begin
                                   if (constdef in [aitconst_darwin_dwarf_delta32,aitconst_darwin_dwarf_delta64]) then
                                     begin
                                       s := NextSetLabel;
                                       t := #9'.set '+s+','+tai_const(hp).endsym.name+'-'+tai_const(hp).sym.name;
                                     end
                                   else
                                     s:=tai_const(hp).endsym.name+'-'+tai_const(hp).sym.name
                                  end
                               else
                                 s:=tai_const(hp).sym.name;
                               if replaceforbidden then
                                 s:=ReplaceForbiddenAsmSymbolChars(s);
                               if tai_const(hp).value<>0 then
                                 s:=s+tostr_with_plus(tai_const(hp).value);
                             end
                           else
{$ifdef cpu64bitaddr}
                             s:=tostr(tai_const(hp).value);
{$else cpu64bitaddr}
                             { 64 bit constants are already handled above in this case }
                             s:=tostr(longint(tai_const(hp).value));
{$endif cpu64bitaddr}
                           if constdef = aitconst_half16bit then
                             s:='('+s+')/2';

                           AsmWrite(s);
                           inc(l,length(s));
                           { Values with symbols are written on a single line to improve
                             reading of the .s file (PFV) }
                           if assigned(tai_const(hp).sym) or
                              not(LastSecType in [sec_data,sec_rodata,sec_rodata_norel]) or
                              (l>line_length) or
                              (hp.next=nil) or
                              (tai(hp.next).typ<>ait_const) or
                              (tai_const(hp.next).consttype<>constdef) or
                              assigned(tai_const(hp.next).sym) then
                             break;
                           hp:=tai(hp.next);
                           AsmWrite(',');
                         until false;
                         if (t <> '') then
                           begin
                             AsmLn;
                             AsmWrite(t);
                           end;
                       end;
                      AsmLn;
                   end;
                 else
                   internalerror(200704251);
               end;
             end;

           { the "and defined(FPC_HAS_TYPE_EXTENDED)" isn't optimal but currently the only solution
             it prevents proper cross compilation to i386 though
           }
{$if defined(cpuextended) and defined(FPC_HAS_TYPE_EXTENDED)}
           ait_real_80bit :
             begin
               if do_line then
                AsmWriteLn(target_asm.comment+'value: '+extended2str(tai_real_80bit(hp).value));
             { Make sure e is a extended type, bestreal could be
               a different type (bestreal) !! (PFV) }
               e:=tai_real_80bit(hp).value;
               AsmWrite(#9'.byte'#9);
               for i:=0 to 9 do
                begin
                  if i<>0 then
                   AsmWrite(',');
                  AsmWrite(tostr(t80bitarray(e)[i]));
                end;
               for i:=11 to tai_real_80bit(hp).savesize do
                 AsmWrite(',0');
               AsmLn;
             end;
{$endif cpuextended}

           ait_real_64bit :
             begin
               if do_line then
                AsmWriteLn(target_asm.comment+'value: '+double2str(tai_real_64bit(hp).value));
               d:=tai_real_64bit(hp).value;
               { swap the values to correct endian if required }
               if source_info.endian <> target_info.endian then
                 swap64bitarray(t64bitarray(d));
               AsmWrite(#9'.byte'#9);
{$ifdef arm}
               if tai_real_64bit(hp).formatoptions=fo_hiloswapped then
                 begin
                   for i:=4 to 7 do
                     begin
                       if i<>4 then
                         AsmWrite(',');
                       AsmWrite(tostr(t64bitarray(d)[i]));
                     end;
                   for i:=0 to 3 do
                     begin
                       AsmWrite(',');
                       AsmWrite(tostr(t64bitarray(d)[i]));
                     end;
                 end
               else
{$endif arm}
                 begin
                   for i:=0 to 7 do
                     begin
                       if i<>0 then
                         AsmWrite(',');
                       AsmWrite(tostr(t64bitarray(d)[i]));
                     end;
                 end;
               AsmLn;
             end;

           ait_real_32bit :
             begin
               if do_line then
                AsmWriteLn(target_asm.comment+'value: '+single2str(tai_real_32bit(hp).value));
               sin:=tai_real_32bit(hp).value;
               { swap the values to correct endian if required }
               if source_info.endian <> target_info.endian then
                 swap32bitarray(t32bitarray(sin));
               AsmWrite(#9'.byte'#9);
               for i:=0 to 3 do
                begin
                  if i<>0 then
                   AsmWrite(',');
                  AsmWrite(tostr(t32bitarray(sin)[i]));
                end;
               AsmLn;
             end;

           ait_comp_64bit :
             begin
               if do_line then
                AsmWriteLn(target_asm.comment+'value: '+extended2str(tai_comp_64bit(hp).value));
               AsmWrite(#9'.byte'#9);
               co:=comp(tai_comp_64bit(hp).value);
               { swap the values to correct endian if required }
               if source_info.endian <> target_info.endian then
                 swap64bitarray(t64bitarray(co));
               for i:=0 to 7 do
                begin
                  if i<>0 then
                   AsmWrite(',');
                  AsmWrite(tostr(t64bitarray(co)[i]));
                end;
               AsmLn;
             end;

           ait_string :
             begin
               pos:=0;
               if not(target_info.system in systems_aix) then
                 begin
                   for i:=1 to tai_string(hp).len do
                    begin
                      if pos=0 then
                       begin
                         AsmWrite(#9'.ascii'#9'"');
                         pos:=20;
                       end;
                      ch:=tai_string(hp).str[i-1];
                      case ch of
                                #0, {This can't be done by range, because a bug in FPC}
                           #1..#31,
                        #128..#255 : s:='\'+tostr(ord(ch) shr 6)+tostr((ord(ch) and 63) shr 3)+tostr(ord(ch) and 7);
                               '"' : s:='\"';
                               '\' : s:='\\';
                      else
                        s:=ch;
                      end;
                      AsmWrite(s);
                      inc(pos,length(s));
                      if (pos>line_length) or (i=tai_string(hp).len) then
                       begin
                         AsmWriteLn('"');
                         pos:=0;
                       end;
                    end;
                 end
               else
                 WriteAixStringConst(tai_string(hp));
             end;

           ait_label :
             begin
               if (tai_label(hp).labsym.is_used) then
                begin
                  if (tai_label(hp).labsym.bind=AB_PRIVATE_EXTERN) then
                    begin
                      AsmWrite(#9'.private_extern ');
                      AsmWriteln(tai_label(hp).labsym.name);
                    end;
                  if tai_label(hp).labsym.bind in [AB_GLOBAL,AB_PRIVATE_EXTERN] then
                   begin
                     AsmWrite('.globl'#9);
                     if replaceforbidden then
                       AsmWriteLn(ReplaceForbiddenAsmSymbolChars(tai_label(hp).labsym.name))
                     else
                       AsmWriteLn(tai_label(hp).labsym.name);
                   end;
                  if replaceforbidden then
                    AsmWrite(ReplaceForbiddenAsmSymbolChars(tai_label(hp).labsym.name))
                  else
                    AsmWrite(tai_label(hp).labsym.name);
                  AsmWriteLn(':');
                end;
             end;

           ait_symbol :
             begin
               if (tai_symbol(hp).sym.bind=AB_PRIVATE_EXTERN) then
                 begin
                   AsmWrite(#9'.private_extern ');
                   if replaceforbidden then
                     AsmWriteln(ReplaceForbiddenAsmSymbolChars(tai_symbol(hp).sym.name))
                   else
                     AsmWriteln(tai_symbol(hp).sym.name);
                 end;
               if (target_info.system = system_powerpc64_linux) and
                 (tai_symbol(hp).sym.typ = AT_FUNCTION) and (cs_profile in current_settings.moduleswitches) then
                 AsmWriteLn('.globl _mcount');

               if tai_symbol(hp).is_global then
                begin
                  AsmWrite('.globl'#9);
                  if replaceforbidden then
                    AsmWriteln(ReplaceForbiddenAsmSymbolChars(tai_symbol(hp).sym.name))
                  else
                    AsmWriteln(tai_symbol(hp).sym.name);
                end;
               if target_info.system in [system_mipsel_linux,system_mips_linux] then
                begin
                  AsmWrite(#9'.ent'#9);
                  if replaceforbidden then
                    AsmWriteln(ReplaceForbiddenAsmSymbolChars(tai_symbol(hp).sym.name))
                  else
                    AsmWriteln(tai_symbol(hp).sym.name);
                end;
               if (target_info.system = system_powerpc64_linux) and
                 (tai_symbol(hp).sym.typ = AT_FUNCTION) then
                 begin
                   AsmWriteLn('.section ".opd", "aw"');
                   AsmWriteLn('.align 3');
                   AsmWriteLn(tai_symbol(hp).sym.name + ':');
                   AsmWriteLn('.quad .' + tai_symbol(hp).sym.name + ', .TOC.@tocbase, 0');
                   AsmWriteLn('.previous');
                   AsmWriteLn('.size ' + tai_symbol(hp).sym.name + ', 24');
                   if (tai_symbol(hp).is_global) then
                     AsmWriteLn('.globl .' + tai_symbol(hp).sym.name);
                   AsmWriteLn('.type .' + tai_symbol(hp).sym.name + ', @function');
                   { the dotted name is the name of the actual function entry }
                   AsmWrite('.');
                 end
               else if (target_info.system in systems_aix) and
                  (tai_symbol(hp).sym.typ = AT_FUNCTION) then
                 begin
                   if target_info.system=system_powerpc_aix then
                     begin
                       s:=#9'.long .';
                       ch:='2';
                     end
                   else
                     begin
                       s:=#9'.llong .';
                       ch:='3';
                     end;
                   AsmWriteLn(#9'.csect '+ReplaceForbiddenAsmSymbolChars(tai_symbol(hp).sym.name)+'[DS],'+ch);
                   AsmWriteLn(ReplaceForbiddenAsmSymbolChars(tai_symbol(hp).sym.name)+':');
                   AsmWriteln(s+ReplaceForbiddenAsmSymbolChars(tai_symbol(hp).sym.name)+', TOC[tc0], 0');
                   AsmWriteln(#9'.csect .text[PR]');
                   if (tai_symbol(hp).is_global) then
                     AsmWriteLn('.globl .'+ReplaceForbiddenAsmSymbolChars(tai_symbol(hp).sym.name))
                   else
                     AsmWriteLn('.lglobl .'+ReplaceForbiddenAsmSymbolChars(tai_symbol(hp).sym.name));
                   { the dotted name is the name of the actual function entry }
                   AsmWrite('.');
                 end
               else
                 begin
                   if (target_info.system <> system_arm_linux) then
                     sepChar := '@'
                   else
                     sepChar := '#';
                   if (tf_needs_symbol_type in target_info.flags) then
                     begin
                       AsmWrite(#9'.type'#9 + tai_symbol(hp).sym.name);
                       if (needsObject(tai_symbol(hp))) then
                         AsmWriteLn(',' + sepChar + 'object')
                       else
                         AsmWriteLn(',' + sepChar + 'function');
                     end;
                 end;
               if replaceforbidden then
                 if not(tai_symbol(hp).has_value) then
                   AsmWriteLn(ReplaceForbiddenAsmSymbolChars(tai_symbol(hp).sym.name + ':'))
                 else
                   AsmWriteLn(ReplaceForbiddenAsmSymbolChars(tai_symbol(hp).sym.name + '=' + tostr(tai_symbol(hp).value)))
               else if not(tai_symbol(hp).has_value) then
                 AsmWriteLn(tai_symbol(hp).sym.name + ':')
               else
                 AsmWriteLn(tai_symbol(hp).sym.name + '=' + tostr(tai_symbol(hp).value));
             end;
{$ifdef arm}
           ait_thumb_func:
             begin
               AsmWriteLn(#9'.thumb_func');
             end;
{$endif arm}
{$if defined(alpha)}
           ait_ent:
             begin
               AsmWriteLn(#9'.ent'#9+tai_ent(hp).Name);
             end;
{$endif alpha}
           ait_symbol_end :
             begin
               if tf_needs_symbol_size in target_info.flags then
                begin
                  s:=target_asm.labelprefix+'e'+tostr(symendcount);
                  inc(symendcount);
                  AsmWriteLn(s+':');
                  AsmWrite(#9'.size'#9);
                  if (target_info.system = system_powerpc64_linux) and (tai_symbol_end(hp).sym.typ = AT_FUNCTION) then
                    AsmWrite('.');
                  if replaceforbidden then
                    AsmWrite(ReplaceForbiddenAsmSymbolChars(tai_symbol_end(hp).sym.name))
                  else
                    AsmWrite(tai_symbol_end(hp).sym.name);
                  AsmWrite(', '+s+' - ');
                  if (target_info.system = system_powerpc64_linux) and (tai_symbol_end(hp).sym.typ = AT_FUNCTION) then
                     AsmWrite('.');
                  if replaceforbidden then
                    AsmWriteLn(ReplaceForbiddenAsmSymbolChars(tai_symbol_end(hp).sym.name))
                  else
                    AsmWriteLn(tai_symbol_end(hp).sym.name);
                end;
             end;

           ait_instruction :
             begin
               WriteInstruction(hp);
             end;

           ait_stab :
             begin
               if assigned(tai_stab(hp).str) then
                 begin
                   AsmWrite(#9'.'+stabtypestr[tai_stab(hp).stabtype]+' ');
                   AsmWritePChar(tai_stab(hp).str);
                   AsmLn;
                 end;
             end;

           ait_force_line,
           ait_function_name :
             ;

           ait_cutobject :
             begin
               if SmartAsm then
                begin
                { only reset buffer if nothing has changed }
                  if AsmSize=AsmStartSize then
                   AsmClear
                  else
                   begin
                     AsmClose;
                     DoAssemble;
                     AsmCreate(tai_cutobject(hp).place);
                   end;
                { avoid empty files }
                  while assigned(hp.next) and (tai(hp.next).typ in [ait_cutobject,ait_section,ait_comment]) do
                   begin
                     if tai(hp.next).typ=ait_section then
                       LastSecType:=tai_section(hp.next).sectype;
                     hp:=tai(hp.next);
                   end;
                  if LastSecType<>sec_none then
                    WriteSection(LastSecType,'',secorder_default,last_align);
                  AsmStartSize:=AsmSize;
                end;
             end;

           ait_marker :
             if tai_marker(hp).kind=mark_NoLineInfoStart then
               inc(InlineLevel)
             else if tai_marker(hp).kind=mark_NoLineInfoEnd then
               dec(InlineLevel);

           ait_directive :
             begin
               WriteDirectiveName(tai_directive(hp).directive);
               if tai_directive(hp).name <>'' then
                 AsmWrite(tai_directive(hp).name);
               AsmLn;
             end;

           ait_seh_directive :
             begin
{$ifdef TEST_WIN64_SEH}
               AsmWrite(sehdirectivestr[tai_seh_directive(hp).kind]);
               case tai_seh_directive(hp).datatype of
                 sd_none:;
                 sd_string:
                   begin
                     AsmWrite(' '+tai_seh_directive(hp).data.name^);
                     if (tai_seh_directive(hp).data.flags and 1)<>0 then
                       AsmWrite(',@except');
                     if (tai_seh_directive(hp).data.flags and 2)<>0 then
                       AsmWrite(',@unwind');
                   end;
                 sd_reg:
                   AsmWrite(' '+gas_regname(tai_seh_directive(hp).data.reg));
                 sd_offset:
                   AsmWrite(' '+tostr(tai_seh_directive(hp).data.offset));
                 sd_regoffset:
                   AsmWrite(' '+gas_regname(tai_seh_directive(hp).data.reg)+', '+
                     tostr(tai_seh_directive(hp).data.offset));
               end;
               AsmLn;
{$endif TEST_WIN64_SEH}
             end;
           ait_varloc:
             begin
               if tai_varloc(hp).newlocationhi<>NR_NO then
                 AsmWrite(strpnew('Var '+tai_varloc(hp).varsym.realname+' located in register '+
                   std_regname(tai_varloc(hp).newlocationhi)+':'+std_regname(tai_varloc(hp).newlocation)))
               else
                 AsmWrite(strpnew('Var '+tai_varloc(hp).varsym.realname+' located in register '+
                   std_regname(tai_varloc(hp).newlocation)));
               AsmLn;
             end;
           else
             internalerror(2006012201);
         end;
         hp:=tai(hp.next);
       end;
    end;


    procedure TGNUAssembler.WriteExtraHeader;
      begin
      end;


    procedure TGNUAssembler.WriteExtraFooter;
      begin
      end;


    procedure TGNUAssembler.WriteInstruction(hp: tai);
      begin
        InstrWriter.WriteInstruction(hp);
      end;


    procedure TGNUAssembler.WriteWeakSymbolDef(s: tasmsymbol);
      begin
        AsmWriteLn(#9'.weak '+s.name);
      end;


    procedure TGNUAssembler.WriteAixStringConst(hp: tai_string);
      type
        tterminationkind = (term_none,term_string,term_nostring);

      var
        i: longint;
        pos: longint;
        s: string;
        ch: char;
        instring: boolean;

      procedure newstatement(terminationkind: tterminationkind);
        begin
          case terminationkind of
            term_none: ;
            term_string:
              AsmWriteLn('"');
            term_nostring:
              AsmLn;
          end;
          AsmWrite(#9'.byte'#9);
          pos:=20;
          instring:=false;
        end;

      begin
        pos:=0;
        for i:=1 to hp.len do
          begin
            if pos=0 then
              newstatement(term_none);
            ch:=hp.str[i-1];
            case ch of
              #0..#31,
              #127..#255 :
                begin
                  if instring then
                    newstatement(term_string);
                  if pos=20 then
                    s:=tostr(ord(ch))
                  else
                    s:=', '+tostr(ord(ch))
                end;
              '"' :
                if instring then
                  s:='""'
                else
                  begin
                    if pos<>20 then
                      newstatement(term_nostring);
                    s:='"""';
                    instring:=true;
                  end;
              else
                if not instring then
                  begin
                    if (pos<>20) then
                      newstatement(term_nostring);
                    s:='"'+ch;
                    instring:=true;
                  end
                else
                  s:=ch;
            end;
            AsmWrite(s);
            inc(pos,length(s));
            if (pos>line_length) or (i=tai_string(hp).len) then
              begin
                if instring then
                  AsmWriteLn('"')
                else
                  AsmLn;
                pos:=0;
              end;
         end;
      end;


    procedure TGNUAssembler.WriteAixIntConst(hp: tai_const);
      var
        pos, size: longint;
      begin
        { only big endian AIX supported for now }
        if target_info.endian<>endian_big then
          internalerror(2012010401);
        { limitation: can only write 4 bytes at a time }
        pos:=0;
        size:=tai_const(hp).size;
        while pos<(size-4) do
          begin
            AsmWrite(#9'.vbyte'#9'4, ');
            AsmWriteln(tostr(longint(tai_const(hp).value shr ((size-pos-4)*8))));
            inc(pos,4);
         end;
        AsmWrite(#9'.vbyte'#9);
        AsmWrite(tostr(size-pos));
        AsmWrite(', ');
        case size-pos of
          1: AsmWrite(tostr(byte(tai_const(hp).value)));
          2: AsmWrite(tostr(word(tai_const(hp).value)));
          4: AsmWrite(tostr(longint(tai_const(hp).value)));
          else
            internalerror(2012010402);
        end;
      end;


    procedure TGNUAssembler.WriteDirectiveName(dir: TAsmDirective);
    begin
      AsmWrite('.'+directivestr[dir]+' ');
    end;


    procedure TGNUAssembler.WriteAsmList;
    var
      n : string;
      hal : tasmlisttype;
      i: longint;
    begin
{$ifdef EXTDEBUG}
      if assigned(current_module.mainsource) then
       Comment(V_Debug,'Start writing gas-styled assembler output for '+current_module.mainsource);
{$endif}

      if current_module.mainsource<>'' then
        n:=ExtractFileName(current_module.mainsource)
      else
        n:=InputFileName;

      { gcc does not add it either for Darwin. Grep for
        TARGET_ASM_FILE_START_FILE_DIRECTIVE in gcc/config/*.h
      }
      if not(target_info.system in systems_darwin) then
        AsmWriteLn(#9'.file "'+FixFileName(n)+'"');

      WriteExtraHeader;
      AsmStartSize:=AsmSize;
      symendcount:=0;

      for hal:=low(TasmlistType) to high(TasmlistType) do
        begin
          AsmWriteLn(target_asm.comment+'Begin asmlist '+AsmlistTypeStr[hal]);
          writetree(current_asmdata.asmlists[hal]);
          AsmWriteLn(target_asm.comment+'End asmlist '+AsmlistTypeStr[hal]);
        end;

      { add weak symbol markers }
      for i:=0 to current_asmdata.asmsymboldict.count-1 do
        if (tasmsymbol(current_asmdata.asmsymboldict[i]).bind=AB_WEAK_EXTERNAL) then
          writeweaksymboldef(tasmsymbol(current_asmdata.asmsymboldict[i]));

      if create_smartlink_sections and
         (target_info.system in systems_darwin) then
        AsmWriteLn(#9'.subsections_via_symbols');

      { "no executable stack" marker for Linux }
      if (target_info.system in systems_linux) and
         not(cs_executable_stack in current_settings.moduleswitches) then
        begin
          AsmWriteLn('.section .note.GNU-stack,"",%progbits');
        end;

      AsmLn;
{$ifdef EXTDEBUG}
      if assigned(current_module.mainsource) then
       Comment(V_Debug,'Done writing gas-styled assembler output for '+current_module.mainsource);
{$endif EXTDEBUG}
    end;


{****************************************************************************}
{                        Apple/GNU Assembler writer                          }
{****************************************************************************}

    function TAppleGNUAssembler.sectionname(atype:TAsmSectiontype;const aname:string;aorder:TAsmSectionOrder):string;
      begin
        if (target_info.system in systems_darwin) then
          case atype of
            sec_bss:
              { all bss (lcomm) symbols are automatically put in the right }
              { place by using the lcomm assembler directive               }
              atype := sec_none;
            sec_debug_frame,
            sec_eh_frame:
              begin
                result := '.section __DWARF,__debug_info,regular,debug';
                exit;
              end;
            sec_debug_line:
              begin
                result := '.section __DWARF,__debug_line,regular,debug';
                exit;
              end;
            sec_debug_info:
              begin
                result := '.section __DWARF,__debug_info,regular,debug';
                exit;
              end;
            sec_debug_abbrev:
               begin
                 result := '.section __DWARF,__debug_abbrev,regular,debug';
                 exit;
               end;
            sec_rodata:
              begin
                result := '.const_data';
                exit;
              end;
            sec_rodata_norel:
              begin
                result := '.const';
                exit;
              end;
            sec_fpc:
              begin
                result := '.section __TEXT, .fpc, regular, no_dead_strip';
                exit;
              end;
            sec_code:
              begin
                if (aname='fpc_geteipasebx') or
                   (aname='fpc_geteipasecx') then
                  begin
                    result:='.section __TEXT,__textcoal_nt,coalesced,pure_instructions'#10'.weak_definition '+aname+
                      #10'.private_extern '+aname;
                    exit;
                  end;
              end;
            sec_data_nonlazy:
              begin
                result:='.section __DATA, __nl_symbol_ptr,non_lazy_symbol_pointers';
                exit;
              end;
            sec_data_lazy:
              begin
                result:='.section __DATA, __la_symbol_ptr,lazy_symbol_pointers';
                exit;
              end;
            sec_init_func:
              begin
                result:='.section __DATA, __mod_init_func, mod_init_funcs';
                exit;
              end;
            sec_term_func:
              begin
                result:='.section __DATA, __mod_term_func, mod_term_funcs';
                exit;
              end;
            sec_objc_protocol_ext:
              begin
                result:='.section __OBJC, __protocol_ext, regular, no_dead_strip';
                exit;
              end;
            sec_objc_class_ext:
              begin
                result:='.section __OBJC, __class_ext, regular, no_dead_strip';
                exit;
              end;
            sec_objc_property:
              begin
                result:='.section __OBJC, __property, regular, no_dead_strip';
                exit;
              end;
            sec_objc_image_info:
              begin
                result:='.section __OBJC, __image_info, regular, no_dead_strip';
                exit;
              end;
            sec_objc_cstring_object:
              begin
                result:='.section __OBJC, __cstring_object, regular, no_dead_strip';
                exit;
              end;
            sec_objc_sel_fixup:
              begin
                result:='.section __OBJC, __sel_fixup, regular, no_dead_strip';
                exit;
              end;
            sec_objc_message_refs:
              begin
                if (target_info.system in systems_objc_nfabi) then
                  begin
                    result:='.section __DATA, __objc_selrefs, literal_pointers, no_dead_strip';
                    exit;
                  end;
              end;
            sec_objc_cls_refs:
              begin
                if (target_info.system in systems_objc_nfabi) then
                  begin
                    result:='.section __DATA, __objc_clsrefs, regular, no_dead_strip';
                    exit;
                  end;
              end;
            sec_objc_meth_var_names,
            sec_objc_class_names:
              begin
                if (target_info.system in systems_objc_nfabi) then
                  begin
                    result:='.cstring';
                    exit
                  end;
              end;
            sec_objc_inst_meth,
            sec_objc_cls_meth,
            sec_objc_cat_inst_meth,
            sec_objc_cat_cls_meth:
              begin
                if (target_info.system in systems_objc_nfabi) then
                  begin
                    result:='.section __DATA, __objc_const';
                    exit;
                  end;
              end;
            sec_objc_meta_class,
            sec_objc_class:
              begin
                if (target_info.system in systems_objc_nfabi) then
                  begin
                    result:='.section __DATA, __objc_data';
                    exit;
                  end;
              end;
            sec_objc_sup_refs:
              begin
                result:='.section __DATA, __objc_superrefs, regular, no_dead_strip';
                exit
              end;
            sec_objc_classlist:
              begin
                result:='.section __DATA, __objc_classlist, regular, no_dead_strip';
                exit
              end;
            sec_objc_nlclasslist:
              begin
                result:='.section __DATA, __objc_nlclasslist, regular, no_dead_strip';
                exit
              end;
            sec_objc_catlist:
              begin
                result:='.section __DATA, __objc_catlist, regular, no_dead_strip';
                exit
              end;
            sec_objc_nlcatlist:
              begin
                result:='.section __DATA, __objc_nlcatlist, regular, no_dead_strip';
                exit
              end;
            sec_objc_protolist:
              begin
                result:='.section __DATA, __objc_protolist, coalesced, no_dead_strip';
                exit;
              end;
          end;
        result := inherited sectionname(atype,aname,aorder);
      end;


    procedure TAppleGNUAssembler.WriteWeakSymbolDef(s: tasmsymbol);
      begin
        AsmWriteLn(#9'.weak_reference '+s.name);
      end;


{****************************************************************************}
{                       a.out/GNU Assembler writer                           }
{****************************************************************************}

    function TAoutGNUAssembler.sectionname(atype:TAsmSectiontype;const aname:string;aorder:TAsmSectionOrder):string;
    const
(* Translation table - replace unsupported section types with basic ones. *)
        SecXTable: array[TAsmSectionType] of TAsmSectionType = (
         sec_none,
         sec_none,
         sec_code,
         sec_data,
         sec_data (* sec_rodata *),
         sec_data (* sec_rodata_norel *),
         sec_bss,
         sec_data (* sec_threadvar *),
         { used for wince exception handling }
         sec_code (* sec_pdata *),
         { used for darwin import stubs }
         sec_code (* sec_stub *),
         sec_data,(* sec_data_nonlazy *)
         sec_data,(* sec_data_lazy *)
         sec_data,(* sec_init_func *)
         sec_data,(* sec_term_func *)
         { stabs }
         sec_stab,sec_stabstr,
         { win32 }
         sec_data (* sec_idata2 *),
         sec_data (* sec_idata4 *),
         sec_data (* sec_idata5 *),
         sec_data (* sec_idata6 *),
         sec_data (* sec_idata7 *),
         sec_data (* sec_edata *),
         { C++ exception handling unwinding (uses dwarf) }
         sec_eh_frame,
         { dwarf }
         sec_debug_frame,
         sec_debug_info,
         sec_debug_line,
         sec_debug_abbrev,
         { ELF resources (+ references to stabs debug information sections) }
         sec_code (* sec_fpc *),
         { Table of contents section }
         sec_code (* sec_toc *),
         sec_code (* sec_init *),
         sec_code (* sec_fini *),
         sec_none (* sec_objc_class *),
         sec_none (* sec_objc_meta_class *),
         sec_none (* sec_objc_cat_cls_meth *),
         sec_none (* sec_objc_cat_inst_meth *),
         sec_none (* sec_objc_protocol *),
         sec_none (* sec_objc_string_object *),
         sec_none (* sec_objc_cls_meth *),
         sec_none (* sec_objc_inst_meth *),
         sec_none (* sec_objc_cls_refs *),
         sec_none (* sec_objc_message_refs *),
         sec_none (* sec_objc_symbols *),
         sec_none (* sec_objc_category *),
         sec_none (* sec_objc_class_vars *),
         sec_none (* sec_objc_instance_vars *),
         sec_none (* sec_objc_module_info *),
         sec_none (* sec_objc_class_names *),
         sec_none (* sec_objc_meth_var_types *),
         sec_none (* sec_objc_meth_var_names *),
         sec_none (* sec_objc_selector_strs *),
         sec_none (* sec_objc_protocol_ext *),
         sec_none (* sec_objc_class_ext *),
         sec_none (* sec_objc_property *),
         sec_none (* sec_objc_image_info *),
         sec_none (* sec_objc_cstring_object *),
         sec_none (* sec_objc_sel_fixup *),
         sec_none (* sec_objc_data *),
         sec_none (* sec_objc_const *),
         sec_none (* sec_objc_sup_refs *),
         sec_none (* sec_data_coalesced *),
         sec_none (* sec_objc_classlist *),
         sec_none (* sec_objc_nlclasslist *),
         sec_none (* sec_objc_catlist *),
         sec_none (* sec_objc_nlcatlist *),
         sec_none (* sec_objc_protlist *)
        );
      begin
        Result := inherited SectionName (SecXTable [AType], AName, AOrder);
      end;


{****************************************************************************}
{                        Abstract Instruction Writer                         }
{****************************************************************************}

     constructor TCPUInstrWriter.create(_owner: TGNUAssembler);
       begin
         inherited create;
         owner := _owner;
       end;

end.
