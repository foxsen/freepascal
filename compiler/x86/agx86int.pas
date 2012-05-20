{
    Copyright (c) 1998-2002 by Florian Klaempfl

    This unit implements an asmoutput class for Intel syntax with Intel i386+

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
{
  This unit implements an asmoutput class for Intel syntax with Intel i386+
}
unit agx86int;

{$i fpcdefs.inc}

interface

    uses
      cpubase,
      aasmbase,aasmtai,aasmdata,aasmcpu,assemble,cgutils;

    type
      Tx86IntelAssembler = class(TExternalAssembler)
      private
        procedure WriteReference(var ref : treference);
        procedure WriteOper(const o:toper;s : topsize; opcode: tasmop;dest : boolean);
        procedure WriteOper_jmp(const o:toper;s : topsize);
      public
        procedure WriteTree(p:TAsmList);override;
        procedure WriteAsmList;override;
        Function  DoAssemble:boolean;override;
        procedure WriteExternals;
      end;


implementation

    uses
      SysUtils,
      cutils,globtype,globals,systems,cclasses,
      verbose,finput,fmodule,script,cpuinfo,
      itx86int,
      cgbase
      ;

    const
      line_length = 70;

      secnames : array[TAsmSectiontype] of string[4] = ('','',
        'CODE','DATA','DATA','DATA','BSS','TLS',
        '','','','','','',
        '','','','',
        '',
        '',
        '',
        '',
        '',
        '','','','',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        ''
      );

      secnamesml64 : array[TAsmSectiontype] of string[7] = ('','',
        '_TEXT','_DATA','_DATA','_DATA','_BSS','_TLS',
        '','','','',
        'idata$2','idata$4','idata$5','idata$6','idata$7','edata',
        '',
        '',
        '',
        '',
        '',
        '','','','',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        '',
        ''
      );

    function single2str(d : single) : string;
      var
         hs : string;
         p : byte;
      begin
         str(d,hs);
      { nasm expects a lowercase e }
         p:=pos('E',hs);
         if p>0 then
          hs[p]:='e';
         p:=pos('+',hs);
         if p>0 then
          delete(hs,p,1);
         single2str:=lower(hs);
      end;

    function double2str(d : double) : string;
      var
         hs : string;
         p : byte;
      begin
         str(d,hs);
      { nasm expects a lowercase e }
         p:=pos('E',hs);
         if p>0 then
          hs[p]:='e';
         p:=pos('+',hs);
         if p>0 then
          delete(hs,p,1);
         double2str:=lower(hs);
      end;

    function extended2str(e : extended) : string;
      var
         hs : string;
         p : byte;
      begin
         str(e,hs);
      { nasm expects a lowercase e }
         p:=pos('E',hs);
         if p>0 then
          hs[p]:='e';
         p:=pos('+',hs);
         if p>0 then
          delete(hs,p,1);
         extended2str:=lower(hs);
      end;


    function comp2str(d : bestreal) : string;
      type
        pdouble = ^double;
      var
        c  : comp;
        dd : pdouble;
      begin
         c:=comp(d);
         dd:=pdouble(@c); { this makes a bitwise copy of c into a double }
         comp2str:=double2str(dd^);
      end;

    { MASM supports aligns up to 8192 }
    function alignstr(b : integer) : string;
      begin
        case b of
          1: result:='BYTE';
          2: result:='WORD';
          4: result:='DWORD';
          16: result:='PARA';
          256: result:='PAGE';
        else
          result:='ALIGN('+tostr(b)+')';
        end;
      end;

{****************************************************************************
                               tx86IntelAssembler
 ****************************************************************************}

    procedure tx86IntelAssembler.WriteReference(var ref : treference);
      var
        first : boolean;
      begin
        with ref do
         begin
           first:=true;
           if segment<>NR_NO then
            AsmWrite(masm_regname(segment)+':[')
           else
            AsmWrite('[');
           if assigned(symbol) then
            begin
              if (target_asm.id = as_i386_tasm) then
                AsmWrite('dword ptr ');
              AsmWrite(symbol.name);
              first:=false;
            end;
           if (base<>NR_NO) then
            begin
              if not(first) then
               AsmWrite('+')
              else
               first:=false;
{$ifdef x86_64}
              { ml64 needs [$+foo] instead of [rip+foo] }
              if (base=NR_RIP) and (target_asm.id=as_x86_64_masm) then
               AsmWrite('$')
              else
{$endif x86_64}
               AsmWrite(masm_regname(base));
            end;
           if (index<>NR_NO) then
            begin
              if not(first) then
               AsmWrite('+')
              else
               first:=false;
              AsmWrite(masm_regname(index));
              if scalefactor<>0 then
               AsmWrite('*'+tostr(scalefactor));
            end;
               if offset<0 then
                begin
                  AsmWrite(tostr(offset));
                  first:=false;
                end
               else if (offset>0) then
                begin
                  AsmWrite('+'+tostr(offset));
                  first:=false;
                end;
           if first then
             AsmWrite('0');
           AsmWrite(']');
         end;
      end;


    procedure tx86IntelAssembler.WriteOper(const o:toper;s : topsize; opcode: tasmop;dest : boolean);
      begin
        case o.typ of
          top_reg :
            AsmWrite(masm_regname(o.reg));
          top_const :
            AsmWrite(tostr(o.val));
          top_ref :
            begin
              if o.ref^.refaddr in [addr_no,addr_pic,addr_pic_no_got] then
                begin
                  if ((opcode <> A_LGS) and (opcode <> A_LSS) and
                      (opcode <> A_LFS) and (opcode <> A_LDS) and
                      (opcode <> A_LES)) then
                   Begin
                     case s of
                      S_B : AsmWrite('byte ptr ');
                      S_W : AsmWrite('word ptr ');
                      S_L : AsmWrite('dword ptr ');
                      S_Q : AsmWrite('qword ptr ');
                     S_IS : AsmWrite('word ptr ');
                     S_IL : AsmWrite('dword ptr ');
                     S_IQ : AsmWrite('qword ptr ');
                     S_FS : AsmWrite('dword ptr ');
                     S_FL : AsmWrite('qword ptr ');
                     S_T,
                     S_FX : AsmWrite('tbyte ptr ');
                     S_BW : if dest then
                             AsmWrite('word ptr ')
                            else
                             AsmWrite('byte ptr ');
                     S_BL : if dest then
                             AsmWrite('dword ptr ')
                            else
                             AsmWrite('byte ptr ');
                     S_WL : if dest then
                             AsmWrite('dword ptr ')
                            else
                             AsmWrite('word ptr ');
{$ifdef x86_64}
                     S_BQ : if dest then
                             AsmWrite('qword ptr ')
                            else
                             AsmWrite('byte ptr ');
                     S_WQ : if dest then
                             AsmWrite('qword ptr ')
                            else
                             AsmWrite('word ptr ');
                     S_LQ : if dest then
                             AsmWrite('qword ptr ')
                            else
                             AsmWrite('dword ptr ');
                     S_XMM: AsmWrite('xmmword ptr ');

{$endif x86_64}
                     end;
                   end;
                  WriteReference(o.ref^);
                end
              else
                begin
                  AsmWrite('offset ');
                  if assigned(o.ref^.symbol) then
                    AsmWrite(o.ref^.symbol.name);
                  if o.ref^.offset>0 then
                   AsmWrite('+'+tostr(o.ref^.offset))
                  else
                   if o.ref^.offset<0 then
                    AsmWrite(tostr(o.ref^.offset))
                  else
                   if not(assigned(o.ref^.symbol)) then
                     AsmWrite('0');
                end;
            end;
          else
            internalerror(2005060510);
        end;
      end;


    procedure tx86IntelAssembler.WriteOper_jmp(const o:toper;s : topsize);
    begin
      case o.typ of
        top_reg :
          AsmWrite(masm_regname(o.reg));
        top_const :
          AsmWrite(tostr(o.val));
        top_ref :
          { what about lcall or ljmp ??? }
          begin
            if o.ref^.refaddr=addr_no then
              begin
                if (target_asm.id <> as_i386_tasm) then
                  begin
                    if s=S_FAR then
                      AsmWrite('far ptr ')
                    else
{$ifdef x86_64}
                      AsmWrite('qword ptr ');
{$else x86_64}
                      AsmWrite('dword ptr ');
{$endif x86_64}
                  end;
                WriteReference(o.ref^);
              end
            else
              begin
                AsmWrite(o.ref^.symbol.name);
                if o.ref^.offset>0 then
                 AsmWrite('+'+tostr(o.ref^.offset))
                else
                 if o.ref^.offset<0 then
                  AsmWrite(tostr(o.ref^.offset));
              end;
          end;
        else
          internalerror(2005060511);
      end;
    end;

    const
      ait_const2str : array[aitconst_128bit..aitconst_secrel32_symbol] of string[20]=(
        #9''#9,#9'DQ'#9,#9'DD'#9,#9'DW'#9,#9'DB'#9,
        #9'FIXMESLEB',#9'FIXEMEULEB',
        #9'DD RVA'#9,#9'DD SECREL32'#9
      );

    Function PadTabs(const p:string;addch:char):string;
    var
      s : string;
      i : longint;
    begin
      i:=length(p);
      if addch<>#0 then
       begin
         inc(i);
         s:=p+addch;
       end
      else
       s:=p;
      if i<8 then
       PadTabs:=s+#9#9
      else
       PadTabs:=s+#9;
    end;

    procedure tx86IntelAssembler.WriteTree(p:TAsmList);
    var
      s,
      prefix,
      suffix   : string;
      hp       : tai;
      counter,
      lines,
      InlineLevel : longint;
      i,j,l    : longint;
      consttype : taiconst_type;
      do_line,DoNotSplitLine,
      quoted   : boolean;
    begin
      if not assigned(p) then
       exit;
      { lineinfo is only needed for al_procedures (PFV) }
      do_line:=((cs_asm_source in current_settings.globalswitches) or
                (cs_lineinfo in current_settings.moduleswitches))
                 and (p=current_asmdata.asmlists[al_procedures]);
      InlineLevel:=0;
      DoNotSplitLine:=false;
      hp:=tai(p.first);
      while assigned(hp) do
       begin
         prefetch(pointer(hp.next)^);
         if not(hp.typ in SkipLineInfo) then
          begin
            current_filepos:=tailineinfo(hp).fileinfo;
            { no line info for inlined code }
            if do_line and (inlinelevel=0) and not DoNotSplitLine then
              WriteSourceLine(hp as tailineinfo);
          end;
         DoNotSplitLine:=false;

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
                 AsmWriteLn(target_asm.comment+'Register '+masm_regname(tai_regalloc(hp).reg)+
                   regallocstr[tai_regalloc(hp).ratype]);
             end;

           ait_tempalloc :
             begin
               if (cs_asm_tempalloc in current_settings.globalswitches) then
                 WriteTempalloc(tai_tempalloc(hp));
             end;

           ait_section :
             begin
               if tai_section(hp).sectype<>sec_none then
                begin
                  if target_asm.id=as_x86_64_masm then
                    begin
                      if LasTSecType<>sec_none then
                        AsmWriteLn(secnamesml64[LasTSecType]+#9#9'ENDS');
                      AsmLn;
                      AsmWriteLn(secnamesml64[tai_section(hp).sectype]+#9+'SEGMENT')
                    end
                  else
                    begin
                      if LasTSecType<>sec_none then
                        AsmWriteLn('_'+secnames[LasTSecType]+#9#9'ENDS');
                      AsmLn;
                      AsmWriteLn('_'+secnames[tai_section(hp).sectype]+#9#9+
                                 'SEGMENT'#9+alignstr(tai_section(hp).secalign)+' PUBLIC USE32 '''+
                                 secnames[tai_section(hp).sectype]+'''');
                    end;
                end;
               LasTSecType:=tai_section(hp).sectype;
             end;
           ait_align :
             begin
               { CAUSES PROBLEMS WITH THE SEGMENT DEFINITION   }
               { SEGMENT DEFINITION SHOULD MATCH TYPE OF ALIGN }
               { HERE UNDER TASM!                              }
                 if tai_align_abstract(hp).aligntype>1 then
                   AsmWriteLn(#9'ALIGN '+tostr(tai_align_abstract(hp).aligntype));
               end;
           ait_datablock :
             begin
               if tai_datablock(hp).is_global then
                 AsmWriteLn(#9'PUBLIC'#9+tai_datablock(hp).sym.name);
               AsmWriteLn(PadTabs(tai_datablock(hp).sym.name,#0)+'DB'#9+tostr(tai_datablock(hp).size)+' DUP(?)');
             end;
           ait_const:
             begin
               consttype:=tai_const(hp).consttype;
               case consttype of
                 aitconst_uleb128bit,
                 aitconst_sleb128bit,
                 aitconst_128bit,
                 aitconst_64bit,
                 aitconst_32bit,
                 aitconst_16bit,
                 aitconst_8bit,
                 aitconst_rva_symbol,
                 aitconst_secrel32_symbol :
                   begin
                     AsmWrite(ait_const2str[consttype]);
                     l:=0;
                     repeat
                       if assigned(tai_const(hp).sym) then
                         begin
                           if assigned(tai_const(hp).endsym) then
                             s:=tai_const(hp).endsym.name+'-'+tai_const(hp).sym.name
                           else
                             s:=tai_const(hp).sym.name;
                           if tai_const(hp).value<>0 then
                             s:=s+tostr_with_plus(tai_const(hp).value);
                         end
                       else
                         s:=tostr(tai_const(hp).value);
                       AsmWrite(s);
                       inc(l,length(s));
                       if (l>line_length) or
                          (hp.next=nil) or
                          (tai(hp.next).typ<>ait_const) or
                          (tai_const(hp.next).consttype<>consttype) then
                         break;
                       hp:=tai(hp.next);
                       AsmWrite(',');
                     until false;
                     AsmLn;
                   end;
                 else
                   internalerror(200704253);
               end;
             end;

           ait_real_32bit :
             AsmWriteLn(#9#9'DD'#9+single2str(tai_real_32bit(hp).value));
           ait_real_64bit :
             AsmWriteLn(#9#9'DQ'#9+double2str(tai_real_64bit(hp).value));
           ait_real_80bit :
             AsmWriteLn(#9#9'DT'#9+extended2str(tai_real_80bit(hp).value));
           ait_comp_64bit :
             AsmWriteLn(#9#9'DQ'#9+extended2str(tai_comp_64bit(hp).value));
           ait_string :
             begin
               counter := 0;
               lines := tai_string(hp).len div line_length;
             { separate lines in different parts }
               if tai_string(hp).len > 0 then
                Begin
                  for j := 0 to lines-1 do
                   begin
                     AsmWrite(#9#9'DB'#9);
                     quoted:=false;
                     for i:=counter to counter+line_length-1 do
                        begin
                          { it is an ascii character. }
                          if (ord(tai_string(hp).str[i])>31) and
                             (ord(tai_string(hp).str[i])<128) and
                             (tai_string(hp).str[i]<>'"') then
                              begin
                                if not(quoted) then
                                    begin
                                      if i>counter then
                                        AsmWrite(',');
                                      AsmWrite('"');
                                    end;
                                AsmWrite(tai_string(hp).str[i]);
                                quoted:=true;
                              end { if > 31 and < 128 and ord('"') }
                          else
                              begin
                                  if quoted then
                                      AsmWrite('"');
                                  if i>counter then
                                      AsmWrite(',');
                                  quoted:=false;
                                  AsmWrite(tostr(ord(tai_string(hp).str[i])));
                              end;
                       end; { end for i:=0 to... }
                     if quoted then AsmWrite('"');
                       AsmWrite(target_info.newline);
                     counter := counter+line_length;
                  end; { end for j:=0 ... }
                { do last line of lines }
                if counter<tai_string(hp).len then
                  AsmWrite(#9#9'DB'#9);
                quoted:=false;
                for i:=counter to tai_string(hp).len-1 do
                  begin
                    { it is an ascii character. }
                    if (ord(tai_string(hp).str[i])>31) and
                       (ord(tai_string(hp).str[i])<128) and
                       (tai_string(hp).str[i]<>'"') then
                        begin
                          if not(quoted) then
                              begin
                                if i>counter then
                                  AsmWrite(',');
                                AsmWrite('"');
                              end;
                          AsmWrite(tai_string(hp).str[i]);
                          quoted:=true;
                        end { if > 31 and < 128 and " }
                    else
                        begin
                          if quoted then
                            AsmWrite('"');
                          if i>counter then
                              AsmWrite(',');
                          quoted:=false;
                          AsmWrite(tostr(ord(tai_string(hp).str[i])));
                        end;
                  end; { end for i:=0 to... }
                if quoted then
                  AsmWrite('"');
                end;
               AsmLn;
             end;
           ait_label :
             begin
               if tai_label(hp).labsym.is_used then
                begin
                  AsmWrite(tai_label(hp).labsym.name);
                  if assigned(hp.next) and not(tai(hp.next).typ in
                     [ait_const,
                      ait_real_32bit,ait_real_64bit,ait_real_80bit,ait_comp_64bit,ait_string]) then
                   AsmWriteLn(':')
                  else
                   DoNotSplitLine:=true;
                end;
             end;
           ait_symbol :
             begin
               if tai_symbol(hp).has_value then
                 internalerror(2009090802);
               if tai_symbol(hp).is_global then
                 AsmWriteLn(#9'PUBLIC'#9+tai_symbol(hp).sym.name);
               AsmWrite(tai_symbol(hp).sym.name);
               if assigned(hp.next) and not(tai(hp.next).typ in
                  [ait_const,
                   ait_real_32bit,ait_real_64bit,ait_real_80bit,ait_comp_64bit,ait_string]) then
                AsmWriteLn(':')
             end;
           ait_symbol_end :
             begin
             end;
           ait_instruction :
             begin
               taicpu(hp).CheckNonCommutativeOpcodes;
               taicpu(hp).SetOperandOrder(op_intel);
               { Reset }
               suffix:='';
               prefix:= '';
               { We need to explicitely set
                 word prefix to get selectors
                 to be pushed in 2 bytes  PM }
               if (taicpu(hp).opsize=S_W) and
                   (
                    (
                     (taicpu(hp).opcode=A_PUSH) or
                     (taicpu(hp).opcode=A_POP)
                    ) and
                    (taicpu(hp).oper[0]^.typ=top_reg) and
                    is_segment_reg(taicpu(hp).oper[0]^.reg)
                   ) then
                 AsmWriteln(#9#9'DB'#9'066h');

               { added prefix instructions, must be on same line as opcode }
               if (taicpu(hp).ops = 0) and
                  ((taicpu(hp).opcode = A_REP) or
                   (taicpu(hp).opcode = A_LOCK) or
                   (taicpu(hp).opcode =  A_REPE) or
                   (taicpu(hp).opcode =  A_REPNZ) or
                   (taicpu(hp).opcode =  A_REPZ) or
                   (taicpu(hp).opcode = A_REPNE)) then
                Begin
                  prefix:=std_op2str[taicpu(hp).opcode]+#9;
                  { there can be a stab inbetween when the opcode was on
                    a different line in the source code }
                  repeat
                    hp:=tai(hp.next);
                  until (hp=nil) or (hp.typ=ait_instruction);
                  { this is theorically impossible... }
                  if hp=nil then
                   begin
                     AsmWriteLn(#9#9+prefix);
                     break;
                   end;
                  { nasm prefers prefix on a line alone
                  AsmWriteln(#9#9+prefix); but not masm PM
                  prefix:=''; }
                  if target_asm.id in [as_i386_nasmcoff,as_i386_nasmwin32,as_i386_nasmwdosx,
                    as_i386_nasmelf,as_i386_nasmobj,as_i386_nasmbeos,as_i386_nasmhaiku] then
                     begin
                       AsmWriteln(prefix);
                       prefix:='';
                     end;
                end
               else
                prefix:= '';
               if (target_asm.id = as_i386_wasm) and
                 (taicpu(hp).opsize=S_W) and
                 (taicpu(hp).opcode=A_PUSH) and
                 (taicpu(hp).oper[0]^.typ=top_const) then
                 begin
                   AsmWriteln(#9#9'DB 66h,68h ; pushw imm16');
                   AsmWrite(#9#9'DW');
                 end
               else if (target_asm.id=as_x86_64_masm) and
                 (taicpu(hp).opcode=A_MOVQ) then
                 AsmWrite(#9#9'mov')
               else
                 AsmWrite(#9#9+prefix+std_op2str[taicpu(hp).opcode]+cond2str[taicpu(hp).condition]+suffix);
               if taicpu(hp).ops<>0 then
                begin
                  if is_calljmp(taicpu(hp).opcode) then
                   begin
                     AsmWrite(#9);
                     WriteOper_jmp(taicpu(hp).oper[0]^,taicpu(hp).opsize);
                   end
                  else
                   begin
                     for i:=0to taicpu(hp).ops-1 do
                      begin
                        if i=0 then
                         AsmWrite(#9)
                        else
                         AsmWrite(',');
                        WriteOper(taicpu(hp).oper[i]^,taicpu(hp).opsize,taicpu(hp).opcode,(i=2));
                      end;
                   end;
                end;
               AsmLn;
             end;

           ait_stab,
           ait_force_line,
           ait_function_name : ;

           ait_cutobject :
             begin
               { only reset buffer if nothing has changed }
                 if AsmSize=AsmStartSize then
                  AsmClear
                 else
                  begin
                    if LasTSecType<>sec_none then
                     AsmWriteLn('_'+secnames[LasTSecType]+#9#9'ENDS');
                    AsmLn;
                    AsmWriteLn(#9'END');
                    AsmClose;
                    DoAssemble;
                    AsmCreate(tai_cutobject(hp).place);
                  end;
               { avoid empty files }
                 while assigned(hp.next) and (tai(hp.next).typ in [ait_cutobject,ait_section,ait_comment]) do
                  begin
                    if tai(hp.next).typ=ait_section then
                      lasTSecType:=tai_section(hp.next).sectype;
                    hp:=tai(hp.next);
                  end;
                 AsmWriteLn(#9'.386p');
                 AsmWriteLn('DGROUP'#9'GROUP'#9'_BSS,_DATA');
                 AsmWriteLn(#9'ASSUME'#9'CS:_CODE,ES:DGROUP,DS:DGROUP,SS:DGROUP');
                 { I was told that this isn't necesarry because }
                 { the labels generated by FPC are unique (FK)  }
                 { AsmWriteLn(#9'LOCALS '+target_asm.labelprefix); }
                 { TODO: PARA is incorrect, must use actual section align }
                 if lasTSectype<>sec_none then
                    AsmWriteLn('_'+secnames[lasTSectype]+#9#9+
                               'SEGMENT'#9'PARA PUBLIC USE32 '''+
                               secnames[lasTSectype]+'''');
                 AsmStartSize:=AsmSize;
               end;
           ait_marker :
             begin
               if tai_marker(hp).kind=mark_NoLineInfoStart then
                 inc(InlineLevel)
               else if tai_marker(hp).kind=mark_NoLineInfoEnd then
                 dec(InlineLevel);
             end;

           ait_directive :
             begin
               case tai_directive(hp).directive of
                 asd_nasm_import :
                   AsmWrite('import ');
                 asd_extern :
                   AsmWrite('EXTRN ');
                 else
                   internalerror(200509192);
               end;
               AsmWrite(tai_directive(hp).name);
               AsmLn;
             end;
           ait_seh_directive :
             { Ignore for now };
           else
            internalerror(10000);
         end;
         hp:=tai(hp.next);
       end;
    end;


    procedure tx86intelassembler.WriteExternals;
      var
        sym : TAsmSymbol;
        i   : longint;
      begin
        for i:=0 to current_asmdata.AsmSymbolDict.Count-1 do
          begin
            sym:=TAsmSymbol(current_asmdata.AsmSymbolDict[i]);
            if sym.bind=AB_EXTERNAL then
              begin
                case target_asm.id of
                  as_i386_masm,
                  as_i386_wasm :
                    AsmWriteln(#9'EXTRN'#9+sym.name+': NEAR');
                  as_x86_64_masm :
                    AsmWriteln(#9'EXTRN'#9+sym.name+': PROC');
                  else
                    AsmWriteln(#9'EXTRN'#9+sym.name);
                end;
              end;
          end;
      end;


    function tx86intelassembler.DoAssemble : boolean;
    var
      masmobjfn : string;
    begin
      DoAssemble:=Inherited DoAssemble;
      { masm does not seem to recognize specific extensions and uses .obj allways PM }
      if (target_asm.id in [as_i386_masm,as_i386_wasm]) then
        begin
          masmobjfn:=ChangeFileExt(objfilename,'.obj');
          if not(cs_asm_extern in current_settings.globalswitches) then
            begin
              if Not FileExists(objfilename) and
                 FileExists(masmobjfn) then
                RenameFile(masmobjfn,objfilename);
            end
          else
            AsmRes.AddAsmCommand('mv',masmobjfn+' '+objfilename,objfilename);
        end;
    end;


    procedure tx86IntelAssembler.WriteAsmList;
    var
      hal : tasmlisttype;
    begin
{$ifdef EXTDEBUG}
      if assigned(current_module.mainsource) then
       comment(v_info,'Start writing intel-styled assembler output for '+current_module.mainsource);
{$endif}
      if target_asm.id<>as_x86_64_masm then
        begin
          AsmWriteLn(#9'.386p');
          { masm 6.11 does not seem to like LOCALS PM }
          if (target_asm.id = as_i386_tasm) then
            begin
              AsmWriteLn(#9'LOCALS '+target_asm.labelprefix);
            end;
          AsmWriteLn('DGROUP'#9'GROUP'#9'_BSS,_DATA');
          AsmWriteLn(#9'ASSUME'#9'CS:_CODE,ES:DGROUP,DS:DGROUP,SS:DGROUP');
          AsmLn;
        end;

      WriteExternals;

      for hal:=low(TasmlistType) to high(TasmlistType) do
        begin
          AsmWriteLn(target_asm.comment+'Begin asmlist '+AsmListTypeStr[hal]);
          writetree(current_asmdata.asmlists[hal]);
          AsmWriteLn(target_asm.comment+'End asmlist '+AsmListTypeStr[hal]);
        end;

      { better do this at end of WriteTree, but then there comes a trouble with
        al_const which does not have leading ait_section and thus goes out of segment }

      if LastSecType <> sec_none then
        begin
          if target_asm.id=as_x86_64_masm then
            AsmWriteLn(secnamesml64[LasTSecType]+#9#9'ENDS')
          else
            AsmWriteLn('_'+secnames[LasTSecType]+#9#9'ENDS');
        end;
      LastSecType := sec_none;

      AsmWriteLn(#9'END');
      AsmLn;

{$ifdef EXTDEBUG}
      if assigned(current_module.mainsource) then
       comment(v_info,'Done writing intel-styled assembler output for '+current_module.mainsource);
{$endif EXTDEBUG}
   end;


{*****************************************************************************
                                  Initialize
*****************************************************************************}

    const
{$ifdef i386}
       as_i386_tasm_info : tasminfo =
          (
            id           : as_i386_tasm;
            idtxt  : 'TASM';
            asmbin : 'tasm';
            asmcmd : '/m2 /ml $ASM $OBJ';
            supported_targets : [system_i386_GO32V2,system_i386_Win32,system_i386_wdosx,system_i386_watcom,system_i386_wince];
            flags : [af_allowdirect,af_needar,af_labelprefix_only_inside_procedure];
            labelprefix : '@@';
            comment : '; ';
            dollarsign: '$';
          );

       as_i386_masm_info : tasminfo =
          (
            id           : as_i386_masm;
            idtxt  : 'MASM';
            asmbin : 'masm';
            asmcmd : '/c /Cp $ASM /Fo$OBJ';
            supported_targets : [system_i386_GO32V2,system_i386_Win32,system_i386_wdosx,system_i386_watcom,system_i386_wince];
            flags : [af_allowdirect,af_needar];
            labelprefix : '@@';
            comment : '; ';
            dollarsign: '$';
          );

       as_i386_wasm_info : tasminfo =
          (
            id     : as_i386_wasm;
            idtxt  : 'WASM';
            asmbin : 'wasm';
            asmcmd : '$ASM -6s -fp6 -ms -zq -Fo=$OBJ';
            supported_targets : [system_i386_watcom];
            flags : [af_allowdirect,af_needar];
            labelprefix : '@@';
            comment : '; ';
            dollarsign: '$';
          );
{$endif i386}
{$ifdef x86_64}
       as_x86_64_masm_info : tasminfo =
          (
            id     : as_x86_64_masm;
            idtxt  : 'MASM';
            asmbin : 'ml64';
            asmcmd : '/c /Cp $ASM /Fo$OBJ';
            supported_targets : [system_x86_64_win64];
            flags : [af_allowdirect,af_needar];
            labelprefix : '@@';
            comment : '; ';
            dollarsign: '$';
          );
{$endif x86_64}

initialization
{$ifdef x86_64}
  RegisterAssembler(as_x86_64_masm_info,tx86IntelAssembler);
{$endif x86_64}
{$ifdef i386}
  RegisterAssembler(as_i386_tasm_info,tx86IntelAssembler);
  RegisterAssembler(as_i386_masm_info,tx86IntelAssembler);
  RegisterAssembler(as_i386_wasm_info,tx86IntelAssembler);
{$endif i386}
end.
