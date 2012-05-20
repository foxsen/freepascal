{
    Copyright (c) 1998-2002 by Florian Klaempfl

    Generate assembler for nodes that handle loads and assignments which
    are the same for all (most) processors

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
unit ncgld;

{$i fpcdefs.inc}

interface

    uses
      globtype,
      symtype,
      aasmdata,
      node,nld,cgutils;

    type
       tcgloadnode = class(tloadnode)
         protected
          procedure generate_nested_access(vs: tsym);virtual;
         public
          procedure pass_generate_code;override;
          procedure generate_picvaraccess;virtual;
          procedure changereflocation(const ref: treference);
       end;

       tcgassignmentnode = class(tassignmentnode)
        protected
          function maybechangetemp(list: TAsmList; var n: tnode; const newref: treference): boolean;virtual;
        public
          procedure pass_generate_code;override;
       end;

       tcgarrayconstructornode = class(tarrayconstructornode)
         protected
          procedure makearrayref(var ref: treference; eledef: tdef);virtual;
          procedure advancearrayoffset(var ref: treference; elesize: asizeint);virtual;
         public
          procedure pass_generate_code;override;
       end;

       tcgrttinode = class(trttinode)
          procedure pass_generate_code;override;
       end;


implementation

    uses
      cutils,
      systems,
      verbose,globals,constexp,
      nutils,
      symtable,symconst,symdef,symsym,defutil,paramgr,
      ncnv,ncon,nmem,nbas,ncgrtti,
      aasmbase,aasmtai,aasmcpu,
      cgbase,pass_2,
      procinfo,
      cpubase,parabase,
      tgobj,ncgutil,
      cgobj,hlcgobj,
      ncgbas,ncgflw,
      wpobase;

{*****************************************************************************
                   SSA (for memory temps) support
*****************************************************************************}

    type
      preplacerefrec = ^treplacerefrec;
      treplacerefrec = record
        old, new: preference;
        ressym: tsym;
      end;

    function doreplaceref(var n: tnode; para: pointer): foreachnoderesult;
      var
        rr: preplacerefrec absolute para;
      begin
        result := fen_false;
        case n.nodetype of
          loadn:
            begin
                 { regular variable }
              if (tabstractvarsym(tloadnode(n).symtableentry).varoptions * [vo_is_dll_var, vo_is_thread_var] = []) and
                 not assigned(tloadnode(n).left) and
                 { not function result, or no exit in function }
                 (((tloadnode(n).symtableentry <> rr^.ressym) and
                   not(vo_is_funcret in tabstractvarsym(tloadnode(n).symtableentry).varoptions)) or
                  not(fc_exit in flowcontrol)) and
                 { stored in memory... }
                 (tabstractnormalvarsym(tloadnode(n).symtableentry).localloc.loc in [LOC_REFERENCE]) and
                 { ... at the place we are looking for }
                 references_equal(tabstractnormalvarsym(tloadnode(n).symtableentry).localloc.reference,rr^.old^) and
                 { its address cannot have escaped the current routine }
                 not(tabstractvarsym(tloadnode(n).symtableentry).addr_taken) then
                begin
                  { relocate variable }
                  tcgloadnode(n).changereflocation(rr^.new^);
                  result := fen_norecurse_true;
                end;
            end;
          temprefn:
            begin
              if (ti_valid in ttemprefnode(n).tempinfo^.flags) and
                 { memory temp... }
                 (ttemprefnode(n).tempinfo^.location.loc in [LOC_REFERENCE]) and
                 { ... at the place we are looking for }
                 references_equal(ttemprefnode(n).tempinfo^.location.reference,rr^.old^) and
                 { its address cannot have escaped the current routine }
                 not(ti_addr_taken in ttemprefnode(n).tempinfo^.flags) then
                begin
                  { relocate the temp }
                  tcgtemprefnode(n).changelocation(rr^.new^);
                  result := fen_norecurse_true;
                end;
            end;
          { Subscriptn must be rejected, otherwise we may replace an
            an entire record with a temp for its first field, mantis #13948)
            Exception: the field's size is the same as the entire record

            The same goes for array indexing
          }
          subscriptn,
          vecn:
            if not(tunarynode(n).left.resultdef.typ in [recorddef,objectdef,arraydef,stringdef]) or
               { make sure we don't try to call resultdef.size for types that
                 don't have a compile-time size such as open arrays }
               is_special_array(tunarynode(n).left.resultdef) or
               (tunarynode(n).left.resultdef.size<>tunarynode(n).resultdef.size) then
              result := fen_norecurse_false;

          { optimize the searching a bit }
          derefn,addrn,
          calln,inlinen,casen,
          addn,subn,muln,
          andn,orn,xorn,
          ltn,lten,gtn,gten,equaln,unequaln,
          slashn,divn,shrn,shln,notn,
          inn,
          asn,isn:
            result := fen_norecurse_false;
        end;
      end;


    function tcgassignmentnode.maybechangetemp(list: TAsmList; var n: tnode; const newref: treference): boolean;
      var
        rr: treplacerefrec;
      begin
        result := false;

        { only do for -O2 or higher (breaks debugging since }
        { variables move to different memory locations)     }
        if not(cs_opt_level2 in current_settings.optimizerswitches) or
           { must be a copy to a memory location ... }
           (n.location.loc <> LOC_REFERENCE) or
           { not inside a control flow statement and no goto's in sight }
           ([fc_inflowcontrol,fc_gotolabel] * flowcontrol <> []) or
           { not for refcounted types, because those locations are   }
           { still used later on in initialisation/finalisation code }
           is_managed_type(n.resultdef) or
           { source and destination are temps (= not global variables) }
           not tg.istemp(n.location.reference) or
           not tg.istemp(newref) or
           { and both point to the start of a temp, and the source is a }
           { non-persistent temp (otherwise we need some kind of copy-  }
           { on-write support in case later on both are still used)     }
           (tg.gettypeoftemp(newref) <> tt_normal) or
           not (tg.gettypeoftemp(n.location.reference) in [tt_normal,tt_persistent]) or
           { and both have the same size }
           (tg.sizeoftemp(current_asmdata.CurrAsmList,newref) <> tg.sizeoftemp(current_asmdata.CurrAsmList,n.location.reference)) then
          exit;

        { find the source of the old reference (loadnode or tempnode) }
        { and replace it with the new reference                       }
        rr.old := @n.location.reference;
        rr.new := @newref;
        rr.ressym := nil;

        if assigned(current_procinfo.procdef.funcretsym) and
           (tabstractvarsym(current_procinfo.procdef.funcretsym).refs <> 0) then
          if (current_procinfo.procdef.proctypeoption=potype_constructor) then
            rr.ressym:=tsym(current_procinfo.procdef.parast.Find('self'))
         else
            rr.ressym:=current_procinfo.procdef.funcretsym;

        { if source not found, don't do anything }
        if not foreachnodestatic(n,@doreplaceref,@rr) then
          exit;

        n.location.reference := newref;
        result:=true;
      end;

{*****************************************************************************
                             SecondLoad
*****************************************************************************}

    procedure tcgloadnode.generate_picvaraccess;
      begin
{$ifndef sparc}
        location.reference.base:=current_procinfo.got;
        location.reference.symbol:=current_asmdata.RefAsmSymbol(tstaticvarsym(symtableentry).mangledname+'@GOT');
{$endif sparc}
      end;


    procedure tcgloadnode.changereflocation(const ref: treference);
      var
        oldtemptype: ttemptype;
      begin
        if (location.loc<>LOC_REFERENCE) then
          internalerror(2007020812);
        if not tg.istemp(location.reference) then
          internalerror(2007020813);
        oldtemptype:=tg.gettypeoftemp(location.reference);
        if (oldtemptype = tt_persistent) then
          tg.ChangeTempType(current_asmdata.CurrAsmList,location.reference,tt_normal);
        tg.ungettemp(current_asmdata.CurrAsmList,location.reference);
        location.reference:=ref;
        tg.ChangeTempType(current_asmdata.CurrAsmList,location.reference,oldtemptype);
        tabstractnormalvarsym(symtableentry).localloc:=location;
      end;


    procedure tcgloadnode.generate_nested_access(vs: tsym);
      var
        { paramter declared as tsym to reduce interface unit dependencies }
        lvs: tabstractnormalvarsym absolute vs;
      begin
        secondpass(left);
        if not(left.location.loc in [LOC_REGISTER,LOC_CREGISTER]) then
          internalerror(200309286);
        if lvs.localloc.loc<>LOC_REFERENCE then
          internalerror(200409241);
        reference_reset_base(location.reference,left.location.register,lvs.localloc.reference.offset,lvs.localloc.reference.alignment);
      end;


    procedure tcgloadnode.pass_generate_code;
      var
        hregister : tregister;
        vs   : tabstractnormalvarsym;
        gvs  : tstaticvarsym;
        pd   : tprocdef;
        href : treference;
        newsize : tcgsize;
        endrelocatelab,
        norelocatelab : tasmlabel;
        paraloc1 : tcgpara;
      begin
        { we don't know the size of all arrays }
        newsize:=def_cgsize(resultdef);
        { alignment is overridden per case below }
        location_reset_ref(location,LOC_REFERENCE,newsize,resultdef.alignment);
        case symtableentry.typ of
           absolutevarsym :
              begin
                 { this is only for toasm and toaddr }
                 case tabsolutevarsym(symtableentry).abstyp of
                   toaddr :
                     begin
{$ifdef i386}
                       if tabsolutevarsym(symtableentry).absseg then
                         location.reference.segment:=NR_FS;
{$endif i386}
                       location.reference.offset:=aint(tabsolutevarsym(symtableentry).addroffset);
                     end;
                   toasm :
                     location.reference.symbol:=current_asmdata.RefAsmSymbol(tabsolutevarsym(symtableentry).mangledname);
                   else
                     internalerror(200310283);
                 end;
              end;
           constsym:
             begin
                if tconstsym(symtableentry).consttyp=constresourcestring then
                  begin
                     location_reset_ref(location,LOC_CREFERENCE,OS_ADDR,sizeof(pint));
                     location.reference.symbol:=current_asmdata.RefAsmSymbol(make_mangledname('RESSTR',symtableentry.owner,symtableentry.name));
                     { Resourcestring layout:
                         TResourceStringRecord = Packed Record
                            Name,
                            CurrentValue,
                            DefaultValue : AnsiString;
                            HashValue    : LongWord;
                          end;
                     }
                     location.reference.offset:=sizeof(pint);
                  end
                else
                  internalerror(22798);
             end;
           staticvarsym :
             begin
               gvs:=tstaticvarsym(symtableentry);

               if (vo_is_dll_var in gvs.varoptions) then
               { DLL variable }
                 begin
                   hregister:=cg.getaddressregister(current_asmdata.CurrAsmList);
                   if not(vo_is_weak_external in gvs.varoptions) then
                     location.reference.symbol:=current_asmdata.RefAsmSymbol(tstaticvarsym(symtableentry).mangledname)
                   else
                     location.reference.symbol:=current_asmdata.WeakRefAsmSymbol(tstaticvarsym(symtableentry).mangledname);
                   cg.a_load_ref_reg(current_asmdata.CurrAsmList,OS_ADDR,OS_ADDR,location.reference,hregister);
                   reference_reset_base(location.reference,hregister,0,location.reference.alignment);
                 end
               { Thread variable }
               else if (vo_is_thread_var in gvs.varoptions) then
                 begin
                    if (tf_section_threadvars in target_info.flags) then
                      begin
                        if gvs.localloc.loc=LOC_INVALID then
                          if not(vo_is_weak_external in gvs.varoptions) then
                            reference_reset_symbol(location.reference,current_asmdata.RefAsmSymbol(gvs.mangledname),0,location.reference.alignment)
                          else
                            reference_reset_symbol(location.reference,current_asmdata.WeakRefAsmSymbol(gvs.mangledname),0,location.reference.alignment)
                        else
                          location:=gvs.localloc;
{$ifdef i386}
                        case target_info.system of
                          system_i386_linux:
                            location.reference.segment:=NR_GS;
                          system_i386_win32:
                            location.reference.segment:=NR_FS;
                        end;
{$endif i386}
                      end
                    else
                      begin
                        {
                          Thread var loading is optimized to first check if
                          a relocate function is available. When the function
                          is available it is called to retrieve the address.
                          Otherwise the address is loaded with the symbol

                          The code needs to be in the order to first handle the
                          call and then the address load to be sure that the
                          register that is used for returning is the same (PFV)
                        }
                        current_asmdata.getjumplabel(norelocatelab);
                        current_asmdata.getjumplabel(endrelocatelab);
                        { make sure hregister can't allocate the register necessary for the parameter }
                        paraloc1.init;
                        paramanager.getintparaloc(pocall_default,1,paraloc1);
                        hregister:=cg.getaddressregister(current_asmdata.CurrAsmList);
                        reference_reset_symbol(href,current_asmdata.RefAsmSymbol('FPC_THREADVAR_RELOCATE'),0,sizeof(pint));
                        cg.a_load_ref_reg(current_asmdata.CurrAsmList,OS_ADDR,OS_ADDR,href,hregister);
                        cg.a_cmp_const_reg_label(current_asmdata.CurrAsmList,OS_ADDR,OC_EQ,0,hregister,norelocatelab);
                        { don't save the allocated register else the result will be destroyed later }
                        if not(vo_is_weak_external in gvs.varoptions) then
                          reference_reset_symbol(href,current_asmdata.RefAsmSymbol(gvs.mangledname),0,sizeof(pint))
                        else
                          reference_reset_symbol(href,current_asmdata.WeakRefAsmSymbol(gvs.mangledname),0,sizeof(pint));
                        cg.a_load_ref_cgpara(current_asmdata.CurrAsmList,OS_32,href,paraloc1);
                        paramanager.freecgpara(current_asmdata.CurrAsmList,paraloc1);
                        paraloc1.done;
                        cg.allocallcpuregisters(current_asmdata.CurrAsmList);
                        cg.a_call_reg(current_asmdata.CurrAsmList,hregister);
                        cg.deallocallcpuregisters(current_asmdata.CurrAsmList);
                        cg.getcpuregister(current_asmdata.CurrAsmList,NR_FUNCTION_RESULT_REG);
                        cg.ungetcpuregister(current_asmdata.CurrAsmList,NR_FUNCTION_RESULT_REG);
                        hregister:=cg.getaddressregister(current_asmdata.CurrAsmList);
                        cg.a_load_reg_reg(current_asmdata.CurrAsmList,OS_INT,OS_ADDR,NR_FUNCTION_RESULT_REG,hregister);
                        cg.a_jmp_always(current_asmdata.CurrAsmList,endrelocatelab);
                        cg.a_label(current_asmdata.CurrAsmList,norelocatelab);
                        { no relocation needed, load the address of the variable only, the
                          layout of a threadvar is (4 bytes pointer):
                            0 - Threadvar index
                            4 - Threadvar value in single threading }
                        if not(vo_is_weak_external in gvs.varoptions) then
                          reference_reset_symbol(href,current_asmdata.RefAsmSymbol(gvs.mangledname),sizeof(pint),sizeof(pint))
                        else
                          reference_reset_symbol(href,current_asmdata.WeakRefAsmSymbol(gvs.mangledname),sizeof(pint),sizeof(pint));
                        cg.a_loadaddr_ref_reg(current_asmdata.CurrAsmList,href,hregister);
                        cg.a_label(current_asmdata.CurrAsmList,endrelocatelab);
                        location.reference.base:=hregister;
                      end;
                  end
                { Normal (or external) variable }
                else
                  begin
                    if gvs.localloc.loc=LOC_INVALID then
                      if not(vo_is_weak_external in gvs.varoptions) then
                        reference_reset_symbol(location.reference,current_asmdata.RefAsmSymbol(gvs.mangledname),0,location.reference.alignment)
                      else
                        reference_reset_symbol(location.reference,current_asmdata.WeakRefAsmSymbol(gvs.mangledname),0,location.reference.alignment)
                    else
                      location:=gvs.localloc;
                  end;

                { make const a LOC_CREFERENCE }
                if (gvs.varspez=vs_const) and
                   (location.loc=LOC_REFERENCE) then
                  location.loc:=LOC_CREFERENCE;
              end;
            paravarsym,
            localvarsym :
              begin
                vs:=tabstractnormalvarsym(symtableentry);
                { Nested variable }
                if assigned(left) then
                  generate_nested_access(vs)
                else
                  location:=vs.localloc;

                { handle call by reference variables when they are not
                  already copied to local copies. Also ignore the reference
                  when we need to load the self pointer for objects }
                if is_addr_param_load then
                  begin
                    if (location.loc in [LOC_CREGISTER,LOC_REGISTER]) then
                      hregister:=location.register
                    else
                      begin
                        hregister:=hlcg.getaddressregister(current_asmdata.CurrAsmList,voidpointertype);
                        { we need to load only an address }
                        location.size:=OS_ADDR;
                        hlcg.a_load_loc_reg(current_asmdata.CurrAsmList,voidpointertype,voidpointertype,location,hregister);
                      end;
                    { assume packed records may always be unaligned }
                    if not(resultdef.typ in [recorddef,objectdef]) or
                       (tabstractrecordsymtable(tabstractrecorddef(resultdef).symtable).usefieldalignment<>1) then
                      location_reset_ref(location,LOC_REFERENCE,newsize,resultdef.alignment)
                    else
                      location_reset_ref(location,LOC_REFERENCE,newsize,1);
                    location.reference.base:=hregister;
                  end;

                { make const a LOC_CREFERENCE }
                if (vs.varspez=vs_const) and
                   (location.loc=LOC_REFERENCE) then
                  location.loc:=LOC_CREFERENCE;
             end;
           procsym:
              begin
                 if not assigned(procdef) then
                   internalerror(200312011);
                 if assigned(left) then
                   begin
                     {$if sizeof(pint) = 4}
                        location_reset_ref(location,LOC_CREFERENCE,OS_64,sizeof(pint));
                     {$else} {$if sizeof(pint) = 8}
                        location_reset_ref(location,LOC_CREFERENCE,OS_128,sizeof(pint));
                     {$else}
                        internalerror(20020520);
                     {$endif} {$endif}
                     tg.gethltemp(current_asmdata.CurrAsmList,methodpointertype,methodpointertype.size,tt_normal,location.reference);
                     secondpass(left);

                     { load class instance/classrefdef address }
                     if left.location.loc=LOC_CONSTANT then
                       { todo: exact type for hlcg (can't use left.resultdef, because can be TP-style object, which is not pointer-sized) }
                       hlcg.location_force_reg(current_asmdata.CurrAsmList,left.location,left.resultdef,voidpointertype,false);
                     case left.location.loc of
                        LOC_CREGISTER,
                        LOC_REGISTER:
                          begin
                             { this is not possible for objects }
                             if is_object(left.resultdef) then
                               internalerror(200304234);
                             hregister:=left.location.register;
                          end;
                        LOC_CREFERENCE,
                        LOC_REFERENCE:
                          begin
                             hregister:=cg.getaddressregister(current_asmdata.CurrAsmList);
                             if not is_object(left.resultdef) then
                               cg.a_load_ref_reg(current_asmdata.CurrAsmList,OS_ADDR,OS_ADDR,left.location.reference,hregister)
                             else
                               cg.a_loadaddr_ref_reg(current_asmdata.CurrAsmList,left.location.reference,hregister);
                             location_freetemp(current_asmdata.CurrAsmList,left.location);
                          end;
                        else
                          internalerror(200610311);
                     end;

                     { store the class instance or classredef address }
                     href:=location.reference;
                     inc(href.offset,sizeof(pint));
                     cg.a_load_reg_ref(current_asmdata.CurrAsmList,OS_ADDR,OS_ADDR,hregister,href);

                     { virtual method ? }
                     if (po_virtualmethod in procdef.procoptions) and
                        not(loadnf_inherited in loadnodeflags) and
                        not is_objectpascal_helper(procdef.struct) then
                       begin
                         if (not assigned(current_procinfo) or
                             wpoinfomanager.symbol_live(current_procinfo.procdef.mangledname)) then
                           tobjectdef(procdef.struct).register_vmt_call(procdef.extnumber);
            {$ifdef vtentry}
                         if not is_interface(procdef.struct) then
                           begin
                             inc(current_asmdata.NextVTEntryNr);
                             current_asmdata.CurrAsmList.Concat(tai_symbol.CreateName('VTREF'+tostr(current_asmdata.NextVTEntryNr)+'_'+procdef._class.vmt_mangledname+'$$'+tostr(vmtoffset div sizeof(pint)),AT_FUNCTION,0));
                           end;
            {$endif vtentry}
                         { a classrefdef already points to the VMT }
                         if (left.resultdef.typ<>classrefdef) then
                           begin
                             { load vmt pointer }
                             reference_reset_base(href,hregister,tobjectdef(left.resultdef).vmt_offset,sizeof(pint));
                             hregister:=cg.getaddressregister(current_asmdata.CurrAsmList);
                             cg.a_load_ref_reg(current_asmdata.CurrAsmList,OS_ADDR,OS_ADDR,href,hregister);
                           end;
                         { load method address }
                         reference_reset_base(href,hregister,tobjectdef(procdef.struct).vmtmethodoffset(procdef.extnumber),sizeof(pint));
                         hregister:=cg.getaddressregister(current_asmdata.CurrAsmList);
                         cg.a_load_ref_reg(current_asmdata.CurrAsmList,OS_ADDR,OS_ADDR,href,hregister);
                         { ... and store it }
                         cg.a_load_reg_ref(current_asmdata.CurrAsmList,OS_ADDR,OS_ADDR,hregister,location.reference);
                       end
                     else
                       begin
                         { load address of the function }
                         reference_reset_symbol(href,current_asmdata.RefAsmSymbol(procdef.mangledname),0,sizeof(pint));
                         hregister:=cg.getaddressregister(current_asmdata.CurrAsmList);
                         cg.a_loadaddr_ref_reg(current_asmdata.CurrAsmList,href,hregister);
                         cg.a_load_reg_ref(current_asmdata.CurrAsmList,OS_ADDR,OS_ADDR,hregister,location.reference);
                       end;
                   end
                 else
                   begin
                      pd:=tprocdef(tprocsym(symtableentry).ProcdefList[0]);
                      if not(po_weakexternal in pd.procoptions) then
                        location.reference.symbol:=current_asmdata.RefAsmSymbol(procdef.mangledname)
                      else
                        location.reference.symbol:=current_asmdata.WeakRefAsmSymbol(procdef.mangledname);
                   end;
              end;
           labelsym :
             if assigned(tlabelsym(symtableentry).asmblocklabel) then
               location.reference.symbol:=tlabelsym(symtableentry).asmblocklabel
             else
               location.reference.symbol:=tcglabelnode((tlabelsym(symtableentry).code)).getasmlabel;
           else internalerror(200510032);
        end;
      end;


{*****************************************************************************
                             SecondAssignment
*****************************************************************************}

    procedure tcgassignmentnode.pass_generate_code;
      var
         otlabel,hlabel,oflabel : tasmlabel;
         href : treference;
         releaseright : boolean;
         alignmentrequirement,
         len : aint;
         r : tregister;
         r64 : tregister64;
         oldflowcontrol : tflowcontrol;
      begin
        location_reset(location,LOC_VOID,OS_NO);
        { managed types should be handled in firstpass }
        if not(target_info.system in systems_garbage_collected_managed_types) and
           (is_managed_type(left.resultdef) or
            is_managed_type(right.resultdef)) then
          InternalError(2012011901);

        otlabel:=current_procinfo.CurrTrueLabel;
        oflabel:=current_procinfo.CurrFalseLabel;
        current_asmdata.getjumplabel(current_procinfo.CurrTrueLabel);
        current_asmdata.getjumplabel(current_procinfo.CurrFalseLabel);

        {
          in most cases we can process first the right node which contains
          the most complex code. Exceptions for this are:
            - result is in flags, loading left will then destroy the flags
            - result is a jump, loading left must be already done before the jump is made
            - result need reference count, when left points to a value used in
              right then decreasing the refcnt on left can possibly release
              the memory before right increased the refcnt, result is that an
              empty value is assigned

           But not when the result is in the flags, then
          loading the left node afterwards can destroy the flags.
        }
        if not(right.expectloc in [LOC_FLAGS,LOC_JUMP]) and
            (node_complexity(right)>node_complexity(left)) then
         begin
           secondpass(right);
           if codegenerror then
             exit;

           secondpass(left);
           if codegenerror then
             exit;
         end
        else
         begin
           { calculate left sides }
           secondpass(left);
           if codegenerror then
             exit;

           { tell the SSA/SSL code that the left side was handled first so
             ni SSL is done
           }
           oldflowcontrol:=flowcontrol;
           include(flowcontrol,fc_lefthandled);

           secondpass(right);
           flowcontrol:=oldflowcontrol;

           if codegenerror then
             exit;
         end;

        releaseright:=true;

        { shortstring assignments are handled separately }
        if is_shortstring(left.resultdef) then
          begin
            {
              we can get here only in the following situations
              for the right node:
               - empty constant string
               - char
            }

            { The addn is replaced by a blockn or calln that already returns
              a shortstring }
            if is_shortstring(right.resultdef) and
               (right.nodetype in [blockn,calln]) then
              begin
                { nothing to do }
              end
            { empty constant string }
            else if (right.nodetype=stringconstn) and
               (tstringconstnode(right).len=0) then
              begin
                hlcg.a_load_const_ref(current_asmdata.CurrAsmList,u8inttype,0,left.location.reference);
              end
            { char loading }
            else if is_char(right.resultdef) then
              begin
                if right.nodetype=ordconstn then
                  begin
                    if (target_info.endian = endian_little) then
                      hlcg.a_load_const_ref(current_asmdata.CurrAsmList,u16inttype,(tordconstnode(right).value.svalue shl 8) or 1,
                          setalignment(left.location.reference,1))
                    else
                      hlcg.a_load_const_ref(current_asmdata.CurrAsmList,u16inttype,tordconstnode(right).value.svalue or (1 shl 8),
                          setalignment(left.location.reference,1));
                  end
                else
                  begin
                    href:=left.location.reference;
                    hlcg.a_load_const_ref(current_asmdata.CurrAsmList,u8inttype,1,href);
                    inc(href.offset,1);
                    case right.location.loc of
                      LOC_REGISTER,
                      LOC_CREGISTER :
                        begin
{$ifndef cpuhighleveltarget}
                          r:=cg.makeregsize(current_asmdata.CurrAsmList,right.location.register,OS_8);
{$else not cpuhighleveltarget}
                          r:=hlcg.getintregister(current_asmdata.CurrAsmList,u8inttype);
                          hlcg.a_load_reg_reg(current_asmdata.CurrAsmList,u8inttype,u8inttype,right.location.register,r);
{$endif cpuhighleveltarget}
                          hlcg.a_load_reg_ref(current_asmdata.CurrAsmList,u8inttype,u8inttype,r,href);
                        end;
                      LOC_REFERENCE,
                      LOC_CREFERENCE :
                        hlcg.a_load_ref_ref(current_asmdata.CurrAsmList,u8inttype,u8inttype,right.location.reference,href);
                      else
                        internalerror(200205111);
                    end;
                  end;
              end
            else
              internalerror(2002042410);
          end
       { try to reuse memory locations instead of copying }
       { copy to a memory location ... }
        else if (right.location.loc = LOC_REFERENCE) and
           maybechangetemp(current_asmdata.CurrAsmList,left,right.location.reference) then
          begin
            { if it worked, we're done }
          end
        else
          begin
            { SSA support }
            maybechangeloadnodereg(current_asmdata.CurrAsmList,left,false);
            maybechangeloadnodereg(current_asmdata.CurrAsmList,right,true);
            case right.location.loc of
              LOC_CONSTANT :
                begin
{$ifndef cpu64bitalu}
                  if (left.location.size in [OS_64,OS_S64]) or (right.location.size in [OS_64,OS_S64]) then
                    cg64.a_load64_const_loc(current_asmdata.CurrAsmList,right.location.value64,left.location)
                  else
{$endif not cpu64bitalu}
                    hlcg.a_load_const_loc(current_asmdata.CurrAsmList,left.resultdef,right.location.value,left.location);
                end;
              LOC_REFERENCE,
              LOC_CREFERENCE :
                begin
                  case left.location.loc of
                    LOC_REGISTER,
                    LOC_CREGISTER :
                      begin
{$ifndef cpu64bitalu}
                        if left.location.size in [OS_64,OS_S64] then
                          cg64.a_load64_ref_reg(current_asmdata.CurrAsmList,right.location.reference,left.location.register64)
                        else
{$endif not cpu64bitalu}
                          hlcg.a_load_ref_reg(current_asmdata.CurrAsmList,right.resultdef,left.resultdef,right.location.reference,left.location.register);
                      end;
                    LOC_FPUREGISTER,
                    LOC_CFPUREGISTER :
                      begin
                        hlcg.a_loadfpu_ref_reg(current_asmdata.CurrAsmList,
                            right.resultdef,left.resultdef,
                            right.location.reference,
                            left.location.register);
                      end;
                    LOC_REFERENCE,
                    LOC_CREFERENCE :
                      begin
                        if (left.resultdef.typ=floatdef) and
                           (right.resultdef.typ=floatdef) and
                           (left.location.size<>right.location.size) then
                          begin
                            hlcg.a_loadfpu_ref_ref(current_asmdata.CurrAsmList,
                              right.resultdef,left.resultdef,
                              right.location.reference,left.location.reference)
                          end
                        else
                          begin
{ TODO: HACK: unaligned test, maybe remove all unaligned locations (array of char) from the compiler}
                            { Use unaligned copy when the offset is not aligned }
                            len:=left.resultdef.size;
                            { can be 0 in case of formaldef on JVM target }
                            if len=0 then
                              len:=sizeof(pint);

                            { data smaller than an aint has less alignment requirements }
                            { max(1,...) avoids div by zero in case of an empty record  }
                            alignmentrequirement:=min(max(1,len),sizeof(aint));

                            if (right.location.reference.offset mod alignmentrequirement<>0) or
                              (left.location.reference.offset mod alignmentrequirement<>0) or
                              (right.resultdef.alignment<alignmentrequirement) or
                              ((right.location.reference.alignment<>0) and
                               (right.location.reference.alignment<alignmentrequirement)) or
                              ((left.location.reference.alignment<>0) and
                               (left.location.reference.alignment<alignmentrequirement)) then
                              hlcg.g_concatcopy_unaligned(current_asmdata.CurrAsmList,left.resultdef,right.location.reference,left.location.reference)
                            else
                              hlcg.g_concatcopy(current_asmdata.CurrAsmList,left.resultdef,right.location.reference,left.location.reference);
                          end;
                      end;
                    LOC_MMREGISTER,
                    LOC_CMMREGISTER:
                      begin
{$ifdef x86}
                        if (right.resultdef.typ=floatdef) and
                           not use_vectorfpu(right.resultdef) then
                          begin
                            { perform size conversion if needed (the mm-code cannot }
                            { convert an extended into a double/single, since sse   }
                            { doesn't support extended)                             }
                            r:=cg.getfpuregister(current_asmdata.CurrAsmList,right.location.size);
                            tg.gethltemp(current_asmdata.CurrAsmList,left.resultdef,left.resultdef.size,tt_normal,href);
                            cg.a_loadfpu_ref_reg(current_asmdata.CurrAsmList,right.location.size,right.location.size,right.location.reference,r);
                            cg.a_loadfpu_reg_ref(current_asmdata.CurrAsmList,right.location.size,left.location.size,r,href);
                            if releaseright then
                              location_freetemp(current_asmdata.CurrAsmList,right.location);
                            releaseright:=true;
                            location_reset_ref(right.location,LOC_REFERENCE,left.location.size,0);
                            right.location.reference:=href;
                          end;
{$endif}
                        cg.a_loadmm_ref_reg(current_asmdata.CurrAsmList,
                          right.location.size,
                          left.location.size,
                          right.location.reference,
                          left.location.register,mms_movescalar);
                      end;
                    LOC_SUBSETREG,
                    LOC_CSUBSETREG:
                      hlcg.a_load_ref_subsetreg(current_asmdata.CurrAsmList,right.resultdef,left.resultdef,right.location.reference,left.location.sreg);
                    LOC_SUBSETREF,
                    LOC_CSUBSETREF:
{$ifndef cpu64bitalu}
                      if right.location.size in [OS_64,OS_S64] then
                       cg64.a_load64_ref_subsetref(current_asmdata.CurrAsmList,right.location.reference,left.location.sref)
                      else
{$endif not cpu64bitalu}
                       hlcg.a_load_ref_subsetref(current_asmdata.CurrAsmList,right.resultdef,left.resultdef,right.location.reference,left.location.sref);
                    else
                      internalerror(200203284);
                  end;
                end;
{$ifdef SUPPORT_MMX}
              LOC_CMMXREGISTER,
              LOC_MMXREGISTER:
                begin
                  if left.location.loc=LOC_CMMXREGISTER then
                    cg.a_loadmm_reg_reg(current_asmdata.CurrAsmList,OS_M64,OS_M64,right.location.register,left.location.register,nil)
                  else
                    cg.a_loadmm_reg_ref(current_asmdata.CurrAsmList,OS_M64,OS_M64,right.location.register,left.location.reference,nil);
                end;
{$endif SUPPORT_MMX}
              LOC_MMREGISTER,
              LOC_CMMREGISTER:
                begin
                  if left.resultdef.typ=arraydef then
                    begin
                    end
                  else
                    begin
                      case left.location.loc of
                        LOC_CMMREGISTER,
                        LOC_MMREGISTER:
                          cg.a_loadmm_reg_reg(current_asmdata.CurrAsmList,right.location.size,left.location.size,right.location.register,left.location.register,mms_movescalar);
                        LOC_REFERENCE,
                        LOC_CREFERENCE:
                          cg.a_loadmm_reg_ref(current_asmdata.CurrAsmList,right.location.size,left.location.size,right.location.register,left.location.reference,mms_movescalar);
                        else
                          internalerror(2009112601);
                      end;
                    end;
                end;
              LOC_REGISTER,
              LOC_CREGISTER :
                begin
{$ifndef cpu64bitalu}
                  { also OS_F64 in case of mmreg -> intreg }
                  if left.location.size in [OS_64,OS_S64,OS_F64] then
                    cg64.a_load64_reg_loc(current_asmdata.CurrAsmList,
                      right.location.register64,left.location)
                  else
{$endif not cpu64bitalu}
                    hlcg.a_load_reg_loc(current_asmdata.CurrAsmList,right.resultdef,left.resultdef,right.location.register,left.location);
                end;
              LOC_FPUREGISTER,
              LOC_CFPUREGISTER :
                begin
                  { we can't do direct moves between fpu and mm registers }
                  if left.location.loc in [LOC_MMREGISTER,LOC_CMMREGISTER] then
                    begin
{$ifdef x86}
                      if not use_vectorfpu(right.resultdef) then
                        begin
                          { perform size conversion if needed (the mm-code cannot convert an   }
                          { extended into a double/single, since sse doesn't support extended) }
                          tg.gethltemp(current_asmdata.CurrAsmList,left.resultdef, left.resultdef.size,tt_normal,href);
                          cg.a_loadfpu_reg_ref(current_asmdata.CurrAsmList,right.location.size,left.location.size,right.location.register,href);
                          location_reset_ref(right.location,LOC_REFERENCE,left.location.size,0);
                          right.location.reference:=href;
                        end;
{$endif}
                      location_force_mmregscalar(current_asmdata.CurrAsmList,right.location,false);
                      cg.a_loadmm_reg_reg(current_asmdata.CurrAsmList,
                          right.location.size,left.location.size,
                          right.location.register,left.location.register,mms_movescalar);
                    end
                  else
                    hlcg.a_loadfpu_reg_loc(current_asmdata.CurrAsmList,
                        right.resultdef,left.resultdef,
                        right.location.register,left.location);
                end;
              LOC_SUBSETREG,
              LOC_CSUBSETREG:
                begin
                  hlcg.a_load_subsetreg_loc(current_asmdata.CurrAsmList,
                      right.resultdef,left.resultdef,right.location.sreg,left.location);
                end;
              LOC_SUBSETREF,
              LOC_CSUBSETREF:
                begin
{$ifndef cpu64bitalu}
                  if right.location.size in [OS_64,OS_S64] then
                   cg64.a_load64_subsetref_loc(current_asmdata.CurrAsmList,right.location.sref,left.location)
                  else
{$endif not cpu64bitalu}
                  hlcg.a_load_subsetref_loc(current_asmdata.CurrAsmList,
                      right.resultdef,left.resultdef,right.location.sref,left.location);
                end;
              LOC_JUMP :
                begin
                  current_asmdata.getjumplabel(hlabel);
                  hlcg.a_label(current_asmdata.CurrAsmList,current_procinfo.CurrTrueLabel);
                  if is_pasbool(left.resultdef) then
                    begin
{$ifndef cpu64bitalu}
                      if left.location.size in [OS_64,OS_S64] then
                        cg64.a_load64_const_loc(current_asmdata.CurrAsmList,1,left.location)
                      else
{$endif not cpu64bitalu}
                        hlcg.a_load_const_loc(current_asmdata.CurrAsmList,left.resultdef,1,left.location)
                    end
                  else
                    begin
{$ifndef cpu64bitalu}
                      if left.location.size in [OS_64,OS_S64] then
                        cg64.a_load64_const_loc(current_asmdata.CurrAsmList,-1,left.location)
                      else
{$endif not cpu64bitalu}
                        hlcg.a_load_const_loc(current_asmdata.CurrAsmList,left.resultdef,-1,left.location);
                    end;

                  hlcg.a_jmp_always(current_asmdata.CurrAsmList,hlabel);
                  hlcg.a_label(current_asmdata.CurrAsmList,current_procinfo.CurrFalseLabel);
{$ifndef cpu64bitalu}
                  if left.location.size in [OS_64,OS_S64] then
                    cg64.a_load64_const_loc(current_asmdata.CurrAsmList,0,left.location)
                  else
{$endif not cpu64bitalu}
                    hlcg.a_load_const_loc(current_asmdata.CurrAsmList,left.resultdef,0,left.location);
                  hlcg.a_label(current_asmdata.CurrAsmList,hlabel);
                end;
{$ifdef cpuflags}
              LOC_FLAGS :
                begin
                  if is_pasbool(left.resultdef) then
                    begin
                      case left.location.loc of
                        LOC_REGISTER,LOC_CREGISTER:
{$ifdef cpu32bitalu}
                          if left.location.size in [OS_S64,OS_64] then
                            begin
                              cg.g_flags2reg(current_asmdata.CurrAsmList,OS_32,right.location.resflags,left.location.register64.reglo);
                              cg.a_load_const_reg(current_asmdata.CurrAsmList,OS_32,0,left.location.register64.reghi);
                            end
                          else
{$endif cpu32bitalu}
                            cg.g_flags2reg(current_asmdata.CurrAsmList,left.location.size,right.location.resflags,left.location.register);
                        LOC_REFERENCE:
                        { i386 has a hack in its code generator so that it can
                          deal with 64 bit locations in this parcticular case }
{$if defined(cpu32bitalu) and not defined(x86)}
                          if left.location.size in [OS_S64,OS_64] then
                            begin
                              r64.reglo:=cg.getintregister(current_asmdata.CurrAsmList,OS_32);
                              r64.reghi:=cg.getintregister(current_asmdata.CurrAsmList,OS_32);
                              cg.g_flags2reg(current_asmdata.CurrAsmList,OS_32,right.location.resflags,r64.reglo);
                              cg.a_load_const_reg(current_asmdata.CurrAsmList,OS_32,0,r64.reghi);
                              cg64.a_load64_reg_ref(current_asmdata.CurrAsmList,r64,left.location.reference);
                            end
                          else
{$endif cpu32bitalu}
                            cg.g_flags2ref(current_asmdata.CurrAsmList,left.location.size,right.location.resflags,left.location.reference);
                        LOC_SUBSETREG,LOC_SUBSETREF:
                          begin
                            r:=cg.getintregister(current_asmdata.CurrAsmList,left.location.size);
                            cg.g_flags2reg(current_asmdata.CurrAsmList,left.location.size,right.location.resflags,r);
                            hlcg.a_load_reg_loc(current_asmdata.CurrAsmList,left.resultdef,left.resultdef,r,left.location);
                          end;
                        else
                          internalerror(200203273);
                      end;
                    end
                  else
                    begin
{$ifdef cpu32bitalu}
                      if left.location.size in [OS_S64,OS_64] then
                        begin
                          r64.reglo:=cg.getintregister(current_asmdata.CurrAsmList,OS_32);
                          r64.reghi:=cg.getintregister(current_asmdata.CurrAsmList,OS_32);
                          cg.g_flags2reg(current_asmdata.CurrAsmList,OS_32,right.location.resflags,r64.reglo);
                          cg.a_load_const_reg(current_asmdata.CurrAsmList,OS_32,0,r64.reghi);
                          cg64.a_op64_reg_reg(current_asmdata.CurrAsmList,OP_NEG,OS_S64,
                            r64,r64);
                          cg64.a_load64_reg_loc(current_asmdata.CurrAsmList,r64,left.location);
                        end
                      else
{$endif cpu32bitalu}
                        begin
                          r:=cg.getintregister(current_asmdata.CurrAsmList,left.location.size);
                          cg.g_flags2reg(current_asmdata.CurrAsmList,left.location.size,right.location.resflags,r);
                          cg.a_op_reg_reg(current_asmdata.CurrAsmList,OP_NEG,left.location.size,r,r);
                          hlcg.a_load_reg_loc(current_asmdata.CurrAsmList,left.resultdef,left.resultdef,r,left.location);
                        end
                    end;
                end;
{$endif cpuflags}
            end;
         end;

        if releaseright then
          location_freetemp(current_asmdata.CurrAsmList,right.location);

        current_procinfo.CurrTrueLabel:=otlabel;
        current_procinfo.CurrFalseLabel:=oflabel;
      end;


{*****************************************************************************
                           SecondArrayConstruct
*****************************************************************************}

      const
        vtInteger       = 0;
        vtBoolean       = 1;
        vtChar          = 2;
        vtExtended      = 3;
        vtString        = 4;
        vtPointer       = 5;
        vtPChar         = 6;
        vtObject        = 7;
        vtClass         = 8;
        vtWideChar      = 9;
        vtPWideChar     = 10;
        vtAnsiString32  = 11;
        vtCurrency      = 12;
        vtVariant       = 13;
        vtInterface     = 14;
        vtWideString    = 15;
        vtInt64         = 16;
        vtQWord         = 17;
        vtUnicodeString = 18;
        vtAnsiString16  = 19;
        vtAnsiString64  = 20;


    procedure tcgarrayconstructornode.makearrayref(var ref: treference; eledef: tdef);
      begin
        { do nothing by default }
      end;


    procedure tcgarrayconstructornode.advancearrayoffset(var ref: treference; elesize: asizeint);
      begin
        inc(ref.offset,elesize);
      end;


    procedure tcgarrayconstructornode.pass_generate_code;
      var
        hp    : tarrayconstructornode;
        href  : treference;
        lt    : tdef;
        paraloc : tcgparalocation;
        otlabel,
        oflabel : tasmlabel;
        vtype : longint;
        eledef: tdef;
        elesize : longint;
        tmpreg  : tregister;
        vaddr : boolean;
        freetemp,
        dovariant: boolean;
      begin
        if is_packed_array(resultdef) then
          internalerror(200608042);
        dovariant:=
          ((nf_forcevaria in flags) or is_variant_array(resultdef)) and
          not(target_info.system in systems_managed_vm);
        if dovariant then
          begin
            eledef:=search_system_type('TVARREC').typedef;
            elesize:=eledef.size;
          end
        else
          begin
            eledef:=tarraydef(resultdef).elementdef;
            elesize:=tarraydef(resultdef).elesize;
          end;
        { alignment is filled in by tg.gethltemp below }
        location_reset_ref(location,LOC_CREFERENCE,OS_NO,0);
        fillchar(paraloc,sizeof(paraloc),0);
        { Allocate always a temp, also if no elements are required, to
          be sure that location is valid (PFV) }
        { on the JVM platform, an array can have 0 elements; since the length
          of the array is part of the array itself, make sure we allocate one
          of the proper length to avoid getting unexpected results later }
         if tarraydef(resultdef).highrange=-1 then
           tg.gethltemp(current_asmdata.CurrAsmList,resultdef,{$ifdef jvm}0{$else}elesize{$endif},tt_normal,location.reference)
         else
           tg.gethltemp(current_asmdata.CurrAsmList,resultdef,(tarraydef(resultdef).highrange+1)*elesize,tt_normal,location.reference);
         href:=location.reference;
         makearrayref(href,eledef);
        { Process nodes in array constructor }
        hp:=self;
        while assigned(hp) do
         begin
           if assigned(hp.left) then
            begin
              freetemp:=true;
              if (hp.left.expectloc=LOC_JUMP) then
                begin
                  otlabel:=current_procinfo.CurrTrueLabel;
                  oflabel:=current_procinfo.CurrFalseLabel;
                  current_asmdata.getjumplabel(current_procinfo.CurrTrueLabel);
                  current_asmdata.getjumplabel(current_procinfo.CurrFalseLabel);
                end;
              secondpass(hp.left);
              { Move flags and jump in register }
              if hp.left.location.loc in [LOC_FLAGS,LOC_JUMP] then
                hlcg.location_force_reg(current_asmdata.CurrAsmList,hp.left.location,hp.left.resultdef,hp.left.resultdef,false);

              if (hp.left.location.loc=LOC_JUMP) then
                begin
                  if (hp.left.expectloc<>LOC_JUMP) then
                    internalerror(2007103101);
                  current_procinfo.CurrTrueLabel:=otlabel;
                  current_procinfo.CurrFalseLabel:=oflabel;
                end;

              if dovariant then
               begin
                 { find the correct vtype value }
                 vtype:=$ff;
                 vaddr:=false;
                 lt:=hp.left.resultdef;
                 case lt.typ of
                   enumdef,
                   orddef :
                     begin
                       if is_64bit(lt) then
                         begin
                            case torddef(lt).ordtype of
                              scurrency:
                                vtype:=vtCurrency;
                              s64bit:
                                vtype:=vtInt64;
                              u64bit:
                                vtype:=vtQWord;
                            end;
                            freetemp:=false;
                            vaddr:=true;
                         end
                       else if (lt.typ=enumdef) or
                         is_integer(lt) then
                         vtype:=vtInteger
                       else
                         if is_boolean(lt) then
                           vtype:=vtBoolean
                         else
                           if (lt.typ=orddef) then
                             begin
                               case torddef(lt).ordtype of
                                 uchar:
                                   vtype:=vtChar;
                                 uwidechar:
                                   vtype:=vtWideChar;
                               end;
                             end;
                     end;
                   floatdef :
                     begin
                       if is_currency(lt) then
                         vtype:=vtCurrency
                       else
                         vtype:=vtExtended;
                       freetemp:=false;
                       vaddr:=true;
                     end;
                   procvardef,
                   pointerdef :
                     begin
                       if is_pchar(lt) then
                         vtype:=vtPChar
                       else if is_pwidechar(lt) then
                         vtype:=vtPWideChar
                       else
                         vtype:=vtPointer;
                     end;
                   variantdef :
                     begin
                        vtype:=vtVariant;
                        vaddr:=true;
                        freetemp:=false;
                     end;
                   classrefdef :
                     vtype:=vtClass;
                   objectdef :
                     if is_interface(lt) then
                       vtype:=vtInterface
                     { vtObject really means a class based on TObject }
                     else if is_class(lt) then
                       vtype:=vtObject
                     else
                       internalerror(200505171);
                   stringdef :
                     begin
                       if is_shortstring(lt) then
                        begin
                          vtype:=vtString;
                          vaddr:=true;
                          freetemp:=false;
                        end
                       else
                        if is_ansistring(lt) then
                         begin
                           vtype:=vtAnsiString;
                           freetemp:=false;
                         end
                       else
                        if is_widestring(lt) then
                         begin
                           vtype:=vtWideString;
                           freetemp:=false;
                         end
                       else
                        if is_unicodestring(lt) then
                         begin
                           vtype:=vtUnicodeString;
                           freetemp:=false;
                         end;
                     end;
                 end;
                 if vtype=$ff then
                   internalerror(14357);
                 { write changing field update href to the next element }
                 inc(href.offset,sizeof(pint));
                 if vaddr then
                  begin
                    hlcg.location_force_mem(current_asmdata.CurrAsmList,hp.left.location,hp.left.resultdef);
                    tmpreg:=cg.getaddressregister(current_asmdata.CurrAsmList);
                    cg.a_loadaddr_ref_reg(current_asmdata.CurrAsmList,hp.left.location.reference,tmpreg);
                    cg.a_load_reg_ref(current_asmdata.CurrAsmList,OS_ADDR,OS_ADDR,tmpreg,href);
                  end
                 else
                  { todo: proper type information for hlcg }
                  hlcg.a_load_loc_ref(current_asmdata.CurrAsmList,hp.left.resultdef,voidpointertype,hp.left.location,href);
                 { update href to the vtype field and write it }
                 dec(href.offset,sizeof(pint));
                 cg.a_load_const_ref(current_asmdata.CurrAsmList, OS_INT,vtype,href);
                 { goto next array element }
                 advancearrayoffset(href,sizeof(pint)*2);
               end
              else
              { normal array constructor of the same type }
               begin
                 if is_managed_type(resultdef) then
                   freetemp:=false;
                 case hp.left.location.loc of
                   LOC_MMREGISTER,
                   LOC_CMMREGISTER:
                     cg.a_loadmm_reg_ref(current_asmdata.CurrAsmList,hp.left.location.size,hp.left.location.size,
                       hp.left.location.register,href,mms_movescalar);
                   LOC_FPUREGISTER,
                   LOC_CFPUREGISTER :
                     hlcg.a_loadfpu_reg_ref(current_asmdata.CurrAsmList,hp.left.resultdef,hp.left.resultdef,hp.left.location.register,href);
                   LOC_REFERENCE,
                   LOC_CREFERENCE :
                     begin
                       if is_shortstring(hp.left.resultdef) then
                         hlcg.g_copyshortstring(current_asmdata.CurrAsmList,hp.left.location.reference,href,
                             Tstringdef(hp.left.resultdef))
                       else
                         hlcg.g_concatcopy(current_asmdata.CurrAsmList,eledef,hp.left.location.reference,href);
                     end;
                   else
                     begin
{$ifndef cpu64bitalu}
                       if hp.left.location.size in [OS_64,OS_S64] then
                         cg64.a_load64_loc_ref(current_asmdata.CurrAsmList,hp.left.location,href)
                       else
{$endif not cpu64bitalu}
                         hlcg.a_load_loc_ref(current_asmdata.CurrAsmList,eledef,eledef,hp.left.location,href);
                     end;
                 end;
                 advancearrayoffset(href,elesize);
               end;
              if freetemp then
                location_freetemp(current_asmdata.CurrAsmList,hp.left.location);
            end;
           { load next entry }
           hp:=tarrayconstructornode(hp.right);
         end;
      end;


{*****************************************************************************
                           SecondRTTI
*****************************************************************************}

    procedure tcgrttinode.pass_generate_code;
      begin
        location_reset_ref(location,LOC_CREFERENCE,OS_NO,sizeof(pint));
        case rttidatatype of
          rdt_normal:
            location.reference.symbol:=RTTIWriter.get_rtti_label(rttidef,rttitype);
          rdt_ord2str:
            location.reference.symbol:=RTTIWriter.get_rtti_label_ord2str(rttidef,rttitype);
          rdt_str2ord:
            location.reference.symbol:=RTTIWriter.get_rtti_label_str2ord(rttidef,rttitype);
        end;
      end;



begin
   cloadnode:=tcgloadnode;
   cassignmentnode:=tcgassignmentnode;
   carrayconstructornode:=tcgarrayconstructornode;
   crttinode:=tcgrttinode;
end.
