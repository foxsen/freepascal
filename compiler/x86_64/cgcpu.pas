{
    Copyright (c) 2002 by Florian Klaempfl

    This unit implements the code generator for the x86-64.

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
unit cgcpu;

{$i fpcdefs.inc}

  interface

    uses
       cgbase,cgutils,cgobj,cgx86,
       aasmbase,aasmtai,aasmdata,aasmcpu,
       cpubase,cpuinfo,cpupara,parabase,
       symdef,
       node,symconst,rgx86,procinfo;

    type
      tcgx86_64 = class(tcgx86)
        procedure init_register_allocators;override;

        procedure g_proc_entry(list : TAsmList; parasize:longint; nostackframe:boolean);override;
        procedure g_proc_exit(list : TAsmList;parasize:longint;nostackframe:boolean);override;
        procedure g_intf_wrapper(list: TAsmList; procdef: tprocdef; const labelname: string; ioffset: longint);override;
        procedure g_local_unwind(list: TAsmList; l: TAsmLabel);override;

        procedure a_loadmm_intreg_reg(list: TAsmList; fromsize, tosize : tcgsize;intreg, mmreg: tregister; shuffle: pmmshuffle); override;
        procedure a_loadmm_reg_intreg(list: TAsmList; fromsize, tosize : tcgsize;mmreg, intreg: tregister;shuffle : pmmshuffle); override;
      end;

    procedure create_codegen;

  implementation

    uses
       globtype,globals,verbose,systems,cutils,cclasses,
       symsym,defutil,paramgr,fmodule,cpupi,
       rgobj,tgobj,rgcpu;


    procedure Tcgx86_64.init_register_allocators;
      const
        win64_saved_std_regs : array[0..6] of tsuperregister = (RS_RBX,RS_RDI,RS_RSI,RS_R12,RS_R13,RS_R14,RS_R15);
        others_saved_std_regs : array[0..4] of tsuperregister = (RS_RBX,RS_R12,RS_R13,RS_R14,RS_R15);
        saved_regs_length : array[boolean] of longint = (5,7);

        win64_saved_xmm_regs : array[0..9] of tsuperregister = (RS_XMM6,RS_XMM7,
          RS_XMM8,RS_XMM9,RS_XMM10,RS_XMM11,RS_XMM12,RS_XMM13,RS_XMM14,RS_XMM15);
      var
        i : longint;
        framepointer : tsuperregister;
      begin
        inherited init_register_allocators;

        if (length(saved_standard_registers)<>saved_regs_length[target_info.system=system_x86_64_win64]) then
          begin
            if target_info.system=system_x86_64_win64 then
              begin
                SetLength(saved_standard_registers,Length(win64_saved_std_regs));
                SetLength(saved_mm_registers,Length(win64_saved_xmm_regs));

                for i:=low(win64_saved_std_regs) to high(win64_saved_std_regs) do
                  saved_standard_registers[i]:=win64_saved_std_regs[i];

                for i:=low(win64_saved_xmm_regs) to high(win64_saved_xmm_regs) do
                  saved_mm_registers[i]:=win64_saved_xmm_regs[i];
              end
            else
              begin
                SetLength(saved_standard_registers,Length(others_saved_std_regs));
                SetLength(saved_mm_registers,0);

                for i:=low(others_saved_std_regs) to high(others_saved_std_regs) do
                  saved_standard_registers[i]:=others_saved_std_regs[i];
              end;
          end;
        if assigned(current_procinfo) then
          framepointer:=getsupreg(current_procinfo.framepointer)
        else
          { in intf. wrapper code generation }
          framepointer:=RS_FRAME_POINTER_REG;
        if target_info.system=system_x86_64_win64 then
          rg[R_INTREGISTER]:=trgcpu.create(R_INTREGISTER,R_SUBWHOLE,[RS_RAX,RS_RDX,RS_RCX,RS_R8,RS_R9,RS_R10,
            RS_R11,RS_RBX,RS_RSI,RS_RDI,RS_R12,RS_R13,RS_R14,RS_R15],first_int_imreg,[framepointer])
        else
          rg[R_INTREGISTER]:=trgcpu.create(R_INTREGISTER,R_SUBWHOLE,[RS_RAX,RS_RDX,RS_RCX,RS_RSI,RS_RDI,RS_R8,
            RS_R9,RS_R10,RS_R11,RS_RBX,RS_R12,RS_R13,RS_R14,RS_R15],first_int_imreg,[framepointer]);

        rg[R_MMREGISTER]:=trgcpu.create(R_MMREGISTER,R_SUBWHOLE,[RS_XMM0,RS_XMM1,RS_XMM2,RS_XMM3,RS_XMM4,RS_XMM5,RS_XMM6,RS_XMM7,
          RS_XMM8,RS_XMM9,RS_XMM10,RS_XMM11,RS_XMM12,RS_XMM13,RS_XMM14,RS_XMM15],first_mm_imreg,[]);
        rgfpu:=Trgx86fpu.create;
      end;


    procedure tcgx86_64.g_proc_entry(list : TAsmList;parasize:longint;nostackframe:boolean);
      var
        hitem: tlinkedlistitem;
        r: integer;
        href: treference;
        templist: TAsmList;
        frame_offset: longint;
        suppress_endprologue: boolean;
      begin
        hitem:=list.last;
        { pi_has_unwind_info may already be set at this point if there are
          SEH directives in assembler body. In this case, .seh_endprologue
          is expected to be one of those directives, and not generated here. }
        suppress_endprologue:=(pi_has_unwind_info in current_procinfo.flags);
        inherited g_proc_entry(list,parasize,nostackframe);

        if not (pi_has_unwind_info in current_procinfo.flags) then
          exit;
        { Generate unwind data for x86_64-win64 }
        list.insertafter(cai_seh_directive.create_name(ash_proc,current_procinfo.procdef.mangledname),hitem);
        templist:=TAsmList.Create;

        { We need to record postive offsets from RSP; if registers are saved
          at negative offsets from RBP we need to account for it. }
        if current_procinfo.framepointer=NR_FRAME_POINTER_REG then
          frame_offset:=current_procinfo.final_localsize
        else
          frame_offset:=0;

        { There's no need to describe position of register saves precisely;
          since registers are not modified before they are saved, and saves do not
          change RSP, 'logically' all saves can happen at the end of prologue. }
        href:=current_procinfo.save_regs_ref;
        for r:=low(saved_standard_registers) to high(saved_standard_registers) do
          if saved_standard_registers[r] in rg[R_INTREGISTER].used_in_proc then
            begin
              templist.concat(cai_seh_directive.create_reg_offset(ash_savereg,
                newreg(R_INTREGISTER,saved_standard_registers[r],R_SUBWHOLE),
                href.offset+frame_offset));
              inc(href.offset,sizeof(aint));
            end;
        if uses_registers(R_MMREGISTER) then
          begin
            if (href.offset mod tcgsize2size[OS_VECTOR])<>0 then
              inc(href.offset,tcgsize2size[OS_VECTOR]-(href.offset mod tcgsize2size[OS_VECTOR]));

            for r:=low(saved_mm_registers) to high(saved_mm_registers) do
              begin
                if saved_mm_registers[r] in rg[R_MMREGISTER].used_in_proc then
                  begin
                    templist.concat(cai_seh_directive.create_reg_offset(ash_savexmm,
                      newreg(R_MMREGISTER,saved_mm_registers[r],R_SUBNONE),
                      href.offset+frame_offset));
                    inc(href.offset,tcgsize2size[OS_VECTOR]);
                  end;
              end;
          end;
        if not suppress_endprologue then
          templist.concat(cai_seh_directive.create(ash_endprologue));
        if assigned(current_procinfo.endprologue_ai) then
          current_procinfo.aktproccode.insertlistafter(current_procinfo.endprologue_ai,templist)
        else
          list.concatlist(templist);
        templist.free;
      end;


    procedure tcgx86_64.g_proc_exit(list : TAsmList;parasize:longint;nostackframe:boolean);
      var
        href : treference;
      begin
        { Release PIC register }
        if cs_create_pic in current_settings.moduleswitches then
          list.concat(tai_regalloc.dealloc(NR_PIC_OFFSET_REG,nil));

        { Prevent return address from a possible call from ending up in the epilogue }
        { (restoring registers happens before epilogue, providing necessary padding) }
        if (current_procinfo.flags*[pi_has_unwind_info,pi_do_call,pi_has_saved_regs])=[pi_has_unwind_info,pi_do_call] then
          list.concat(Taicpu.op_none(A_NOP));
        { remove stackframe }
        if not nostackframe then
          begin
            if (current_procinfo.framepointer=NR_STACK_POINTER_REG) or
               (current_procinfo.procdef.proctypeoption=potype_exceptfilter) then
              begin
                if (current_procinfo.final_localsize<>0) then
                  cg.a_op_const_reg(list,OP_ADD,OS_ADDR,current_procinfo.final_localsize,NR_STACK_POINTER_REG);
                if (current_procinfo.procdef.proctypeoption=potype_exceptfilter) then
                  list.concat(Taicpu.op_reg(A_POP,tcgsize2opsize[OS_ADDR],NR_FRAME_POINTER_REG));
              end
            else if (target_info.system=system_x86_64_win64) then
              begin
                { Comply with Win64 unwinding mechanism, which only recognizes
                  'add $constant,%rsp' and 'lea offset(FPREG),%rsp' as belonging to
                  the function epilog.
                  Neither 'leave' nor even 'mov %FPREG,%rsp' are allowed. }
                reference_reset_base(href,current_procinfo.framepointer,0,sizeof(pint));
                list.concat(Taicpu.op_ref_reg(A_LEA,tcgsize2opsize[OS_ADDR],href,NR_STACK_POINTER_REG));
                list.concat(Taicpu.op_reg(A_POP,tcgsize2opsize[OS_ADDR],current_procinfo.framepointer));
              end
            else
              list.concat(Taicpu.op_none(A_LEAVE,S_NO));
            list.concat(tai_regalloc.dealloc(NR_FRAME_POINTER_REG,nil));
          end;

        list.concat(Taicpu.Op_none(A_RET,S_NO));
        if (pi_has_unwind_info in current_procinfo.flags) then
          begin
            tx86_64procinfo(current_procinfo).dump_scopes(list);
            list.concat(cai_seh_directive.create(ash_endproc));
          end;
      end;


    procedure tcgx86_64.g_intf_wrapper(list: TAsmList; procdef: tprocdef; const labelname: string; ioffset: longint);
      var
        make_global : boolean;
        href : treference;
        sym : tasmsymbol;
        r : treference;
      begin
        if not(procdef.proctypeoption in [potype_function,potype_procedure]) then
          Internalerror(200006137);
        if not assigned(procdef.struct) or
           (procdef.procoptions*[po_classmethod, po_staticmethod,
             po_methodpointer, po_interrupt, po_iocheck]<>[]) then
          Internalerror(200006138);
        if procdef.owner.symtabletype<>ObjectSymtable then
          Internalerror(200109191);

        make_global:=false;
        if (not current_module.is_unit) or create_smartlink or
           (procdef.owner.defowner.owner.symtabletype=globalsymtable) then
          make_global:=true;

        if make_global then
          List.concat(Tai_symbol.Createname_global(labelname,AT_FUNCTION,0))
        else
          List.concat(Tai_symbol.Createname(labelname,AT_FUNCTION,0));

        { set param1 interface to self  }
        g_adjust_self_value(list,procdef,ioffset);

        if (po_virtualmethod in procdef.procoptions) and
            not is_objectpascal_helper(procdef.struct) then
          begin
            if (procdef.extnumber=$ffff) then
              Internalerror(200006139);
            { load vmt from first paramter }
            { win64 uses a different abi }
            if target_info.system=system_x86_64_win64 then
              reference_reset_base(href,NR_RCX,0,sizeof(pint))
            else
              reference_reset_base(href,NR_RDI,0,sizeof(pint));
            cg.a_load_ref_reg(list,OS_ADDR,OS_ADDR,href,NR_RAX);
            { jmp *vmtoffs(%eax) ; method offs }
            reference_reset_base(href,NR_RAX,tobjectdef(procdef.struct).vmtmethodoffset(procdef.extnumber),sizeof(pint));
            list.concat(taicpu.op_ref_reg(A_MOV,S_Q,href,NR_RAX));
            list.concat(taicpu.op_reg(A_JMP,S_Q,NR_RAX));
          end
        else
          begin
            sym:=current_asmdata.RefAsmSymbol(procdef.mangledname);
            reference_reset_symbol(r,sym,0,sizeof(pint));
            if (cs_create_pic in current_settings.moduleswitches) and
               { darwin/x86_64's assembler doesn't want @PLT after call symbols }
               (target_info.system<>system_x86_64_darwin) then
              r.refaddr:=addr_pic
            else
              r.refaddr:=addr_full;

            list.concat(taicpu.op_ref(A_JMP,S_NO,r));
          end;

        List.concat(Tai_symbol_end.Createname(labelname));
      end;

    procedure tcgx86_64.g_local_unwind(list: TAsmList; l: TAsmLabel);
      var
        para1,para2: tcgpara;
        href:treference;
      begin
        if (target_info.system<>system_x86_64_win64) then
          begin
            inherited g_local_unwind(list,l);
            exit;
          end;
        para1.init;
        para2.init;
        paramanager.getintparaloc(pocall_default,1,para1);
        paramanager.getintparaloc(pocall_default,2,para2);
        reference_reset_symbol(href,l,0,1);
        { TODO: using RSP is correct only while the stack is fixed!!
          (true now, but will change if/when allocating from stack is implemented) }
        a_load_reg_cgpara(list,OS_ADDR,NR_STACK_POINTER_REG,para1);
        a_loadaddr_ref_cgpara(list,href,para2);
        paramanager.freecgpara(list,para2);
        paramanager.freecgpara(list,para1);
        g_call(current_asmdata.CurrAsmList,'_FPC_local_unwind');
        para2.done;
        para1.done;
      end;

    procedure tcgx86_64.a_loadmm_intreg_reg(list: TAsmList; fromsize, tosize : tcgsize; intreg, mmreg: tregister; shuffle: pmmshuffle);
      var
        opc: tasmop;
      begin
        { this code can only be used to transfer raw data, not to perform
          conversions }
        if (tcgsize2size[fromsize]<>tcgsize2size[tosize]) or
           not(tosize in [OS_F32,OS_F64,OS_M64]) then
          internalerror(2009112505);
        case fromsize of
          OS_32,OS_S32:
            opc:=A_MOVD;
          OS_64,OS_S64:
            opc:=A_MOVQ;
          else
            internalerror(2009112506);
        end;
        if assigned(shuffle) and
           not shufflescalar(shuffle) then
          internalerror(2009112517);
        list.concat(taicpu.op_reg_reg(opc,S_NO,intreg,mmreg));
      end;


    procedure tcgx86_64.a_loadmm_reg_intreg(list: TAsmList; fromsize, tosize : tcgsize; mmreg, intreg: tregister;shuffle : pmmshuffle);
      var
        opc: tasmop;
      begin
        { this code can only be used to transfer raw data, not to perform
          conversions }
        if (tcgsize2size[fromsize]<>tcgsize2size[tosize]) or
           not (fromsize in [OS_F32,OS_F64,OS_M64]) then
          internalerror(2009112507);
        case tosize of
          OS_32,OS_S32:
            opc:=A_MOVD;
          OS_64,OS_S64:
            opc:=A_MOVQ;
          else
            internalerror(2009112408);
        end;
        if assigned(shuffle) and
           not shufflescalar(shuffle) then
          internalerror(2009112515);
        list.concat(taicpu.op_reg_reg(opc,S_NO,mmreg,intreg));
      end;


    procedure create_codegen;
      begin
        cg:=tcgx86_64.create;
      end;

end.
