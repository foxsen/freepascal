{
    Copyright (c) 2011 by Free Pascal development team

    Generate Win64-specific exception handling code

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
unit nx64flw;

{$i fpcdefs.inc}

interface

  uses
    node,nflw,ncgflw,psub;

  type
    tx64raisenode=class(tcgraisenode)
      procedure pass_generate_code;override;
    end;

    tx64onnode=class(tcgonnode)
      procedure pass_generate_code;override;
    end;

    tx64tryexceptnode=class(tcgtryexceptnode)
      procedure pass_generate_code;override;
    end;

    tx64tryfinallynode=class(tcgtryfinallynode)
      finalizepi: tcgprocinfo;
      constructor create(l,r:TNode);override;
      constructor create_implicit(l,r,_t1:TNode);override;
      function simplify(forinline: boolean): tnode;override;
      procedure pass_generate_code;override;
    end;

implementation

  uses
    cutils,globtype,globals,verbose,systems,
    nbas,ncal,nmem,nutils,
    symconst,symbase,symtable,symsym,symdef,
    cgbase,cgobj,cgcpu,cgutils,tgobj,
    cpubase,htypechk,
    parabase,paramgr,pdecsub,pass_1,pass_2,ncgutil,cga,
    aasmbase,aasmtai,aasmdata,aasmcpu,procinfo,cpupi;

  var
    endexceptlabel: tasmlabel;


{ tx64raisenode }

procedure tx64raisenode.pass_generate_code;
  begin
    { difference from generic code is that address stack is not popped on reraise }
    if (target_info.system<>system_x86_64_win64) or assigned(left) then
      inherited pass_generate_code
    else
      cg.g_call(current_asmdata.CurrAsmList,'FPC_RERAISE');
  end;

{ tx64onnode }

procedure tx64onnode.pass_generate_code;
  var
    oldflowcontrol : tflowcontrol;
    exceptvarsym : tlocalvarsym;
  begin
    if (target_info.system<>system_x86_64_win64) then
      begin
        inherited pass_generate_code;
        exit;
      end;

    location_reset(location,LOC_VOID,OS_NO);

    oldflowcontrol:=flowcontrol;
    flowcontrol:=[fc_inflowcontrol];

    { RTL will put exceptobject into RAX when jumping here }
    cg.a_reg_alloc(current_asmdata.CurrAsmList,NR_FUNCTION_RESULT_REG);

    { Retrieve exception variable }
    if assigned(excepTSymtable) then
      exceptvarsym:=tlocalvarsym(excepTSymtable.SymList[0])
    else
      exceptvarsym:=nil;

    if assigned(exceptvarsym) then
      begin
        exceptvarsym.localloc.loc:=LOC_REFERENCE;
        exceptvarsym.localloc.size:=OS_ADDR;
        tg.GetLocal(current_asmdata.CurrAsmList,sizeof(pint),voidpointertype,exceptvarsym.localloc.reference);
        cg.a_load_reg_ref(current_asmdata.CurrAsmList,OS_ADDR,OS_ADDR,NR_FUNCTION_RESULT_REG,exceptvarsym.localloc.reference);
      end;
    cg.a_reg_dealloc(current_asmdata.CurrAsmList,NR_FUNCTION_RESULT_REG);

    if assigned(right) then
      secondpass(right);

    { deallocate exception symbol }
    if assigned(exceptvarsym) then
      begin
        tg.UngetLocal(current_asmdata.CurrAsmList,exceptvarsym.localloc.reference);
        exceptvarsym.localloc.loc:=LOC_INVALID;
      end;
    cg.g_call(current_asmdata.CurrAsmList,'FPC_DONEEXCEPTION');
    cg.a_jmp_always(current_asmdata.CurrAsmList,endexceptlabel);

    flowcontrol:=oldflowcontrol+(flowcontrol-[fc_inflowcontrol]);
  end;

{ tx64tryfinallynode }
var
  seq: longint=0;


function create_pd: tprocdef;
  var
    st:TSymTable;
    checkstack: psymtablestackitem;
    sym:tprocsym;
  begin
    { get actual procedure symtable (skip withsymtables, etc.) }
    st:=nil;
    checkstack:=symtablestack.stack;
    while assigned(checkstack) do
      begin
        st:=checkstack^.symtable;
          if st.symtabletype in [staticsymtable,globalsymtable,localsymtable] then
            break;
          checkstack:=checkstack^.next;
      end;
    { Create a nested procedure, even from main_program_level. }
    result:=tprocdef.create(max(normal_function_level,st.symtablelevel)+1);
    result.struct:=current_procinfo.procdef.struct;
    result.proctypeoption:=potype_exceptfilter;
    handle_calling_convention(result);
    sym:=tprocsym.create('$fin$'+tostr(seq));
    st.insert(sym);
    inc(seq);

    result.procsym:=sym;
    proc_add_definition(result);
    result.forwarddef:=false;
    result.aliasnames.insert(result.mangledname);
    alloc_proc_symbol(result);
  end;

function reset_regvars(var n: tnode; arg: pointer): foreachnoderesult;
  begin
    case n.nodetype of
      temprefn:
        make_not_regable(n,[]);
      calln:
        include(tprocinfo(arg).flags,pi_do_call);
    end;
    result:=fen_true;
  end;

function copy_parasize(var n: tnode; arg: pointer): foreachnoderesult;
  begin
    case n.nodetype of
      calln:
        tcgprocinfo(arg).allocate_push_parasize(tcallnode(n).pushed_parasize);
    end;
    result:=fen_true;
  end;

constructor tx64tryfinallynode.create(l, r: TNode);
  begin
    inherited create(l,r);
    if (target_info.system<>system_x86_64_win64) then
      exit;
    finalizepi:=tcgprocinfo(cprocinfo.create(current_procinfo));
    finalizepi.force_nested;
    finalizepi.procdef:=create_pd;
    finalizepi.entrypos:=r.fileinfo;
    finalizepi.entryswitches:=r.localswitches;
    finalizepi.exitpos:=current_filepos; // last_endtoken_pos?
    finalizepi.exitswitches:=current_settings.localswitches;
    { Regvar optimization for symbols is suppressed when using exceptions, but
      temps may be still placed into registers. This must be fixed. }
    foreachnodestatic(r,@reset_regvars,finalizepi);
  end;

constructor tx64tryfinallynode.create_implicit(l, r, _t1: TNode);
  begin
    inherited create_implicit(l, r, _t1);
    if (target_info.system<>system_x86_64_win64) then
      exit;
    finalizepi:=tcgprocinfo(cprocinfo.create(current_procinfo));
    finalizepi.force_nested;
    finalizepi.procdef:=create_pd;

    finalizepi.entrypos:=current_filepos;
    finalizepi.exitpos:=current_filepos; // last_endtoken_pos?
    finalizepi.entryswitches:=r.localswitches;
    finalizepi.exitswitches:=current_settings.localswitches;
    include(finalizepi.flags,pi_do_call);
    finalizepi.allocate_push_parasize(32);
  end;

function tx64tryfinallynode.simplify(forinline: boolean): tnode;
  begin
    result:=inherited simplify(forinline);
    if (target_info.system<>system_x86_64_win64) then
      exit;
    if (result=nil) then
      begin
        finalizepi.code:=right;
        foreachnodestatic(right,@copy_parasize,finalizepi);
        right:=ccallnode.create(nil,tprocsym(finalizepi.procdef.procsym),nil,nil,[]);
        firstpass(right);
        { For implicit frames, no actual code is available at this time,
          it is added later in assembler form. So store the nested procinfo
          for later use. }
        if implicitframe then
          begin
            current_procinfo.finalize_procinfo:=finalizepi;
            { don't leave dangling pointer }
            tcgprocinfo(current_procinfo).final_asmnode:=nil;
          end;
      end;
  end;

procedure emit_nop;
  var
    dummy: TAsmLabel;
  begin
    { To avoid optimizing away the whole thing, prepend a jumplabel with increased refcount }
    current_asmdata.getjumplabel(dummy);
    dummy.increfs;
    cg.a_label(current_asmdata.CurrAsmList,dummy);
    current_asmdata.CurrAsmList.concat(Taicpu.op_none(A_NOP,S_NO));
  end;

procedure tx64tryfinallynode.pass_generate_code;
  var
    trylabel,
    endtrylabel,
    finallylabel,
    endfinallylabel,
    oldexitlabel: tasmlabel;
    oldflowcontrol: tflowcontrol;
    catch_frame: boolean;
  begin
    if (target_info.system<>system_x86_64_win64) then
      begin
        inherited pass_generate_code;
        exit;
      end;

    location_reset(location,LOC_VOID,OS_NO);

    { Do not generate a frame that catches exceptions if the only action
      would be reraising it. Doing so is extremely inefficient with SEH
      (in contrast with setjmp/longjmp exception handling) }
    catch_frame:=implicitframe and ((not has_no_code(t1)) or
      (current_procinfo.procdef.proccalloption=pocall_safecall));

    oldflowcontrol:=flowcontrol;
    flowcontrol:=[fc_inflowcontrol];

    current_asmdata.getjumplabel(trylabel);
    current_asmdata.getjumplabel(endtrylabel);
    current_asmdata.getjumplabel(finallylabel);
    current_asmdata.getjumplabel(endfinallylabel);
    oldexitlabel:=current_procinfo.CurrExitLabel;
    if implicitframe then
      current_procinfo.CurrExitLabel:=finallylabel;

    { Start of scope }
    { Padding with NOP is necessary here because exceptions in called
      procedures are seen at the next instruction, while CPU/OS exceptions
      like AV are seen at the current instruction.

      So in the following code

      raise_some_exception;        //(a)
      try
        pchar(nil)^:='0';          //(b)
        ...

      without NOP, exceptions (a) and (b) will be seen at the same address
      and fall into the same scope. However they should be seen in different scopes.
    }

    emit_nop;
    cg.a_label(current_asmdata.CurrAsmList,trylabel);

    { try code }
    if assigned(left) then
      begin
        { fc_unwind tells exit/continue/break statements to emit special
          unwind code instead of just JMP }
        if not implicitframe then
          include(flowcontrol,fc_unwind);
        secondpass(left);
        exclude(flowcontrol,fc_unwind);
        if codegenerror then
          exit;
      end;

    { If the immediately preceding instruction is CALL,
      its return address must not end up outside the scope, so pad with NOP. }
    if catch_frame then
      cg.a_jmp_always(current_asmdata.CurrAsmList,finallylabel)
    else
      emit_nop;

    cg.a_label(current_asmdata.CurrAsmList,endtrylabel);

    { Handle the except block first, so endtrylabel serves both
      as end of scope and as unwind target. This way it is possible to
      encode everything into a single scope record. }
    if catch_frame then
      begin
        flowcontrol:=[fc_inflowcontrol];
        secondpass(t1);
        { note 1: this is not a 'finally' block, no flow restrictions apply
          note 2: it contains autogenerated sequential code, flow away is impossible }
        if flowcontrol<>[fc_inflowcontrol] then
          CGMessage(cg_e_control_flow_outside_finally);
        if codegenerror then
          exit;

        if (current_procinfo.procdef.proccalloption=pocall_safecall) then
          begin
            handle_safecall_exception;
            cg.a_jmp_always(current_asmdata.CurrAsmList,endfinallylabel);
          end
        else
          cg.a_call_name(current_asmdata.CurrAsmList,'FPC_RERAISE_IMPLICIT',false);
      end;

    flowcontrol:=[fc_inflowcontrol];
    cg.a_label(current_asmdata.CurrAsmList,finallylabel);
    { generate finally code as a separate procedure }
    if not implicitframe then
      tcgprocinfo(current_procinfo).generate_exceptfilter(finalizepi);
    { right is a call to finalizer procedure }
    secondpass(right);

    if codegenerror then
      exit;

    { normal exit from safecall proc must zero the result register }
    if implicitframe and (current_procinfo.procdef.proccalloption=pocall_safecall) then
      cg.a_load_const_reg(current_asmdata.CurrAsmList,OS_INT,0,NR_FUNCTION_RESULT_REG);

    cg.a_label(current_asmdata.CurrAsmList,endfinallylabel);

    { generate the scope record in .xdata }
    tx86_64procinfo(current_procinfo).add_finally_scope(trylabel,endtrylabel,
      current_asmdata.RefAsmSymbol(finalizepi.procdef.mangledname),catch_frame);

    if implicitframe then
      current_procinfo.CurrExitLabel:=oldexitlabel;
    flowcontrol:=oldflowcontrol;
  end;

{ tx64tryexceptnode }

procedure tx64tryexceptnode.pass_generate_code;
  var
    trylabel,
    exceptlabel,oldendexceptlabel,
    lastonlabel,
    exitexceptlabel,
    continueexceptlabel,
    breakexceptlabel,
    oldCurrExitLabel,
    oldContinueLabel,
    oldBreakLabel : tasmlabel;
    onlabel,
    filterlabel: tasmlabel;
    oldflowcontrol,tryflowcontrol,
    exceptflowcontrol : tflowcontrol;
    hnode : tnode;
    hlist : tasmlist;
    onnodecount : tai_const;
  label
    errorexit;
  begin
    if (target_info.system<>system_x86_64_win64) then
      begin
        inherited pass_generate_code;
        exit;
      end;
    location_reset(location,LOC_VOID,OS_NO);

    oldflowcontrol:=flowcontrol;
    flowcontrol:=[fc_inflowcontrol];
    { this can be called recursivly }
    oldBreakLabel:=nil;
    oldContinueLabel:=nil;
    oldendexceptlabel:=endexceptlabel;

    { save the old labels for control flow statements }
    oldCurrExitLabel:=current_procinfo.CurrExitLabel;
    current_asmdata.getjumplabel(exitexceptlabel);
    if assigned(current_procinfo.CurrBreakLabel) then
      begin
        oldContinueLabel:=current_procinfo.CurrContinueLabel;
        oldBreakLabel:=current_procinfo.CurrBreakLabel;
        current_asmdata.getjumplabel(breakexceptlabel);
        current_asmdata.getjumplabel(continueexceptlabel);
      end;

    current_asmdata.getjumplabel(exceptlabel);
    current_asmdata.getjumplabel(endexceptlabel);
    current_asmdata.getjumplabel(lastonlabel);
    filterlabel:=nil;

    { start of scope }
    current_asmdata.getjumplabel(trylabel);
    emit_nop;
    cg.a_label(current_asmdata.CurrAsmList,trylabel);

    { control flow in try block needs no special handling,
      just make sure that target labels are outside the scope }
    secondpass(left);
    tryflowcontrol:=flowcontrol;
    if codegenerror then
      goto errorexit;

    { jump over except handlers }
    cg.a_jmp_always(current_asmdata.CurrAsmList,endexceptlabel);

    { end of scope }
    cg.a_label(current_asmdata.CurrAsmList,exceptlabel);

    { set control flow labels for the except block }
    { and the on statements                        }
    current_procinfo.CurrExitLabel:=exitexceptlabel;
    if assigned(oldBreakLabel) then
      begin
        current_procinfo.CurrContinueLabel:=continueexceptlabel;
        current_procinfo.CurrBreakLabel:=breakexceptlabel;
      end;

    flowcontrol:=[fc_inflowcontrol];
    { on statements }
    if assigned(right) then
      begin
        { emit filter table to a temporary asmlist }
        hlist:=TAsmList.Create;
        current_asmdata.getdatalabel(filterlabel);
        new_section(hlist,sec_rodata_norel,filterlabel.name,4);
        cg.a_label(hlist,filterlabel);
        onnodecount:=tai_const.create_32bit(0);
        hlist.concat(onnodecount);

        hnode:=right;
        while assigned(hnode) do
          begin
            if hnode.nodetype<>onn then
              InternalError(2011103101);
            { TODO: make it done without using global label }
            current_asmdata.getglobaljumplabel(onlabel);
            hlist.concat(tai_const.create_rva_sym(current_asmdata.RefAsmSymbol(tonnode(hnode).excepttype.vmt_mangledname)));
            hlist.concat(tai_const.create_rva_sym(onlabel));
            cg.a_label(current_asmdata.CurrAsmList,onlabel);
            secondpass(hnode);
            inc(onnodecount.value);
            hnode:=tonnode(hnode).left;
          end;
        { add 'else' node to the filter list, too }
        if assigned(t1) then
          begin
            hlist.concat(tai_const.create_32bit(-1));
            hlist.concat(tai_const.create_rva_sym(lastonlabel));
            inc(onnodecount.value);
          end;
        { now move filter table to permanent list all at once }
        maybe_new_object_file(current_asmdata.asmlists[al_typedconsts]);
        current_asmdata.asmlists[al_typedconsts].concatlist(hlist);
        hlist.free;
      end;

    cg.a_label(current_asmdata.CurrAsmList,lastonlabel);
    if assigned(t1) then
      begin
        { here we don't have to reset flowcontrol           }
        { the default and on flowcontrols are handled equal }
        secondpass(t1);
        cg.g_call(current_asmdata.CurrAsmList,'FPC_DONEEXCEPTION');
        if (flowcontrol*[fc_exit,fc_break,fc_continue]<>[]) then
          cg.a_jmp_always(current_asmdata.CurrAsmList,endexceptlabel);
      end;
    exceptflowcontrol:=flowcontrol;

    if fc_exit in exceptflowcontrol then
      begin
        { do some magic for exit in the try block }
        cg.a_label(current_asmdata.CurrAsmList,exitexceptlabel);
        cg.g_call(current_asmdata.CurrAsmList,'FPC_DONEEXCEPTION');
        cg.a_jmp_always(current_asmdata.CurrAsmList,oldCurrExitLabel);
      end;

    if fc_break in exceptflowcontrol then
      begin
        cg.a_label(current_asmdata.CurrAsmList,breakexceptlabel);
        cg.g_call(current_asmdata.CurrAsmList,'FPC_DONEEXCEPTION');
        cg.a_jmp_always(current_asmdata.CurrAsmList,oldBreakLabel);
      end;

    if fc_continue in exceptflowcontrol then
      begin
        cg.a_label(current_asmdata.CurrAsmList,continueexceptlabel);
        cg.g_call(current_asmdata.CurrAsmList,'FPC_DONEEXCEPTION');
        cg.a_jmp_always(current_asmdata.CurrAsmList,oldContinueLabel);
      end;

    emit_nop;
    cg.a_label(current_asmdata.CurrAsmList,endexceptlabel);
    tx86_64procinfo(current_procinfo).add_except_scope(trylabel,exceptlabel,endexceptlabel,filterlabel);

errorexit:
    { restore all saved labels }
    endexceptlabel:=oldendexceptlabel;

    { restore the control flow labels }
    current_procinfo.CurrExitLabel:=oldCurrExitLabel;
    if assigned(oldBreakLabel) then
      begin
        current_procinfo.CurrContinueLabel:=oldContinueLabel;
        current_procinfo.CurrBreakLabel:=oldBreakLabel;
      end;

    { return all used control flow statements }
    flowcontrol:=oldflowcontrol+(exceptflowcontrol +
      tryflowcontrol - [fc_inflowcontrol]);
  end;

initialization
  craisenode:=tx64raisenode;
  connode:=tx64onnode;
  ctryexceptnode:=tx64tryexceptnode;
  ctryfinallynode:=tx64tryfinallynode;
end.

