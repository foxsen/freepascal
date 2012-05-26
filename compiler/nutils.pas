{
    Copyright (c) 1998-2002 by Florian Klaempfl

    Type checking and register allocation for inline nodes

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
unit nutils;

{$i fpcdefs.inc}

interface

  uses
    globtype,constexp,
    symtype,symsym,symbase,symtable,
    node;

  const
    NODE_COMPLEXITY_INF = 255;

  type
    { resultdef of functions that process on all nodes in a (sub)tree }
    foreachnoderesult = (
      { false, continue recursion }
      fen_false,
      { false, stop recursion }
      fen_norecurse_false,
      { true, continue recursion }
      fen_true,
      { true, stop recursion }
      fen_norecurse_true
    );

    tforeachprocmethod = (pm_preprocess,pm_postprocess,
                          pm_postandagain);

    foreachnodefunction = function(var n: tnode; arg: pointer): foreachnoderesult of object;
    staticforeachnodefunction = function(var n: tnode; arg: pointer): foreachnoderesult;

    function foreachnode(var n: tnode; f: foreachnodefunction; arg: pointer): boolean;
    function foreachnode(procmethod : tforeachprocmethod; var n: tnode; f: foreachnodefunction; arg: pointer): boolean;
    function foreachnodestatic(var n: tnode; f: staticforeachnodefunction; arg: pointer): boolean;
    function foreachnodestatic(procmethod : tforeachprocmethod; var n: tnode; f: staticforeachnodefunction; arg: pointer): boolean;

    { checks if the given node tree contains only nodes of the given type,
      if this isn't the case, an ie is thrown
    }
    procedure checktreenodetypes(n : tnode;typeset : tnodetypeset);

    procedure load_procvar_from_calln(var p1:tnode);
    function maybe_call_procvar(var p1:tnode;tponly:boolean):boolean;
    function load_high_value_node(vs:tparavarsym):tnode;
    function load_self_node:tnode;
    function load_result_node:tnode;
    function load_self_pointer_node:tnode;
    function load_vmt_pointer_node:tnode;
    function is_self_node(p:tnode):boolean;

    function node_complexity(p: tnode): cardinal;
    function node_resources_fpu(p: tnode): cardinal;
    procedure node_tree_set_filepos(var n:tnode;const filepos:tfileposinfo);

    { tries to simplify the given node after inlining }
    procedure doinlinesimplify(var n : tnode);
    { creates an ordinal constant, optionally based on the result from a
      simplify operation: normally the type is the smallest integer type
      that can hold the value, but when inlining the "def" will be used instead,
      which was determined during an earlier typecheck pass (because the value
      may e.g. be a parameter to a call, which needs to be of the declared
      parameter type) }
    function create_simplified_ord_const(value: tconstexprint; def: tdef; forinline: boolean): tnode;

    { returns true if n is only a tree of administrative nodes
      containing no code }
    function has_no_code(n : tnode) : boolean;

    function getpropaccesslist(propsym:tpropertysym; pap:tpropaccesslisttypes;out propaccesslist:tpropaccesslist):boolean;
    procedure propaccesslist_to_node(var p1:tnode;st:TSymtable;pl:tpropaccesslist);
    function node_to_propaccesslist(p1:tnode):tpropaccesslist;

    { checks whether sym is a static field and if so, translates the access
      to the appropriate node tree }
    function handle_staticfield_access(sym: tsym; nested: boolean; var p1: tnode): boolean;

    { returns true if n is an array element access of a bitpacked array with
      elements of the which the vitsize mod 8 <> 0, or if is a field access
      with bitsize mod 8 <> 0 or bitoffset mod 8 <> 0 of an element in a
      bitpacked structure }
    function is_bitpacked_access(n: tnode): boolean;

    { creates a load of field 'fieldname' in the record/class/...
      represented by n }
    function genloadfield(n: tnode; const fieldname: string): tnode;

    { returns true, if the tree given might have side effects }
    function might_have_sideeffects(n : tnode) : boolean;

    { count the number of nodes in the node tree,
      rough estimation how large the tree "node" is }
    function node_count(node : tnode) : dword;

implementation

    uses
      cutils,verbose,globals,
      symconst,symdef,
      defutil,defcmp,
      nbas,ncon,ncnv,nld,nflw,nset,ncal,nadd,nmem,ninl,
      cpubase,cgbase,procinfo,
      pass_1;

  function foreachnode(procmethod : tforeachprocmethod;var n: tnode; f: foreachnodefunction; arg: pointer): boolean;

    function process_children(res : boolean) : boolean;
      var
        i: longint;
      begin
        result:=res;
        case n.nodetype of
        asn:
          if assigned(tasnode(n).call) then
            begin
              result := foreachnode(procmethod,tasnode(n).call,f,arg);
              exit
            end;
          calln:
            begin
              result := foreachnode(procmethod,tnode(tcallnode(n).callinitblock),f,arg) or result;
              result := foreachnode(procmethod,tcallnode(n).methodpointer,f,arg) or result;
              result := foreachnode(procmethod,tcallnode(n).funcretnode,f,arg) or result;
              result := foreachnode(procmethod,tnode(tcallnode(n).callcleanupblock),f,arg) or result;
            end;
          ifn, whilerepeatn, forn, tryexceptn, tryfinallyn:
            begin
              { not in one statement, won't work because of b- }
              result := foreachnode(procmethod,tloopnode(n).t1,f,arg) or result;
              result := foreachnode(procmethod,tloopnode(n).t2,f,arg) or result;
            end;
          raisen:
            { frame tree }
            result := foreachnode(traisenode(n).third,f,arg) or result;
          tempcreaten:
            { temp. initialization code }
            if assigned(ttempcreatenode(n).tempinfo^.tempinitcode) then
              result := foreachnode(ttempcreatenode(n).tempinfo^.tempinitcode,f,arg) or result;
          casen:
            begin
              for i := 0 to tcasenode(n).blocks.count-1 do
                if assigned(tcasenode(n).blocks[i]) then
                  result := foreachnode(procmethod,pcaseblock(tcasenode(n).blocks[i])^.statement,f,arg) or result;
              result := foreachnode(procmethod,tcasenode(n).elseblock,f,arg) or result;
            end;
        end;
        if n.inheritsfrom(tbinarynode) then
          begin
            { first process the "payload" of statementnodes }
            result := foreachnode(procmethod,tbinarynode(n).left,f,arg) or result;
            result := foreachnode(procmethod,tbinarynode(n).right,f,arg) or result;
          end
        else if n.inheritsfrom(tunarynode) then
          result := foreachnode(procmethod,tunarynode(n).left,f,arg) or result;
      end;

    begin
      result := false;
      if not assigned(n) then
        exit;
      if procmethod=pm_preprocess then
        result:=process_children(result);
      case f(n,arg) of
        fen_norecurse_false:
          exit;
        fen_norecurse_true:
          begin
            result := true;
            exit;
          end;
        fen_true:
          result := true;
       { result is already false
        fen_false:
          result := false; }
      end;
      if (procmethod=pm_postprocess) or (procmethod=pm_postandagain) then
        result:=process_children(result);
      if procmethod=pm_postandagain then
        begin
          case f(n,arg) of
            fen_norecurse_false:
              exit;
            fen_norecurse_true:
              begin
                result := true;
                exit;
              end;
            fen_true:
              result := true;
          end;
        end;
    end;


    function foreachnode(var n: tnode; f: foreachnodefunction; arg: pointer): boolean;
      begin
        result:=foreachnode(pm_postprocess,n,f,arg);
      end;


  function foreachnodestatic(procmethod : tforeachprocmethod;var n: tnode; f: staticforeachnodefunction; arg: pointer): boolean;

    function process_children(res : boolean) : boolean;
      var
        i: longint;
      begin
        result:=res;
        case n.nodetype of
        asn:
          if assigned(tasnode(n).call) then
            begin
              result := foreachnodestatic(procmethod,tasnode(n).call,f,arg);
              exit
            end;
          calln:
            begin
              result := foreachnodestatic(procmethod,tnode(tcallnode(n).callinitblock),f,arg) or result;
              result := foreachnodestatic(procmethod,tcallnode(n).methodpointer,f,arg) or result;
              result := foreachnodestatic(procmethod,tcallnode(n).funcretnode,f,arg) or result;
              result := foreachnodestatic(procmethod,tnode(tcallnode(n).callcleanupblock),f,arg) or result;
            end;
          ifn, whilerepeatn, forn, tryexceptn, tryfinallyn:
            begin
              { not in one statement, won't work because of b- }
              result := foreachnodestatic(procmethod,tloopnode(n).t1,f,arg) or result;
              result := foreachnodestatic(procmethod,tloopnode(n).t2,f,arg) or result;
            end;
          raisen:
            { frame tree }
            result := foreachnodestatic(traisenode(n).third,f,arg) or result;
          tempcreaten:
            { temp. initialization code }
            if assigned(ttempcreatenode(n).tempinfo^.tempinitcode) then
              result := foreachnodestatic(ttempcreatenode(n).tempinfo^.tempinitcode,f,arg) or result;
          casen:
            begin
              for i := 0 to tcasenode(n).blocks.count-1 do
                if assigned(tcasenode(n).blocks[i]) then
                  result := foreachnodestatic(procmethod,pcaseblock(tcasenode(n).blocks[i])^.statement,f,arg) or result;
              result := foreachnodestatic(procmethod,tcasenode(n).elseblock,f,arg) or result;
            end;
        end;
        if n.inheritsfrom(tbinarynode) then
          begin
            { first process the "payload" of statementnodes }
            result := foreachnodestatic(procmethod,tbinarynode(n).left,f,arg) or result;
            result := foreachnodestatic(procmethod,tbinarynode(n).right,f,arg) or result;
          end
        else if n.inheritsfrom(tunarynode) then
          result := foreachnodestatic(procmethod,tunarynode(n).left,f,arg) or result;
      end;

    begin
      result := false;
      if not assigned(n) then
        exit;
      if procmethod=pm_preprocess then
        result:=process_children(result);
      case f(n,arg) of
        fen_norecurse_false:
          exit;
        fen_norecurse_true:
          begin
            result := true;
            exit;
          end;
        fen_true:
          result := true;
       { result is already false
        fen_false:
          result := false; }
      end;
      if (procmethod=pm_postprocess) or (procmethod=pm_postandagain) then
        result:=process_children(result);
      if procmethod=pm_postandagain then
        begin
          case f(n,arg) of
            fen_norecurse_false:
              exit;
            fen_norecurse_true:
              begin
                result := true;
                exit;
              end;
            fen_true:
              result := true;
          end;
        end;
    end;


    function foreachnodestatic(var n: tnode; f: staticforeachnodefunction; arg: pointer): boolean;
      begin
        result:=foreachnodestatic(pm_postprocess,n,f,arg);
      end;


    function do_check(var n: tnode; arg: pointer): foreachnoderesult;
      begin
        if not(n.nodetype in pnodetypeset(arg)^) then
          internalerror(200610141);
        result:=fen_true;
      end;


    procedure checktreenodetypes(n : tnode;typeset : tnodetypeset);
      begin
        foreachnodestatic(n,@do_check,@typeset);
      end;


    procedure load_procvar_from_calln(var p1:tnode);
      var
        p2 : tnode;
      begin
        if p1.nodetype<>calln then
          internalerror(200212251);
        { was it a procvar, then we simply remove the calln and
          reuse the right }
        if assigned(tcallnode(p1).right) then
          begin
            p2:=tcallnode(p1).right;
            tcallnode(p1).right:=nil;
          end
        else
          begin
            p2:=cloadnode.create_procvar(tcallnode(p1).symtableprocentry,
               tprocdef(tcallnode(p1).procdefinition),tcallnode(p1).symtableproc);
            { when the methodpointer is typen we've something like:
              tobject.create. Then only the address is needed of the
              method without a self pointer }
            if assigned(tcallnode(p1).methodpointer) and
               (tcallnode(p1).methodpointer.nodetype<>typen) then
              tloadnode(p2).set_mp(tcallnode(p1).methodpointer.getcopy);
          end;
        typecheckpass(p2);
        p1.free;
        p1:=p2;
      end;


    function maybe_call_procvar(var p1:tnode;tponly:boolean):boolean;
      var
        hp : tnode;
      begin
        result:=false;
        if (p1.resultdef.typ<>procvardef) or
           (tponly and
            not(m_tp_procvar in current_settings.modeswitches)) then
          exit;
        { ignore vecn,subscriptn }
        hp:=p1;
        repeat
          case hp.nodetype of
            vecn,
            derefn,
            typeconvn,
            subscriptn :
              hp:=tunarynode(hp).left;
            else
              break;
          end;
        until false;
        { a tempref is used when it is loaded from a withsymtable }
        if (hp.nodetype in [calln,loadn,temprefn]) then
          begin
            hp:=ccallnode.create_procvar(nil,p1);
            typecheckpass(hp);
            p1:=hp;
            result:=true;
          end;
      end;


    function get_local_or_para_sym(const aname:string):tsym;
      var
        pd : tprocdef;
      begin
        result:=nil;
        { is not assigned while parsing a property }
        if not assigned(current_procinfo) then
          exit;
        { we can't use searchsym here, because the
          symtablestack is not fully setup when pass1
          is run for nested procedures }
        pd:=current_procinfo.procdef;
        repeat
          result := tsym(pd.localst.Find(aname));
          if assigned(result) then
            break;
          result := tsym(pd.parast.Find(aname));
          if assigned(result) then
            break;
          { try the parent of a nested function }
          if assigned(pd.owner.defowner) and
             (pd.owner.defowner.typ=procdef) then
            pd:=tprocdef(pd.owner.defowner)
          else
            break;
        until false;
      end;


    function load_high_value_node(vs:tparavarsym):tnode;
      var
        srsym : tsym;
      begin
        result:=nil;
        srsym:=get_high_value_sym(vs);
        if assigned(srsym) then
          begin
            result:=cloadnode.create(srsym,vs.owner);
            typecheckpass(result);
          end
        else
          CGMessage(parser_e_illegal_expression);
      end;


    function load_self_node:tnode;
      var
        srsym : tsym;
      begin
        result:=nil;

        srsym:=get_local_or_para_sym('self');
        if assigned(srsym) then
          begin
            result:=cloadnode.create(srsym,srsym.owner);
            include(tloadnode(result).loadnodeflags,loadnf_is_self);
          end
        else
          begin
            result:=cerrornode.create;
            CGMessage(parser_e_illegal_expression);
          end;
        typecheckpass(result);
      end;


    function load_result_node:tnode;
      var
        srsym : tsym;
      begin
        result:=nil;
        srsym:=get_local_or_para_sym('result');
        if assigned(srsym) then
          result:=cloadnode.create(srsym,srsym.owner)
        else
          begin
            result:=cerrornode.create;
            CGMessage(parser_e_illegal_expression);
          end;
        typecheckpass(result);
      end;


    function load_self_pointer_node:tnode;
      var
        srsym : tsym;
      begin
        result:=nil;
        srsym:=get_local_or_para_sym('self');
        if assigned(srsym) then
          begin
            result:=cloadnode.create(srsym,srsym.owner);
            include(tloadnode(result).loadnodeflags,loadnf_load_self_pointer);
          end
        else
          begin
            result:=cerrornode.create;
            CGMessage(parser_e_illegal_expression);
          end;
        typecheckpass(result);
      end;


    function load_vmt_pointer_node:tnode;
      var
        srsym : tsym;
      begin
        result:=nil;
        srsym:=get_local_or_para_sym('vmt');
        if assigned(srsym) then
          result:=cloadnode.create(srsym,srsym.owner)
        else
          begin
            result:=cerrornode.create;
            CGMessage(parser_e_illegal_expression);
          end;
        typecheckpass(result);
      end;


    function is_self_node(p:tnode):boolean;
      begin
        is_self_node:=(p.nodetype=loadn) and
                      (tloadnode(p).symtableentry.typ=paravarsym) and
                      (vo_is_self in tparavarsym(tloadnode(p).symtableentry).varoptions);
      end;


    { this function must return a very high value ("infinity") for   }
    { trees containing a call, the rest can be balanced more or less }
    { at will, probably best mainly in terms of required memory      }
    { accesses                                                       }
    function node_complexity(p: tnode): cardinal;
      var
        correction: byte;
{$ifdef ARM}
        dummy : byte;
{$endif ARM}
      begin
        result := 0;
        while assigned(p) do
          begin
            case p.nodetype of
              { floating point constants usually need loading from memory }
              realconstn,
              setconstn,
              stringconstn,
              temprefn,
              loadvmtaddrn,
              { main reason for the next one: we can't take the address of }
              { loadparentfpnode, so replacing it by a temp which is the   }
              { address of this node's location and then dereferencing     }
              { doesn't work. If changed, check whether webtbs/tw0935      }
              { still works with nodeinlining (JM)                         }
              loadparentfpn:
                begin
                  result := 1;
                  exit;
                end;
              loadn:
                begin
                  if assigned(tloadnode(p).left) then
                    inc(result,node_complexity(tloadnode(p).left));
                  { threadvars need a helper call }
                  if (tloadnode(p).symtableentry.typ=staticvarsym) and
                     (vo_is_thread_var in tstaticvarsym(tloadnode(p).symtableentry).varoptions) then
                    inc(result,5)
                  else
                    inc(result);
                  if (result >= NODE_COMPLEXITY_INF) then
                    result := NODE_COMPLEXITY_INF;
                  exit;
                end;
              subscriptn:
                begin
                  if is_implicit_pointer_object_type(tunarynode(p).left.resultdef) then
                    inc(result,2);
                  if (result = NODE_COMPLEXITY_INF) then
                    exit;
                  p := tunarynode(p).left;
                end;
              blockn,
              callparan:
                p := tunarynode(p).left;
              notn,
              derefn :
                begin
                  inc(result);
                  if (result = NODE_COMPLEXITY_INF) then
                    exit;
                  p := tunarynode(p).left;
                end;
              typeconvn:
                begin
                  { may be more complex in some cases }
                  if not(ttypeconvnode(p).convtype in [tc_equal,tc_int_2_int,tc_bool_2_bool,tc_real_2_real,tc_cord_2_pointer]) then
                    inc(result);
                  if (result = NODE_COMPLEXITY_INF) then
                    exit;
                  p := tunarynode(p).left;
                end;
              vecn,
              statementn:
                begin
                  inc(result,node_complexity(tbinarynode(p).left));
                  if (result >= NODE_COMPLEXITY_INF) then
                    begin
                      result := NODE_COMPLEXITY_INF;
                      exit;
                    end;
                  p := tbinarynode(p).right;
                end;
              addn,subn,orn,andn,xorn,muln,divn,modn,symdifn,
              shln,shrn,
              equaln,unequaln,gtn,gten,ltn,lten,
              assignn:
                begin
{$ifdef CPU64BITALU}
                  correction:=1;
{$else CPU64BITALU}
                  correction:=2;
{$endif CPU64BITALU}
                  inc(result,node_complexity(tbinarynode(p).left)+1*correction);
                  if (p.nodetype in [muln,divn,modn]) then
                    inc(result,5*correction*correction);
                  if (result >= NODE_COMPLEXITY_INF) then
                    begin
                      result := NODE_COMPLEXITY_INF;
                      exit;
                    end;
                  p := tbinarynode(p).right;
                end;
              ordconstn:
                begin
{$ifdef ARM}
                  if not(is_shifter_const(tordconstnode(p).value.svalue,dummy)) then
                    result:=2;
{$endif ARM}
                  exit;
                end;
              tempcreaten,
              tempdeleten,
              pointerconstn,
              nothingn,
              niln:
                exit;
              inlinen:
                begin
                  { this code assumes that the inline node has   }
                  { already been firstpassed, and consequently   }
                  { that inline nodes which are transformed into }
                  { calls already have been transformed          }
                  case tinlinenode(p).inlinenumber of
                    in_lo_qword,
                    in_hi_qword,
                    in_lo_long,
                    in_hi_long,
                    in_lo_word,
                    in_hi_word,
                    in_length_x,
                    in_assigned_x,
                    in_pred_x,
                    in_succ_x,
                    in_round_real,
                    in_trunc_real,
                    in_int_real,
                    in_frac_real,
                    in_cos_real,
                    in_sin_real,
                    in_arctan_real,
                    in_pi_real,
                    in_abs_real,
                    in_sqr_real,
                    in_sqrt_real,
                    in_ln_real,
                    in_unaligned_x,
                    in_prefetch_var:
                      begin
                        inc(result);
                        p:=tunarynode(p).left;
                      end;
                    in_abs_long:
                      begin
                        inc(result,3);
                        if (result >= NODE_COMPLEXITY_INF) then
                          begin
                            result:=NODE_COMPLEXITY_INF;
                            exit;
                          end;
                        p:=tunarynode(p).left;
                      end;
                    in_sizeof_x,
                    in_typeof_x:
                      begin
                        inc(result);
                        if (tinlinenode(p).left.nodetype<>typen) then
                          { get instance vmt }
                          p:=tunarynode(p).left
                        else
                          { type vmt = global symbol, result is }
                          { already increased above             }
                          exit;
                      end;
          {$ifdef SUPPORT_MMX}
                    in_mmx_pcmpeqb..in_mmx_pcmpgtw,
          {$endif SUPPORT_MMX}
                    { load from global symbol }
                    in_typeinfo_x,
                    { load frame pointer }
                    in_get_frame,
                    in_get_caller_frame,
                    in_get_caller_addr:
                      begin
                        inc(result);
                        exit;
                      end;

                    in_inc_x,
                    in_dec_x,
                    in_include_x_y,
                    in_exclude_x_y,
                    in_assert_x_y :
                      begin
                        { operation (add, sub, or, and }
                        inc(result);
                        { left expression }
                        inc(result,node_complexity(tcallparanode(tunarynode(p).left).left));
                        if (result >= NODE_COMPLEXITY_INF) then
                          begin
                            result := NODE_COMPLEXITY_INF;
                            exit;
                          end;
                        p:=tcallparanode(tunarynode(p).left).right;
                        if assigned(p) then
                          p:=tcallparanode(p).left;
                      end;
                    else
                      begin
                        result := NODE_COMPLEXITY_INF;
                        exit;
                      end;
                  end;

                end;
              else
                begin
                  result := NODE_COMPLEXITY_INF;
                  exit;
                end;
            end;
        end;
      end;


    { this function returns an indication how much fpu registers
      will be required.
      Note: The algorithms need to be pessimistic to prevent a
      fpu stack overflow on i386 }
    function node_resources_fpu(p: tnode): cardinal;
      var
        res1,res2,res3 : cardinal;
      begin
        result:=0;
        res1:=0;
        res2:=0;
        res3:=0;
        if p.inheritsfrom(tunarynode) then
          begin
            if assigned(tunarynode(p).left) then
              res1:=node_resources_fpu(tunarynode(p).left);
            if p.inheritsfrom(tbinarynode) then
              begin
                if assigned(tbinarynode(p).right) then
                  res2:=node_resources_fpu(tbinarynode(p).right);
                if p.inheritsfrom(ttertiarynode) and assigned(ttertiarynode(p).third) then
                  res3:=node_resources_fpu(ttertiarynode(p).third)
              end;
          end;
        result:=max(max(res1,res2),res3);
        case p.nodetype of
          calln:
            { it could be a recursive call, so we never really know the number of used fpu registers }
            result:=maxfpuregs;
          realconstn,
          typeconvn,
          loadn :
            begin
              if p.expectloc in [LOC_CFPUREGISTER,LOC_FPUREGISTER] then
                result:=max(result,1);
            end;
          assignn,
          addn,subn,muln,slashn,
          equaln,unequaln,gtn,gten,ltn,lten :
            begin
              if (tbinarynode(p).left.expectloc in [LOC_CFPUREGISTER,LOC_FPUREGISTER]) or
                 (tbinarynode(p).right.expectloc in [LOC_CFPUREGISTER,LOC_FPUREGISTER])then
                result:=max(result,2);
              if(p.expectloc in [LOC_CFPUREGISTER,LOC_FPUREGISTER]) then
                inc(result);
            end;
        end;
      end;


    function setnodefilepos(var n: tnode; arg: pointer): foreachnoderesult;
      begin
        result:=fen_true;
        n.fileinfo:=pfileposinfo(arg)^;
      end;


    procedure node_tree_set_filepos(var n:tnode;const filepos:tfileposinfo);
      begin
        foreachnodestatic(n,@setnodefilepos,@filepos);
      end;


    function callsimplify(var n: tnode; arg: pointer): foreachnoderesult;
      var
        hn : tnode;
        treechanged : ^boolean;
      begin
        result:=fen_false;
        if n.inheritsfrom(tloopnode) and
           not (lnf_simplify_processing in tloopnode(n).loopflags) then
          begin
            // Try to simplify condition
            doinlinesimplify(tloopnode(n).left);
            // call directly second part below,
            // which might change the loopnode into
            // something else if the conditino is a constant node
            include(tloopnode(n).loopflags,lnf_simplify_processing);
            callsimplify(n,arg);
            // Be careful, n might have change node type
            if n.inheritsfrom(tloopnode) then
              exclude(tloopnode(n).loopflags,lnf_simplify_processing);
          end
        else
          begin
            hn:=n.simplify(true);
            if assigned(hn) then
              begin
                treechanged := arg;
                if assigned(treechanged) then
                  treechanged^:=true
                else
                  internalerror (201008181);
                n.free;
                n:=hn;
                typecheckpass(n);
              end;
          end;
      end;


    { tries to simplify the given node calling the simplify method recursively }
    procedure doinlinesimplify(var n : tnode);
      var
        treechanged : boolean;
      begin
        // Optimize if code first
        repeat
          treechanged:=false;
          foreachnodestatic(pm_postandagain,n,@callsimplify,@treechanged);
        until not(treechanged);
      end;


    function create_simplified_ord_const(value: tconstexprint; def: tdef; forinline: boolean): tnode;
      begin
        if not forinline then
          result:=genintconstnode(value)
        else
          result:=cordconstnode.create(value,def,cs_check_range in current_settings.localswitches);
      end;


    function getpropaccesslist(propsym:tpropertysym; pap:tpropaccesslisttypes;out propaccesslist:tpropaccesslist):boolean;
    var
      hpropsym : tpropertysym;
    begin
      result:=false;
      { find property in the overridden list }
      hpropsym:=propsym;
      repeat
        propaccesslist:=hpropsym.propaccesslist[pap];
        if not propaccesslist.empty then
          begin
            result:=true;
            exit;
          end;
        hpropsym:=hpropsym.overriddenpropsym;
      until not assigned(hpropsym);
    end;


    procedure propaccesslist_to_node(var p1:tnode;st:TSymtable;pl:tpropaccesslist);
      var
        plist : ppropaccesslistitem;
      begin
        plist:=pl.firstsym;
        while assigned(plist) do
         begin
           case plist^.sltype of
             sl_load :
               begin
                 addsymref(plist^.sym);
                 if not assigned(st) then
                   st:=plist^.sym.owner;
                 if (plist^.sym.typ<>staticvarsym) then
                   begin
                     { p1 can already contain the loadnode of
                       the class variable. When there is no tree yet we
                       may need to load it for with or objects }
                     if not assigned(p1) then
                      begin
                        case st.symtabletype of
                          withsymtable :
                            p1:=tnode(twithsymtable(st).withrefnode).getcopy;
                          ObjectSymtable :
                            p1:=load_self_node;
                        end;
                      end
                   end
                 else
                   begin
                     p1.free;
                     p1:=nil;
                   end;
                 if assigned(p1) then
                  p1:=csubscriptnode.create(plist^.sym,p1)
                 else
                  p1:=cloadnode.create(plist^.sym,st);
               end;
             sl_subscript :
               begin
                 addsymref(plist^.sym);
                 p1:=csubscriptnode.create(plist^.sym,p1);
               end;
             sl_typeconv :
               p1:=ctypeconvnode.create_explicit(p1,plist^.def);
             sl_absolutetype :
               begin
                 p1:=ctypeconvnode.create(p1,plist^.def);
                 include(p1.flags,nf_absolute);
               end;
             sl_vec :
               p1:=cvecnode.create(p1,cordconstnode.create(plist^.value,plist^.valuedef,true));
             else
               internalerror(200110205);
           end;
           plist:=plist^.next;
         end;
      end;


    function node_to_propaccesslist(p1:tnode):tpropaccesslist;
      var
        sl : tpropaccesslist;

        procedure addnode(p:tnode);
        begin
          case p.nodetype of
            subscriptn :
              begin
                addnode(tsubscriptnode(p).left);
                sl.addsym(sl_subscript,tsubscriptnode(p).vs);
              end;
            typeconvn :
              begin
                addnode(ttypeconvnode(p).left);
                if nf_absolute in ttypeconvnode(p).flags then
                  sl.addtype(sl_absolutetype,ttypeconvnode(p).totypedef)
                else
                  sl.addtype(sl_typeconv,ttypeconvnode(p).totypedef);
              end;
            vecn :
              begin
                addnode(tvecnode(p).left);
                if tvecnode(p).right.nodetype=ordconstn then
                  sl.addconst(sl_vec,tordconstnode(tvecnode(p).right).value,tvecnode(p).right.resultdef)
                else
                  begin
                    Message(parser_e_illegal_expression);
                    { recovery }
                    sl.addconst(sl_vec,0,tvecnode(p).right.resultdef);
                  end;
             end;
            loadn :
              sl.addsym(sl_load,tloadnode(p).symtableentry);
            else
              internalerror(200310282);
          end;
        end;

      begin
        sl:=tpropaccesslist.create;
        addnode(p1);
        result:=sl;
      end;


    function handle_staticfield_access(sym: tsym; nested: boolean; var p1: tnode): boolean;
      var
        static_name: shortstring;
        srsymtable: tsymtable;
      begin
        result:=false;
        { generate access code }
        if (sp_static in sym.symoptions) then
          begin
            result:=true;
            if not nested then
              static_name:=lower(sym.owner.name^)+'_'+sym.name
            else
             static_name:=lower(generate_nested_name(sym.owner,'_'))+'_'+sym.name;
            if sym.owner.defowner.typ=objectdef then
              searchsym_in_class(tobjectdef(sym.owner.defowner),tobjectdef(sym.owner.defowner),static_name,sym,srsymtable,true)
            else
              searchsym_in_record(trecorddef(sym.owner.defowner),static_name,sym,srsymtable);
            if assigned(sym) then
              check_hints(sym,sym.symoptions,sym.deprecatedmsg);
            p1.free;
            p1:=nil;
            { static syms are always stored as absolutevarsym to handle scope and storage properly }
            propaccesslist_to_node(p1,nil,tabsolutevarsym(sym).ref);
          end;
      end;


    function is_bitpacked_access(n: tnode): boolean;
      begin
        case n.nodetype of
          vecn:
            result:=
              is_packed_array(tvecnode(n).left.resultdef) and
              { only orddefs and enumdefs are actually bitpacked. Don't consider
                e.g. an access to a 3-byte record as "bitpacked", since it
                isn't }
              (tvecnode(n).left.resultdef.typ in [orddef,enumdef]) and
              not(tarraydef(tvecnode(n).left.resultdef).elepackedbitsize in [8,16,32,64]);
          subscriptn:
            result:=
              is_packed_record_or_object(tsubscriptnode(n).left.resultdef) and
              { see above }
              (tsubscriptnode(n).vs.vardef.typ in [orddef,enumdef]) and
              (not(tsubscriptnode(n).vs.vardef.packedbitsize in [8,16,32,64]) or
               (tsubscriptnode(n).vs.fieldoffset mod 8 <> 0));
          else
            result:=false;
        end;
      end;


    function genloadfield(n: tnode; const fieldname: string): tnode;
      var
        vs         : tsym;
      begin
        if not assigned(n.resultdef) then
          typecheckpass(n);
        vs:=tsym(tabstractrecorddef(n.resultdef).symtable.find(fieldname));
        if not assigned(vs) or
           (vs.typ<>fieldvarsym) then
          internalerror(2010061902);
        result:=csubscriptnode.create(vs,n);
      end;


    function has_no_code(n : tnode) : boolean;
      begin
        if n=nil then
          begin
            result:=true;
            exit;
          end;
        result:=false;
        case n.nodetype of
          nothingn:
            begin
               result:=true;
               exit;
            end;
          blockn:
            begin
              result:=has_no_code(tblocknode(n).left);
              exit;
            end;
          statementn:
            begin
              repeat
                result:=has_no_code(tstatementnode(n).left);
                n:=tstatementnode(n).right;
              until not(result) or not assigned(n);
              exit;
            end;
        end;
      end;


    function check_for_sideeffect(var n: tnode; arg: pointer): foreachnoderesult;
      begin
        result:=fen_false;
        if (n.nodetype in [assignn,calln,asmn]) or
          ((n.nodetype=inlinen) and
           (tinlinenode(n).inlinenumber in [in_write_x,in_writeln_x,in_read_x,in_readln_x,in_str_x_string,
             in_val_x,in_reset_x,in_rewrite_x,in_reset_typedfile,in_rewrite_typedfile,in_settextbuf_file_x,
             in_inc_x,in_dec_x,in_include_x_y,in_exclude_x_y,in_break,in_continue,in_setlength_x,
             in_finalize_x,in_new_x,in_dispose_x,in_exit,in_copy_x,in_initialize_x,in_leave,in_cycle])
          ) then
          result:=fen_norecurse_true;
      end;


    function might_have_sideeffects(n : tnode) : boolean;
      begin
        result:=foreachnodestatic(n,@check_for_sideeffect,nil);
      end;

    var
      nodecount : dword;

    function donodecount(var n: tnode; arg: pointer): foreachnoderesult;
      begin
        inc(nodecount);
        result:=fen_false;
      end;


    { rough estimation how large the tree "node" is }
    function node_count(node : tnode) : dword;
      begin
        nodecount:=0;
        foreachnodestatic(node,@donodecount,nil);
        result:=nodecount;
      end;


end.
