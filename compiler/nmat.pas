{
    Copyright (c) 2000-2005 by Florian Klaempfl

    Type checking and register allocation for math nodes

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
unit nmat;

{$i fpcdefs.inc}

interface

    uses
       node;

    type
       tmoddivnode = class(tbinopnode)
          function pass_1 : tnode;override;
          function pass_typecheck:tnode;override;
          function simplify(forinline : boolean) : tnode;override;
         protected
          { override the following if you want to implement }
          { parts explicitely in the code generator (JM)    }
          function use_moddiv64bitint_helper: boolean; virtual;
          function first_moddiv64bitint: tnode; virtual;
          function firstoptimize: tnode; virtual;
          function first_moddivint: tnode; virtual;
       end;
       tmoddivnodeclass = class of tmoddivnode;

       tshlshrnode = class(tbinopnode)
          function pass_1 : tnode;override;
          function pass_typecheck:tnode;override;
          function simplify(forinline : boolean) : tnode;override;
{$ifndef cpu64bitalu}
          { override the following if you want to implement }
          { parts explicitely in the code generator (CEC)
            Should return nil, if everything will be handled
            in the code generator
          }
          function first_shlshr64bitint: tnode; virtual;
{$endif not cpu64bitalu}
       end;
       tshlshrnodeclass = class of tshlshrnode;

       tunaryminusnode = class(tunarynode)
          constructor create(expr : tnode);virtual;
          function pass_1 : tnode;override;
          function pass_typecheck:tnode;override;
          function simplify(forinline : boolean) : tnode;override;
       end;
       tunaryminusnodeclass = class of tunaryminusnode;

       tunaryplusnode = class(tunarynode)
         constructor create(expr : tnode);virtual;
         function pass_1 : tnode;override;
         function pass_typecheck:tnode;override;
       end;
       tunaryplusnodeclass = class of tunaryplusnode;

       tnotnode = class(tunarynode)
          constructor create(expr : tnode);virtual;
          function pass_1 : tnode;override;
          function pass_typecheck:tnode;override;
          function simplify(forinline : boolean) : tnode;override;
       {$ifdef state_tracking}
          function track_state_pass(exec_known:boolean):boolean;override;
       {$endif}
       end;
       tnotnodeclass = class of tnotnode;

    var
       cmoddivnode : tmoddivnodeclass = tmoddivnode;
       cshlshrnode : tshlshrnodeclass = tshlshrnode;
       cunaryminusnode : tunaryminusnodeclass = tunaryminusnode;
       cunaryplusnode : tunaryplusnodeclass = tunaryplusnode;
       cnotnode : tnotnodeclass = tnotnode;

implementation

    uses
      systems,
      verbose,globals,cutils,
      globtype,constexp,
      symconst,symtype,symdef,symtable,
      defutil,
      htypechk,pass_1,
      cgbase,
      ncon,ncnv,ncal,nadd,nld,nbas,nflw,ninl,
      nutils;

{****************************************************************************
                              TMODDIVNODE
 ****************************************************************************}

    function tmoddivnode.simplify(forinline : boolean):tnode;
      var
        rv,lv : tconstexprint;
      begin
        result:=nil;

        if is_constintnode(right) then
          begin
            rv:=tordconstnode(right).value;
            if rv = 1 then
              begin
                case nodetype of
                  modn:
                    result := cordconstnode.create(0,left.resultdef,true);
                  divn:
                    result := left.getcopy;
                end;
                exit;
              end;
            if rv = 0 then
              begin
                Message(parser_e_division_by_zero);
                { recover }
                tordconstnode(right).value := 1;
              end;
            if (nf_isomod in flags) and
              (rv<=0) then
               begin
                 Message(cg_e_mod_only_defined_for_pos_quotient);
                 { recover }
                 tordconstnode(right).value := 1;
               end;
          end;

        if is_constintnode(right) and is_constintnode(left) then
          begin
            rv:=tordconstnode(right).value;
            lv:=tordconstnode(left).value;

            case nodetype of
              modn:
                if nf_isomod in flags then
                  begin
                    if lv>=0 then
                      result:=create_simplified_ord_const(lv mod rv,resultdef,forinline)
                    else
                      if ((-lv) mod rv)=0 then
                        result:=create_simplified_ord_const((-lv) mod rv,resultdef,forinline)
                      else
                        result:=create_simplified_ord_const(rv-((-lv) mod rv),resultdef,forinline);
                  end
                else
                  result:=create_simplified_ord_const(lv mod rv,resultdef,forinline);
              divn:
                result:=create_simplified_ord_const(lv div rv,resultdef,forinline);
            end;
         end;
      end;


    function tmoddivnode.use_moddiv64bitint_helper: boolean;
      begin
        { not with an ifdef around the call to this routine, because e.g. the
          Java VM has a signed 64 bit division opcode, but not an unsigned
          one }
{$ifdef cpu64bitalu}
        result:=false;
{$else cpu64bitalu}
        result:=
          (left.resultdef.typ=orddef) and
          (right.resultdef.typ=orddef) and
          (is_64bitint(left.resultdef) or is_64bitint(right.resultdef));
{$endif cpu64bitaly}
      end;


    function tmoddivnode.pass_typecheck:tnode;
      var
        else_block,
        hp,t : tnode;
        rd,ld : torddef;
        else_statements,
        statements : tstatementnode;
        result_data : ttempcreatenode;
      begin
         result:=nil;
         typecheckpass(left);
         typecheckpass(right);
         set_varstate(left,vs_read,[vsf_must_be_valid]);
         set_varstate(right,vs_read,[vsf_must_be_valid]);
         if codegenerror then
           exit;

         { tp procvar support }
         maybe_call_procvar(left,true);
         maybe_call_procvar(right,true);

         { allow operator overloading }
         t:=self;
         if isbinaryoverloaded(t) then
           begin
              result:=t;
              exit;
           end;

         { we need 2 orddefs always }
         if (left.resultdef.typ<>orddef) then
           inserttypeconv(left,sinttype);
         if (right.resultdef.typ<>orddef) then
           inserttypeconv(right,sinttype);
         if codegenerror then
           exit;

         { Try only now to simply constant
           as otherwise you might create
           tconstnode with return type that are
           not compatible with tconst node
           as in bug report 21566 PM }

         result:=simplify(false);
         if assigned(result) then
           exit;

         rd:=torddef(right.resultdef);
         ld:=torddef(left.resultdef);

         { if one operand is a cardinal and the other is a positive constant, convert the }
         { constant to a cardinal as well so we don't have to do a 64bit division (JM)    }
         { Do the same for qwords and positive constants as well, otherwise things like   }
         { "qword mod 10" are evaluated with int64 as result, which is wrong if the       }
         { "qword" was > high(int64) (JM)                                                 }
         { Additionally, do the same for cardinal/qwords and other positive types, but    }
         { always in a way that a smaller type is converted to a bigger type              }
         { (webtbs/tw8870)                                                                }
         if (rd.ordtype in [u32bit,u64bit]) and
            ((is_constintnode(left) and
              (tordconstnode(left).value >= 0)) or
             (not is_signed(ld) and
              (rd.size >= ld.size))) then
           begin
             inserttypeconv(left,right.resultdef);
             ld:=torddef(left.resultdef);
           end;
         if (ld.ordtype in [u32bit,u64bit]) and
            ((is_constintnode(right) and
              (tordconstnode(right).value >= 0)) or
             (not is_signed(rd) and
              (ld.size >= rd.size))) then
          begin
            inserttypeconv(right,left.resultdef);
            rd:=torddef(right.resultdef);
          end;

         { when there is one currency value, everything is done
           using currency }
         if (ld.ordtype=scurrency) or
            (rd.ordtype=scurrency) then
           begin
             if (ld.ordtype<>scurrency) then
              inserttypeconv(left,s64currencytype);
             if (rd.ordtype<>scurrency) then
              inserttypeconv(right,s64currencytype);
             resultdef:=left.resultdef;
           end
         else
{$ifndef cpu64bitaddr}
          { when there is one 64bit value, everything is done
            in 64bit }
          if (is_64bitint(left.resultdef) or
              is_64bitint(right.resultdef)) then
           begin
             if is_signed(rd) or is_signed(ld) then
               begin
                  if (ld.ordtype<>s64bit) then
                    inserttypeconv(left,s64inttype);
                  if (rd.ordtype<>s64bit) then
                    inserttypeconv(right,s64inttype);
               end
             else
               begin
                  if (ld.ordtype<>u64bit) then
                    inserttypeconv(left,u64inttype);
                  if (rd.ordtype<>u64bit) then
                    inserttypeconv(right,u64inttype);
               end;
             resultdef:=left.resultdef;
           end
         else
          { when mixing cardinals and signed numbers, convert everythign to 64bit (JM) }
          if ((rd.ordtype = u32bit) and
              is_signed(ld)) or
             ((ld.ordtype = u32bit) and
              is_signed(rd)) then
           begin
              CGMessage(type_h_mixed_signed_unsigned);
              if (ld.ordtype<>s64bit) then
                inserttypeconv(left,s64inttype);
              if (rd.ordtype<>s64bit) then
                inserttypeconv(right,s64inttype);
              resultdef:=left.resultdef;
           end
         else
{$endif not cpu64bitaddr}
           begin
              { Make everything always default singed int }
              if not(rd.ordtype in [torddef(sinttype).ordtype,torddef(uinttype).ordtype]) then
                inserttypeconv(right,sinttype);
              if not(ld.ordtype in [torddef(sinttype).ordtype,torddef(uinttype).ordtype]) then
                inserttypeconv(left,sinttype);
              resultdef:=right.resultdef;
           end;

         { when the result is currency we need some extra code for
           division. this should not be done when the divn node is
           created internally }
         if (nodetype=divn) and
            not(nf_is_currency in flags) and
            is_currency(resultdef) then
          begin
            hp:=caddnode.create(muln,getcopy,cordconstnode.create(10000,s64currencytype,false));
            include(hp.flags,nf_is_currency);
            result:=hp;
          end;

         if (nodetype=modn) and (nf_isomod in flags) then
           begin
             result:=internalstatements(statements);
             else_block:=internalstatements(else_statements);
             result_data:=ctempcreatenode.create(resultdef,resultdef.size,tt_persistent,true);

             { right <=0? }
             addstatement(statements,cifnode.create(caddnode.create(lten,right.getcopy,cordconstnode.create(0,resultdef,false)),
               { then: result:=left mod right }
               ccallnode.createintern('fpc_divbyzero',nil),
               nil
               ));

             { prepare else block }
             { result:=(-left) mod right }
             addstatement(else_statements,cassignmentnode.create(ctemprefnode.create(result_data),cmoddivnode.create(modn,cunaryminusnode.create(left.getcopy),right.getcopy)));
             { result<>0? }
             addstatement(else_statements,cifnode.create(caddnode.create(unequaln,ctemprefnode.create(result_data),cordconstnode.create(0,resultdef,false)),
               { then: result:=right-result }
               cassignmentnode.create(ctemprefnode.create(result_data),caddnode.create(subn,right.getcopy,ctemprefnode.create(result_data))),
               nil
               ));

             addstatement(statements,result_data);
             { if left>=0 }
             addstatement(statements,cifnode.create(caddnode.create(gten,left.getcopy,cordconstnode.create(0,resultdef,false)),
               { then: result:=left mod right }
               cassignmentnode.create(ctemprefnode.create(result_data),cmoddivnode.create(modn,left.getcopy,right.getcopy)),
               { else block }
               else_block
               ));

             addstatement(statements,ctempdeletenode.create_normal_temp(result_data));
             addstatement(statements,ctemprefnode.create(result_data));
           end;
      end;


    function tmoddivnode.first_moddivint: tnode;
{$ifdef cpuneedsdiv32helper}
      var
        procname: string[31];
      begin
        result := nil;

        { otherwise create a call to a helper }
        if nodetype = divn then
          procname := 'fpc_div_'
        else
          procname := 'fpc_mod_';
        { only qword needs the unsigned code, the
          signed code is also used for currency }
        if is_signed(resultdef) then
          procname := procname + 'longint'
        else
          procname := procname + 'dword';

        result := ccallnode.createintern(procname,ccallparanode.create(left,
          ccallparanode.create(right,nil)));
        left := nil;
        right := nil;
        firstpass(result);
      end;
{$else cpuneedsdiv32helper}
      begin
        result:=nil;
      end;
{$endif cpuneedsdiv32helper}


    function tmoddivnode.first_moddiv64bitint: tnode;
      var
        procname: string[31];
      begin
        result := nil;

        { when currency is used set the result of the
          parameters to s64bit, so they are not converted }
        if is_currency(resultdef) then
          begin
            left.resultdef:=s64inttype;
            right.resultdef:=s64inttype;
          end;

        { otherwise create a call to a helper }
        if nodetype = divn then
          procname := 'fpc_div_'
        else
          procname := 'fpc_mod_';
        { only qword needs the unsigned code, the
          signed code is also used for currency }
        if is_signed(resultdef) then
          procname := procname + 'int64'
        else
          procname := procname + 'qword';

        result := ccallnode.createintern(procname,ccallparanode.create(left,
          ccallparanode.create(right,nil)));
        left := nil;
        right := nil;
        firstpass(result);
      end;


    function tmoddivnode.firstoptimize: tnode;
      var
        power,shiftval : longint;
        newtype: tnodetype;
        statements : tstatementnode;
        temp : ttempcreatenode;
      begin
        result := nil;
        { divide/mod a number by a constant which is a power of 2? }
        if (right.nodetype = ordconstn) and
{$ifdef cpu64bitalu}
          { for 64 bit, we leave the optimization to the cg }
            (not is_signed(resultdef)) and
{$else cpu64bitalu}
           ((nodetype=divn) and (is_64bit(resultdef)) or
            not is_signed(resultdef)) and
{$endif cpu64bitalu}
           ispowerof2(tordconstnode(right).value,power) then
          begin
            if nodetype=divn then
              begin
                if is_signed(resultdef) then
                  begin
                    if is_64bitint(left.resultdef) then
                      if not (cs_opt_size in current_settings.optimizerswitches) then
                        shiftval:=63
                      else
                        { the shift code is a lot bigger than the call to }
                        { the divide helper                               }
                        exit
                    else
                      shiftval:=31;

                    result:=internalstatements(statements);
                    temp:=ctempcreatenode.create(left.resultdef,left.resultdef.size,tt_persistent,true);
                    addstatement(statements,temp);
                    addstatement(statements,cassignmentnode.create(ctemprefnode.create(temp),
                     left));
                    left:=nil;

                    addstatement(statements,ccallnode.createintern('fpc_sarint64',
                      ccallparanode.create(cordconstnode.create(power,u8inttype,false),
                      ccallparanode.create(caddnode.create(addn,ctemprefnode.create(temp),
                        caddnode.create(andn,
                          ccallnode.createintern('fpc_sarint64',
                            ccallparanode.create(cordconstnode.create(shiftval,u8inttype,false),
                            ccallparanode.create(ctemprefnode.create(temp),nil))
                          ),
                          cordconstnode.create(tordconstnode(right).value-1,
                            right.resultdef,false)
                        )),nil
                      )))
                    );
                  end
                else
                  begin
                    tordconstnode(right).value:=power;
                    result:=cshlshrnode.create(shrn,left,right)
                  end;
              end
            else
              begin
                dec(tordconstnode(right).value.uvalue);
                result := caddnode.create(andn,left,right);
              end;
            { left and right are reused }
            left := nil;
            right := nil;
            firstpass(result);
            exit;
          end;
      end;


    function tmoddivnode.pass_1 : tnode;
      begin
         result:=nil;
         firstpass(left);
         firstpass(right);
         if codegenerror then
           exit;

         { Try to optimize mod/div }
         result := firstoptimize;
         if assigned(result) then
           exit;

         { 64bit }
         if use_moddiv64bitint_helper then
           begin
             result := first_moddiv64bitint;
             if assigned(result) then
               exit;
             expectloc:=LOC_REGISTER;
           end
         else
           begin
             result := first_moddivint;
             if assigned(result) then
               exit;
           end;
         expectloc:=LOC_REGISTER;
      end;



{****************************************************************************
                              TSHLSHRNODE
 ****************************************************************************}

    function tshlshrnode.simplify(forinline : boolean):tnode;
      begin
        result:=nil;
        { constant folding }
        if is_constintnode(left) and is_constintnode(right) then
          begin
             case nodetype of
                shrn:
                  result:=create_simplified_ord_const(tordconstnode(left).value shr tordconstnode(right).value,resultdef,forinline);
                shln:
                  result:=create_simplified_ord_const(tordconstnode(left).value shl tordconstnode(right).value,resultdef,forinline);
             end;
          end;

      end;


    function tshlshrnode.pass_typecheck:tnode;
      var
         t : tnode;
{$ifdef cpunodefaultint}
         nd : tdef;
{$endif cpunodefaultint}
      begin
         result:=nil;
         typecheckpass(left);
         typecheckpass(right);
         set_varstate(right,vs_read,[vsf_must_be_valid]);
         set_varstate(left,vs_read,[vsf_must_be_valid]);
         if codegenerror then
           exit;

         { tp procvar support }
         maybe_call_procvar(left,true);
         maybe_call_procvar(right,true);

         { allow operator overloading }
         t:=self;
         if isbinaryoverloaded(t) then
           begin
              result:=t;
              exit;
           end;

{$ifdef cpunodefaultint}
         { for small cpus we use the smallest common type }
         if (left.resultdef.typ=orddef) and (right.resultdef.typ=orddef) then
           nd:=get_common_intdef(torddef(left.resultdef),torddef(right.resultdef),false)
         else
           nd:=s32inttype;
{$endif cpunodefaultint}

         { calculations for ordinals < 32 bit have to be done in
           32 bit for backwards compatibility. That way 'shl 33' is
           the same as 'shl 1'. It's ugly but compatible with delphi/tp/gcc }
         if (not is_64bit(left.resultdef)) and
            (torddef(left.resultdef).ordtype<>u32bit) then
           begin
             { keep singness of orignal type }
             if is_signed(left.resultdef) then
{$ifdef cpunodefaultint}
               inserttypeconv(left,nd)
{$else cpunodefaultint}
               inserttypeconv(left,s32inttype)
{$endif cpunodefaultint}
             else
               begin
{$ifdef cpunodefaultint}
                 inserttypeconv(left,nd)
{$else cpunodefaultint}
                 inserttypeconv(left,u32inttype);
{$endif cpunodefaultint}
               end
           end;

{$ifdef cpunodefaultint}
         inserttypeconv(right,nd);
{$else cpunodefaultint}
         inserttypeconv(right,sinttype);
{$endif cpunodefaultint}

         resultdef:=left.resultdef;

         result:=simplify(false);
         if assigned(result) then
           exit;
      end;


{$ifndef cpu64bitalu}
    function tshlshrnode.first_shlshr64bitint: tnode;
      var
        procname: string[31];
      begin
        result := nil;
        { Normally already done below, but called again,
          just in case it is called directly }
        firstpass(left);
        { otherwise create a call to a helper }
        if is_signed(left.resultdef) then
          procname:='int64'
        else
          procname:='qword';
        if nodetype = shln then
          procname := 'fpc_shl_'+procname
        else
          procname := 'fpc_shr_'+procname;
        { this order of parameters works at least for the arm,
          however it should work for any calling conventions (FK) }
        result := ccallnode.createintern(procname,ccallparanode.create(right,
          ccallparanode.create(left,nil)));
        left := nil;
        right := nil;
        firstpass(result);
      end;
{$endif not cpu64bitalu}


    function tshlshrnode.pass_1 : tnode;
      var
         regs : longint;
      begin
         result:=nil;
         firstpass(left);
         firstpass(right);
         if codegenerror then
           exit;

{$ifndef cpu64bitalu}
         { 64 bit ints have their own shift handling }
         if is_64bit(left.resultdef) then
           begin
             result := first_shlshr64bitint;
             if assigned(result) then
               exit;
             regs:=2;
           end
         else
{$endif not cpu64bitalu}
           begin
             regs:=1
           end;

         if (right.nodetype<>ordconstn) then
           inc(regs);
         expectloc:=LOC_REGISTER;
      end;


{****************************************************************************
                            TUNARYMINUSNODE
 ****************************************************************************}

    constructor tunaryminusnode.create(expr : tnode);
      begin
         inherited create(unaryminusn,expr);
      end;


    function tunaryminusnode.simplify(forinline : boolean):tnode;
      begin
        result:=nil;
        { constant folding }
        if is_constintnode(left) then
          begin
             result:=create_simplified_ord_const(-tordconstnode(left).value,resultdef,forinline);
             exit;
          end;
        if is_constrealnode(left) then
          begin
             trealconstnode(left).value_real:=-trealconstnode(left).value_real;
             trealconstnode(left).value_currency:=-trealconstnode(left).value_currency;
             result:=left;
             left:=nil;
             exit;
          end;
      end;


    function tunaryminusnode.pass_typecheck : tnode;
      var
         t : tnode;
      begin
         result:=nil;
         typecheckpass(left);
         set_varstate(left,vs_read,[vsf_must_be_valid]);
         if codegenerror then
           exit;

         result:=simplify(false);
         if assigned(result) then
           exit;

         resultdef:=left.resultdef;
         if (left.resultdef.typ=floatdef) or
            is_currency(left.resultdef) then
           begin
           end
{$ifdef SUPPORT_MMX}
         else if (cs_mmx in current_settings.localswitches) and
           is_mmx_able_array(left.resultdef) then
             begin
               { if saturation is on, left.resultdef isn't
                 "mmx able" (FK)
               if (cs_mmx_saturation in current_settings.localswitches^) and
                 (torddef(tarraydef(resultdef).definition).typ in
                 [s32bit,u32bit]) then
                 CGMessage(type_e_mismatch);
               }
             end
{$endif SUPPORT_MMX}
{$ifndef cpu64bitaddr}
         else if is_64bit(left.resultdef) then
           begin
             inserttypeconv(left,s64inttype);
             resultdef:=left.resultdef
           end
{$endif not cpu64bitaddr}
         else if (left.resultdef.typ=orddef) then
           begin
             inserttypeconv(left,sinttype);
             resultdef:=left.resultdef
           end
         else
           begin
             { allow operator overloading }
             t:=self;
             if isunaryoverloaded(t) then
               begin
                  result:=t;
                  exit;
               end;

             CGMessage(type_e_mismatch);
           end;
      end;

    { generic code     }
    { overridden by:   }
    {   i386           }
    function tunaryminusnode.pass_1 : tnode;
      var
        procname: string[31];
        fdef : tdef;
      begin
        result:=nil;
        firstpass(left);
        if codegenerror then
          exit;

        if (cs_fp_emulation in current_settings.moduleswitches) and (left.resultdef.typ=floatdef) then
          begin
            if not(target_info.system in systems_wince) then
              begin
                case tfloatdef(resultdef).floattype of
                  s32real:
                    begin
                      procname:='float32_sub';
                      fdef:=search_system_type('FLOAT32REC').typedef;
                    end;
                  s64real:
                    begin
                      procname:='float64_sub';
                      fdef:=search_system_type('FLOAT64').typedef;
                    end;
                  {!!! not yet implemented
                  s128real:
                  }
                  else
                    internalerror(2005082801);
                end;
                result:=ctypeconvnode.create_internal(ccallnode.createintern(procname,ccallparanode.create(
                  ctypeconvnode.create_internal(left,fDef),
                  ccallparanode.create(ctypeconvnode.create_internal(crealconstnode.create(0,resultdef),fdef),nil))),resultdef);
              end
            else
              begin
                case tfloatdef(resultdef).floattype of
                  s32real:
                    procname:='NEGS';
                  s64real:
                    procname:='NEGD';
                  {!!! not yet implemented
                  s128real:
                  }
                  else
                    internalerror(2005082802);
                end;
                result:=ccallnode.createintern(procname,ccallparanode.create(left,nil));
              end;

            left:=nil;
          end
        else
          begin
            if (left.resultdef.typ=floatdef) then
              expectloc:=LOC_FPUREGISTER
{$ifdef SUPPORT_MMX}
             else if (cs_mmx in current_settings.localswitches) and
               is_mmx_able_array(left.resultdef) then
              expectloc:=LOC_MMXREGISTER
{$endif SUPPORT_MMX}
             else if (left.resultdef.typ=orddef) then
               expectloc:=LOC_REGISTER;
          end;
      end;

{****************************************************************************
                             TUNARYPLUSNODE
 ****************************************************************************}

    constructor tunaryplusnode.create(expr: tnode);
      begin
        inherited create(unaryplusn,expr);
      end;

    function tunaryplusnode.pass_1: tnode;
      begin
        result:=nil;
        { can never happen because all the conversions happen
          in pass_typecheck }
        internalerror(201012250);
      end;

    function tunaryplusnode.pass_typecheck: tnode;
      var
        t:tnode;
      begin
        result:=nil;
        typecheckpass(left);
        set_varstate(left,vs_read,[vsf_must_be_valid]);
        if codegenerror then
          exit;

        if is_constintnode(left) or
           is_constrealnode(left) or
           (left.resultdef.typ=floatdef) or
           is_currency(left.resultdef)
{$ifdef SUPPORT_MMX}
           or ((cs_mmx in current_settings.localswitches) and
                is_mmx_able_array(left.resultdef))
{$endif SUPPORT_MMX}
        then
          begin
            result:=left;
            left:=nil;
          end
{$ifndef cpu64bitaddr}
        else if is_64bit(left.resultdef) then
          begin
            inserttypeconv(left,s64inttype);
            result:=left;
            left:=nil;
          end
{$endif not cpu64bitaddr}
        else if (left.resultdef.typ=orddef) then
          begin
            inserttypeconv(left,sinttype);
            result:=left;
            left:=nil;
          end
        else
          begin
            { allow operator overloading }
            t:=self;
            if isunaryoverloaded(t) then
              begin
                result:=t;
                exit;
             end;

             CGMessage(type_e_mismatch);
           end;
      end;


{****************************************************************************
                               TNOTNODE
 ****************************************************************************}

    const
      boolean_reverse:array[ltn..unequaln] of Tnodetype=(
        gten,gtn,lten,ltn,unequaln,equaln
      );

    constructor tnotnode.create(expr : tnode);
      begin
         inherited create(notn,expr);
      end;


    function tnotnode.simplify(forinline : boolean):tnode;
      var
        v : tconstexprint;
        t : tnode;
        def : tdef;
      begin
        result:=nil;
        { Try optmimizing ourself away }
        if left.nodetype=notn then
          begin
            { Double not. Remove both }
            result:=Tnotnode(left).left;
            tnotnode(left).left:=nil;
            exit;
          end;

        if (left.nodetype in [ltn,lten,equaln,unequaln,gtn,gten]) then
         begin
           { Not of boolean expression. Turn around the operator and remove
             the not. This is not allowed for sets with the gten/lten,
             because there is no ltn/gtn support }
           if (taddnode(left).left.resultdef.typ<>setdef) or
              (left.nodetype in [equaln,unequaln]) then
            begin
              result:=left;
              left.nodetype:=boolean_reverse[left.nodetype];
              left:=nil;
              exit;
            end;
         end;

        { constant folding }
        if (left.nodetype=ordconstn) then
          begin
             v:=tordconstnode(left).value;
             def:=left.resultdef;
             case torddef(left.resultdef).ordtype of
               pasbool8,
               pasbool16,
               pasbool32,
               pasbool64,
               bool8bit,
               bool16bit,
               bool32bit,
               bool64bit:
                 begin
                   v:=byte(not(boolean(int64(v))));
                   if is_cbool(left.resultdef) then
                     v:=-v;
                 end;
               uchar,
               uwidechar,
               u8bit,
               s8bit,
               u16bit,
               s16bit,
               s32bit,
{$ifdef cpu64bitaddr}
               u32bit,
{$endif cpu64bitaddr}
               s64bit:
                 begin
                   v:=int64(not int64(v));
                   if (torddef(left.resultdef).ordtype<>s64bit) then
                     def:=sinttype
                   else
                     def:=s64inttype;
                 end;
{$ifndef cpu64bitaddr}
               u32bit,
{$endif not cpu64bitaddr}
               u64bit :
                 begin
                   { Delphi-compatible: not dword = dword (not word = longint) }
                   { Extension: not qword = qword                              }
                   v:=qword(not qword(v));
                   { will be truncated by the ordconstnode for u32bit }
                 end;
               else
                 CGMessage(type_e_mismatch);
             end;
             { not-nodes are not range checked by the code generator -> also
               don't range check while inlining; the resultdef is a bit tricky
               though: the node's resultdef gets changed in most cases compared
               to left, but the not-operation itself is caried out in the code
               generator using the size of left
               }
             if not(forinline) then
               t:=cordconstnode.create(v,def,false)
             else
               begin
                 { cut off the value if necessary }
                 t:=cordconstnode.create(v,left.resultdef,false);
                 { now convert to node's resultdef }
                 inserttypeconv_explicit(t,def);
               end;
             result:=t;
             exit;
          end;
      end;


    function tnotnode.pass_typecheck : tnode;
      var
         t : tnode;
      begin
         result:=nil;
         typecheckpass(left);
         set_varstate(left,vs_read,[vsf_must_be_valid]);
         if codegenerror then
           exit;

         { tp procvar support }
         maybe_call_procvar(left,true);

         resultdef:=left.resultdef;

         result:=simplify(false);
         if assigned(result) then
           exit;

         if is_boolean(resultdef) then
           begin
           end
         else
{$ifdef SUPPORT_MMX}
           if (cs_mmx in current_settings.localswitches) and
             is_mmx_able_array(left.resultdef) then
             begin
             end
         else
{$endif SUPPORT_MMX}
{$ifndef cpu64bitaddr}
           if is_64bitint(left.resultdef) then
             begin
             end
         else
{$endif not cpu64bitaddr}
           if is_integer(left.resultdef) then
             begin
             end
         else
           begin
             { allow operator overloading }
             t:=self;
             if isunaryoverloaded(t) then
               begin
                  result:=t;
                  exit;
               end;

             CGMessage(type_e_mismatch);
           end;
      end;


    function tnotnode.pass_1 : tnode;
      begin
         result:=nil;
         firstpass(left);
         if codegenerror then
           exit;

         expectloc:=left.expectloc;
         if is_boolean(resultdef) then
           begin
             if (expectloc in [LOC_REFERENCE,LOC_CREFERENCE,LOC_CREGISTER]) then
               expectloc:=LOC_REGISTER;
            { before loading it into flags we need to load it into
              a register thus 1 register is need PM }
{$ifdef cpuflags}
             if left.expectloc<>LOC_JUMP then
               expectloc:=LOC_FLAGS;
{$endif def cpuflags}
           end
         else
{$ifdef SUPPORT_MMX}
           if (cs_mmx in current_settings.localswitches) and
             is_mmx_able_array(left.resultdef) then
             expectloc:=LOC_MMXREGISTER
         else
{$endif SUPPORT_MMX}
{$ifndef cpu64bitalu}
           if is_64bit(left.resultdef) then
             begin
                if (expectloc in [LOC_REFERENCE,LOC_CREFERENCE,LOC_CREGISTER]) then
                  expectloc:=LOC_REGISTER;
             end
         else
{$endif not cpu64bitalu}
           if is_integer(left.resultdef) then
             expectloc:=LOC_REGISTER;
      end;

{$ifdef state_tracking}
    function Tnotnode.track_state_pass(exec_known:boolean):boolean;
      begin
        track_state_pass:=true;
        if left.track_state_pass(exec_known) then
          begin
            left.resultdef:=nil;
            do_typecheckpass(left);
          end;
      end;
{$endif}

end.
