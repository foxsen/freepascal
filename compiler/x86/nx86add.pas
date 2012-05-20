{
    Copyright (c) 2000-2002 by Florian Klaempfl

    Common code generation for add nodes on the i386 and x86

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
unit nx86add;

{$i fpcdefs.inc}

  interface

    uses
      symtype,
      cgbase,
      cpubase,
      node,nadd,ncgadd;

    type
      tx86addnode = class(tcgaddnode)
      protected
        function  getresflags(unsigned : boolean) : tresflags;
        procedure left_must_be_reg(opdef: tdef; opsize:TCGSize;noswap:boolean);
        procedure check_left_and_right_fpureg(force_fpureg: boolean);
        procedure emit_op_right_left(op:TAsmOp;opsize:TCgSize);
        procedure emit_generic_code(op:TAsmOp;opsize:TCgSize;unsigned,extra_not,mboverflow:boolean);

        procedure second_cmpfloatsse;
        procedure second_addfloatsse;
      public
        procedure second_addfloat;override;
        procedure second_addsmallset;override;
        procedure second_add64bit;override;
        procedure second_cmpfloat;override;
        procedure second_cmpsmallset;override;
        procedure second_cmp64bit;override;
        procedure second_cmpordinal;override;
{$ifdef SUPPORT_MMX}
        procedure second_opmmx;override;
{$endif SUPPORT_MMX}
        procedure second_opvector;override;
      end;


  implementation

    uses
      globtype,globals,
      verbose,cutils,
      cpuinfo,
      aasmbase,aasmtai,aasmdata,aasmcpu,
      symconst,symdef,
      cgobj,hlcgobj,cgx86,cga,cgutils,
      paramgr,tgobj,ncgutil,
      ncon,nset,ninl,
      defutil;


{*****************************************************************************
                                  Helpers
*****************************************************************************}

    procedure tx86addnode.emit_generic_code(op:TAsmOp;opsize:TCGSize;unsigned,extra_not,mboverflow:boolean);
      var
        power : longint;
        hl4   : tasmlabel;
        r     : Tregister;
      begin
        { at this point, left.location.loc should be LOC_REGISTER }
        if right.location.loc=LOC_REGISTER then
         begin
           { right.location is a LOC_REGISTER }
           { when swapped another result register }
           if (nodetype=subn) and (nf_swapped in flags) then
            begin
              if extra_not then
               emit_reg(A_NOT,TCGSize2Opsize[opsize],left.location.register);
              emit_reg_reg(op,TCGSize2Opsize[opsize],left.location.register,right.location.register);
              { newly swapped also set swapped flag }
              location_swap(left.location,right.location);
              toggleflag(nf_swapped);
            end
           else
            begin
              if extra_not then
                emit_reg(A_NOT,TCGSize2Opsize[opsize],right.location.register);
              if (op=A_ADD) or (op=A_OR) or (op=A_AND) or (op=A_XOR) or (op=A_IMUL) then
                location_swap(left.location,right.location);
              emit_reg_reg(op,TCGSize2Opsize[opsize],right.location.register,left.location.register);
            end;
         end
        else
         begin
           { right.location is not a LOC_REGISTER }
           if (nodetype=subn) and (nf_swapped in flags) then
            begin
              if extra_not then
                cg.a_op_reg_reg(current_asmdata.CurrAsmList,OP_NOT,opsize,left.location.register,left.location.register);
              r:=cg.getintregister(current_asmdata.CurrAsmList,opsize);
              hlcg.a_load_loc_reg(current_asmdata.CurrAsmList,right.resultdef,hlcg.tcgsize2orddef(opsize),right.location,r);
              emit_reg_reg(op,TCGSize2Opsize[opsize],left.location.register,r);
              cg.a_load_reg_reg(current_asmdata.CurrAsmList,opsize,opsize,r,left.location.register);
            end
           else
            begin
               { Optimizations when right.location is a constant value }
               if (op=A_CMP) and
                  (nodetype in [equaln,unequaln]) and
                  (right.location.loc=LOC_CONSTANT) and
                  (right.location.value=0) then
                 begin
                   emit_reg_reg(A_TEST,TCGSize2Opsize[opsize],left.location.register,left.location.register);
                 end
               else
                 if (op=A_ADD) and
                    (right.location.loc=LOC_CONSTANT) and
                    (right.location.value=1) and
                    not(cs_check_overflow in current_settings.localswitches) then
                  begin
                    emit_reg(A_INC,TCGSize2Opsize[opsize],left.location.register);
                  end
               else
                 if (op=A_SUB) and
                    (right.location.loc=LOC_CONSTANT) and
                    (right.location.value=1) and
                    not(cs_check_overflow in current_settings.localswitches) then
                  begin
                    emit_reg(A_DEC,TCGSize2Opsize[opsize],left.location.register);
                  end
               else
                 if (op=A_IMUL) and
                    (right.location.loc=LOC_CONSTANT) and
                    (ispowerof2(int64(right.location.value),power)) and
                    not(cs_check_overflow in current_settings.localswitches) then
                  begin
                    emit_const_reg(A_SHL,TCGSize2Opsize[opsize],power,left.location.register);
                  end
               else
                 begin
                   if extra_not then
                     begin
                        r:=cg.getintregister(current_asmdata.CurrAsmList,opsize);
                        hlcg.a_load_loc_reg(current_asmdata.CurrAsmList,right.resultdef,hlcg.tcgsize2orddef(opsize),right.location,r);
                        emit_reg(A_NOT,TCGSize2Opsize[opsize],r);
                        emit_reg_reg(A_AND,TCGSize2Opsize[opsize],r,left.location.register);
                     end
                   else
                     begin
                        emit_op_right_left(op,opsize);
                     end;
                 end;
            end;
         end;

        { only in case of overflow operations }
        { produce overflow code }
        { we must put it here directly, because sign of operation }
        { is in unsigned VAR!!                                   }
        if mboverflow then
         begin
           if cs_check_overflow in current_settings.localswitches  then
            begin
              current_asmdata.getjumplabel(hl4);
              if unsigned then
                cg.a_jmp_flags(current_asmdata.CurrAsmList,F_AE,hl4)
              else
                cg.a_jmp_flags(current_asmdata.CurrAsmList,F_NO,hl4);
              cg.a_call_name(current_asmdata.CurrAsmList,'FPC_OVERFLOW',false);
              cg.a_label(current_asmdata.CurrAsmList,hl4);
            end;
         end;
      end;


    procedure tx86addnode.left_must_be_reg(opdef: tdef; opsize:TCGSize;noswap:boolean);
      begin
        { left location is not a register? }
        if (left.location.loc<>LOC_REGISTER) then
         begin
           { if right is register then we can swap the locations }
           if (not noswap) and
              (right.location.loc=LOC_REGISTER) then
            begin
              location_swap(left.location,right.location);
              toggleflag(nf_swapped);
            end
           else
            begin
              { maybe we can reuse a constant register when the
                operation is a comparison that doesn't change the
                value of the register }
              hlcg.location_force_reg(current_asmdata.CurrAsmList,left.location,left.resultdef,opdef,(nodetype in [ltn,lten,gtn,gten,equaln,unequaln]));
            end;
          end;
        if (right.location.loc<>LOC_CONSTANT) and
           (tcgsize2unsigned[right.location.size]<>tcgsize2unsigned[opsize]) then
          hlcg.location_force_reg(current_asmdata.CurrAsmList,right.location,right.resultdef,opdef,true);
        if (left.location.loc<>LOC_CONSTANT) and
           (tcgsize2unsigned[left.location.size]<>tcgsize2unsigned[opsize]) then
          hlcg.location_force_reg(current_asmdata.CurrAsmList,left.location,left.resultdef,opdef,false);
       end;


    procedure tx86addnode.check_left_and_right_fpureg(force_fpureg: boolean);
      begin
        if (right.location.loc<>LOC_FPUREGISTER) then
         begin
           if (force_fpureg) then
             begin
               location_force_fpureg(current_asmdata.CurrAsmList,right.location,false);
                if (left.location.loc<>LOC_FPUREGISTER) then
                  location_force_fpureg(current_asmdata.CurrAsmList,left.location,false)
                else
                  { left was on the stack => swap }
                  toggleflag(nf_swapped);
             end
         end
        { the nominator in st0 }
        else if (left.location.loc<>LOC_FPUREGISTER) then
          begin
            if (force_fpureg) then
              location_force_fpureg(current_asmdata.CurrAsmList,left.location,false)
          end
        else
          begin
            { fpu operands are always in the wrong order on the stack }
            toggleflag(nf_swapped);
          end;
      end;


    procedure tx86addnode.emit_op_right_left(op:TAsmOp;opsize:TCgsize);
{$ifdef x86_64}
      var
        tmpreg : tregister;
{$endif x86_64}
      begin
        if (right.location.loc in [LOC_CSUBSETREG,LOC_SUBSETREG,LOC_SUBSETREF,LOC_CSUBSETREF]) then
          hlcg.location_force_reg(current_asmdata.CurrAsmList,right.location,right.resultdef,right.resultdef,true);
        { left must be a register }
        case right.location.loc of
          LOC_REGISTER,
          LOC_CREGISTER :
            current_asmdata.CurrAsmList.concat(taicpu.op_reg_reg(op,TCGSize2Opsize[opsize],right.location.register,left.location.register));
          LOC_REFERENCE,
          LOC_CREFERENCE :
            begin
              tcgx86(cg).make_simple_ref(current_asmdata.CurrAsmList,right.location.reference);
              current_asmdata.CurrAsmList.concat(taicpu.op_ref_reg(op,TCGSize2Opsize[opsize],right.location.reference,left.location.register));
            end;
          LOC_CONSTANT :
            begin
{$ifdef x86_64}
              { x86_64 only supports signed 32 bits constants directly }
              if (opsize in [OS_S64,OS_64]) and
                 ((right.location.value<low(longint)) or (right.location.value>high(longint))) then
                begin
                  tmpreg:=cg.getintregister(current_asmdata.CurrAsmList,opsize);
                  cg.a_load_const_reg(current_asmdata.CurrAsmList,opsize,right.location.value,tmpreg);
                  current_asmdata.CurrAsmList.concat(taicpu.op_reg_reg(op,TCGSize2Opsize[opsize],tmpreg,left.location.register));
                end
              else
{$endif x86_64}
                current_asmdata.CurrAsmList.concat(taicpu.op_const_reg(op,TCGSize2Opsize[opsize],right.location.value,left.location.register));
            end;
          else
            internalerror(200203232);
        end;
      end;


    function tx86addnode.getresflags(unsigned : boolean) : tresflags;
      begin
         case nodetype of
           equaln : getresflags:=F_E;
           unequaln : getresflags:=F_NE;
          else
           if not(unsigned) then
             begin
                if nf_swapped in flags then
                  case nodetype of
                     ltn : getresflags:=F_G;
                     lten : getresflags:=F_GE;
                     gtn : getresflags:=F_L;
                     gten : getresflags:=F_LE;
                  end
                else
                  case nodetype of
                     ltn : getresflags:=F_L;
                     lten : getresflags:=F_LE;
                     gtn : getresflags:=F_G;
                     gten : getresflags:=F_GE;
                  end;
             end
           else
             begin
                if nf_swapped in flags then
                  case nodetype of
                     ltn : getresflags:=F_A;
                     lten : getresflags:=F_AE;
                     gtn : getresflags:=F_B;
                     gten : getresflags:=F_BE;
                  end
                else
                  case nodetype of
                     ltn : getresflags:=F_B;
                     lten : getresflags:=F_BE;
                     gtn : getresflags:=F_A;
                     gten : getresflags:=F_AE;
                  end;
             end;
         end;
      end;


{*****************************************************************************
                                AddSmallSet
*****************************************************************************}

    procedure tx86addnode.second_addsmallset;
      var
        setbase : aint;
        opdef  : tdef;
        opsize : TCGSize;
        op     : TAsmOp;
        extra_not,
        noswap : boolean;
        all_member_optimization:boolean;

      begin
        pass_left_right;

        noswap:=false;
        extra_not:=false;
        all_member_optimization:=false;
        opdef:=resultdef;
        opsize:=int_cgsize(opdef.size);
        if (left.resultdef.typ=setdef) then
          setbase:=tsetdef(left.resultdef).setbase
        else
          setbase:=tsetdef(right.resultdef).setbase;
        case nodetype of
          addn :
            begin
              { adding elements is not commutative }
              if (nf_swapped in flags) and (left.nodetype=setelementn) then
               swapleftright;
              { are we adding set elements ? }
              if right.nodetype=setelementn then
               begin
                 { no range support for smallsets! }
                 if assigned(tsetelementnode(right).right) then
                   internalerror(43244);
                 { btsb isn't supported }
                 if opsize=OS_8 then
                   begin
                     opsize:=OS_32;
                     opdef:=u32inttype;
                   end;
                 { bts requires both elements to be registers }
                 hlcg.location_force_reg(current_asmdata.CurrAsmList,left.location,left.resultdef,opdef,false);
                 hlcg.location_force_reg(current_asmdata.CurrAsmList,right.location,right.resultdef,opdef,true);
                 register_maybe_adjust_setbase(current_asmdata.CurrAsmList,right.location,setbase);
                 op:=A_BTS;
                 noswap:=true;
               end
              else
               op:=A_OR;
            end;
          symdifn :
            op:=A_XOR;
          muln :
            op:=A_AND;
          subn :
            begin
              op:=A_AND;
              if (not(nf_swapped in flags) and (left.location.loc=LOC_CONSTANT) and (left.location.value=-1)) or
                  ((nf_swapped in flags) and (right.location.loc=LOC_CONSTANT) and (right.location.value=-1)) then
                all_member_optimization:=true;

              if (not(nf_swapped in flags)) and
                 (right.location.loc=LOC_CONSTANT) then
                right.location.value := not(right.location.value)
              else if (nf_swapped in flags) and
                      (left.location.loc=LOC_CONSTANT) then
                left.location.value := not(left.location.value)
              else
                extra_not:=true;
            end;
          xorn :
            op:=A_XOR;
          orn :
            op:=A_OR;
          andn :
            op:=A_AND;
          else
            internalerror(2003042215);
        end;
        if all_member_optimization then
          begin
            {A set expression [0..31]-x can be implemented with a simple NOT.}
            if nf_swapped in flags then
              begin
                { newly swapped also set swapped flag }
                location_swap(left.location,right.location);
                toggleflag(nf_swapped);
              end;
            hlcg.location_force_reg(current_asmdata.currAsmList,right.location,right.resultdef,opdef,false);
            emit_reg(A_NOT,TCGSize2Opsize[opsize],right.location.register);
            location:=right.location;
          end
        else
          begin
            { left must be a register }
            left_must_be_reg(opdef,opsize,noswap);
            emit_generic_code(op,opsize,true,extra_not,false);
            location_freetemp(current_asmdata.CurrAsmList,right.location);

            { left is always a register and contains the result }
            location:=left.location;
          end;

        { fix the changed opsize we did above because of the missing btsb }
        if opsize<>int_cgsize(resultdef.size) then
          hlcg.location_force_reg(current_asmdata.CurrAsmList,location,opdef,hlcg.tcgsize2orddef(int_cgsize(resultdef.size)),false);
      end;


    procedure tx86addnode.second_cmpsmallset;
      var
        opdef  : tdef;
        opsize : TCGSize;
        op     : TAsmOp;
      begin
        pass_left_right;
        opdef:=left.resultdef;
        opsize:=int_cgsize(opdef.size);
        case nodetype of
          equaln,
          unequaln :
            op:=A_CMP;
          lten,gten:
            begin
              if (not(nf_swapped in flags) and (nodetype = lten)) or
                 ((nf_swapped in flags) and (nodetype = gten)) then
                swapleftright;
              hlcg.location_force_reg(current_asmdata.CurrAsmList,left.location,left.resultdef,opdef,false);
              emit_op_right_left(A_AND,opsize);
              op:=A_CMP;
              { warning: ugly hack, we need a JE so change the node to equaln }
              nodetype:=equaln;
            end;
          else
            internalerror(2003042215);
        end;
        { left must be a register }
        left_must_be_reg(opdef,opsize,false);
        emit_generic_code(op,opsize,true,false,false);
        location_freetemp(current_asmdata.CurrAsmList,right.location);
        location_freetemp(current_asmdata.CurrAsmList,left.location);

        location_reset(location,LOC_FLAGS,OS_NO);
        location.resflags:=getresflags(true);
      end;


{*****************************************************************************
                                AddMMX
*****************************************************************************}

{$ifdef SUPPORT_MMX}
    procedure tx86addnode.second_opmmx;
      var
        op         : TAsmOp;
        cmpop      : boolean;
        mmxbase    : tmmxtype;
        hreg,
        hregister  : tregister;
      begin
        pass_left_right;

        cmpop:=false;
        mmxbase:=mmx_type(left.resultdef);
        location_reset(location,LOC_MMXREGISTER,def_cgsize(resultdef));
        case nodetype of
          addn :
            begin
              if (cs_mmx_saturation in current_settings.localswitches) then
                begin
                   case mmxbase of
                      mmxs8bit:
                        op:=A_PADDSB;
                      mmxu8bit:
                        op:=A_PADDUSB;
                      mmxs16bit,mmxfixed16:
                        op:=A_PADDSW;
                      mmxu16bit:
                        op:=A_PADDUSW;
                   end;
                end
              else
                begin
                   case mmxbase of
                      mmxs8bit,mmxu8bit:
                        op:=A_PADDB;
                      mmxs16bit,mmxu16bit,mmxfixed16:
                        op:=A_PADDW;
                      mmxs32bit,mmxu32bit:
                        op:=A_PADDD;
                   end;
                end;
            end;
          muln :
            begin
               case mmxbase of
                  mmxs16bit,mmxu16bit:
                    op:=A_PMULLW;
                  mmxfixed16:
                    op:=A_PMULHW;
               end;
            end;
          subn :
            begin
              if (cs_mmx_saturation in current_settings.localswitches) then
                begin
                   case mmxbase of
                      mmxs8bit:
                        op:=A_PSUBSB;
                      mmxu8bit:
                        op:=A_PSUBUSB;
                      mmxs16bit,mmxfixed16:
                        op:=A_PSUBSB;
                      mmxu16bit:
                        op:=A_PSUBUSW;
                   end;
                end
              else
                begin
                   case mmxbase of
                      mmxs8bit,mmxu8bit:
                        op:=A_PSUBB;
                      mmxs16bit,mmxu16bit,mmxfixed16:
                        op:=A_PSUBW;
                      mmxs32bit,mmxu32bit:
                        op:=A_PSUBD;
                   end;
                end;
            end;
          xorn:
            op:=A_PXOR;
          orn:
            op:=A_POR;
          andn:
            op:=A_PAND;
          else
            internalerror(2003042214);
        end;

        { left and right no register?  }
        { then one must be demanded    }
        if (left.location.loc<>LOC_MMXREGISTER) then
         begin
           if (right.location.loc=LOC_MMXREGISTER) then
            begin
              location_swap(left.location,right.location);
              toggleflag(nf_swapped);
            end
           else
            begin
              { register variable ? }
              if (left.location.loc=LOC_CMMXREGISTER) then
               begin
                 hregister:=tcgx86(cg).getmmxregister(current_asmdata.CurrAsmList);
                 emit_reg_reg(A_MOVQ,S_NO,left.location.register,hregister);
               end
              else
               begin
                 if not(left.location.loc in [LOC_REFERENCE,LOC_CREFERENCE]) then
                  internalerror(200203245);

                 hregister:=tcgx86(cg).getmmxregister(current_asmdata.CurrAsmList);
                 tcgx86(cg).make_simple_ref(current_asmdata.CurrAsmList,left.location.reference);
                 emit_ref_reg(A_MOVQ,S_NO,left.location.reference,hregister);
               end;

              location_reset(left.location,LOC_MMXREGISTER,OS_NO);
              left.location.register:=hregister;
            end;
         end;

        { at this point, left.location.loc should be LOC_MMXREGISTER }
        if right.location.loc<>LOC_MMXREGISTER then
         begin
           if (nodetype=subn) and (nf_swapped in flags) then
            begin
              hreg:=tcgx86(cg).getmmxregister(current_asmdata.CurrAsmList);
              if right.location.loc=LOC_CMMXREGISTER then
               begin
                 emit_reg_reg(A_MOVQ,S_NO,right.location.register,hreg);
                 emit_reg_reg(op,S_NO,left.location.register,hreg);
               end
              else
               begin
                 if not(left.location.loc in [LOC_REFERENCE,LOC_CREFERENCE]) then
                  internalerror(200203247);
                 tcgx86(cg).make_simple_ref(current_asmdata.CurrAsmList,right.location.reference);
                 emit_ref_reg(A_MOVQ,S_NO,right.location.reference,hreg);
                 emit_reg_reg(op,S_NO,left.location.register,hreg);
               end;
               location.register:=hreg;
            end
           else
            begin
              if (right.location.loc=LOC_CMMXREGISTER) then
                emit_reg_reg(op,S_NO,right.location.register,left.location.register)
              else
               begin
                 if not(right.location.loc in [LOC_REFERENCE,LOC_CREFERENCE]) then
                  internalerror(200203246);
                 tcgx86(cg).make_simple_ref(current_asmdata.CurrAsmList,right.location.reference);
                 emit_ref_reg(op,S_NO,right.location.reference,left.location.register);
               end;
              location.register:=left.location.register;
            end;
          end
        else
          begin
            { right.location=LOC_MMXREGISTER }
            if (nodetype=subn) and (nf_swapped in flags) then
             begin
               emit_reg_reg(op,S_NO,left.location.register,right.location.register);
               location_swap(left.location,right.location);
               toggleflag(nf_swapped);
             end
            else
             begin
               emit_reg_reg(op,S_NO,right.location.register,left.location.register);
             end;
            location.register:=left.location.register;
          end;

        location_freetemp(current_asmdata.CurrAsmList,right.location);
        if cmpop then
          location_freetemp(current_asmdata.CurrAsmList,left.location);
      end;
{$endif SUPPORT_MMX}


{*****************************************************************************
                                AddFloat
*****************************************************************************}

    procedure tx86addnode.second_addfloatsse;
      var
        op : topcg;
        sqr_sum : boolean;
        tmp : tnode;
      begin
        sqr_sum:=false;
        if (current_settings.fputype>=fpu_sse3) and
           use_vectorfpu(resultdef) and
           (nodetype in [addn,subn]) and
          (left.nodetype=inlinen) and (tinlinenode(left).inlinenumber=in_sqr_real) and
          (right.nodetype=inlinen) and (tinlinenode(right).inlinenumber=in_sqr_real) then
          begin
            sqr_sum:=true;
            tmp:=tinlinenode(left).left;
            tinlinenode(left).left:=nil;
            left.free;
            left:=tmp;

            tmp:=tinlinenode(right).left;
            tinlinenode(right).left:=nil;
            right.free;
            right:=tmp;
          end;

        pass_left_right;
        check_left_and_right_fpureg(false);

        if (nf_swapped in flags) then
          { can't use swapleftright if both are on the fpu stack, since then }
          { both are "R_ST" -> nothing would change -> manually switch       }
          if (left.location.loc = LOC_FPUREGISTER) and
             (right.location.loc = LOC_FPUREGISTER) then
            emit_none(A_FXCH,S_NO)
          else
            swapleftright;

        case nodetype of
          addn :
            op:=OP_ADD;
          muln :
            op:=OP_MUL;
          subn :
            op:=OP_SUB;
          slashn :
            op:=OP_DIV;
          else
            internalerror(200312231);
        end;

        location_reset(location,LOC_MMREGISTER,def_cgsize(resultdef));

        if sqr_sum then
          begin
            if nf_swapped in flags then
              swapleftright;

            location_force_mmregscalar(current_asmdata.CurrAsmList,left.location,false);
            location_force_mmregscalar(current_asmdata.CurrAsmList,right.location,true);
            location:=left.location;
            if is_double(resultdef) then
              begin
                current_asmdata.CurrAsmList.concat(taicpu.op_const_reg_reg(A_SHUFPD,S_NO,%00,right.location.register,location.register));
                current_asmdata.CurrAsmList.concat(taicpu.op_reg_reg(A_MULPD,S_NO,location.register,location.register));
                case nodetype of
                  addn:
                    current_asmdata.CurrAsmList.concat(taicpu.op_reg_reg(A_HADDPD,S_NO,location.register,location.register));
                  subn:
                    current_asmdata.CurrAsmList.concat(taicpu.op_reg_reg(A_HSUBPD,S_NO,location.register,location.register));
                  else
                    internalerror(201108162);
                end;
              end
            else
              begin
                current_asmdata.CurrAsmList.concat(taicpu.op_reg_reg(A_UNPCKLPS,S_NO,right.location.register,location.register));
                { ensure that bits 64..127 contain valid values }
                current_asmdata.CurrAsmList.concat(taicpu.op_const_reg_reg(A_SHUFPD,S_NO,%00,location.register,location.register));
                { the data is now in bits 0..32 and 64..95 }
                current_asmdata.CurrAsmList.concat(taicpu.op_reg_reg(A_MULPS,S_NO,location.register,location.register));
                case nodetype of
                  addn:
                    begin
                      current_asmdata.CurrAsmList.concat(taicpu.op_reg_reg(A_HADDPS,S_NO,location.register,location.register));
                    end;
                  subn:
                    begin
                      current_asmdata.CurrAsmList.concat(taicpu.op_reg_reg(A_HSUBPS,S_NO,location.register,location.register));
                    end;
                  else
                    internalerror(201108163);
                end;
              end
          end
        { we can use only right as left operand if the operation is commutative }
        else if (right.location.loc=LOC_MMREGISTER) and (op in [OP_ADD,OP_MUL]) then
          begin
            location.register:=right.location.register;
            { force floating point reg. location to be written to memory,
              we don't force it to mm register because writing to memory
              allows probably shorter code because there is no direct fpu->mm register
              copy instruction
            }
            if left.location.loc in [LOC_FPUREGISTER,LOC_CFPUREGISTER] then
              hlcg.location_force_mem(current_asmdata.CurrAsmList,left.location,left.resultdef);
            cg.a_opmm_loc_reg(current_asmdata.CurrAsmList,op,location.size,left.location,location.register,mms_movescalar);
          end
        else
          begin
            if (nf_swapped in flags) then
              swapleftright;

            location_force_mmregscalar(current_asmdata.CurrAsmList,left.location,false);
            location.register:=left.location.register;
            { force floating point reg. location to be written to memory,
              we don't force it to mm register because writing to memory
              allows probably shorter code because there is no direct fpu->mm register
              copy instruction
            }
            if right.location.loc in [LOC_FPUREGISTER,LOC_CFPUREGISTER] then
              hlcg.location_force_mem(current_asmdata.CurrAsmList,right.location,right.resultdef);
            cg.a_opmm_loc_reg(current_asmdata.CurrAsmList,op,location.size,right.location,location.register,mms_movescalar);
          end;
      end;


    procedure tx86addnode.second_cmpfloatsse;
      var
        op : tasmop;
      begin
        if is_single(left.resultdef) then
          op:=A_COMISS
        else if is_double(left.resultdef) then
          op:=A_COMISD
        else
          internalerror(200402222);
        pass_left_right;

        location_reset(location,LOC_FLAGS,def_cgsize(resultdef));
        { we can use only right as left operand if the operation is commutative }
        if (right.location.loc=LOC_MMREGISTER) then
          begin
            { force floating point reg. location to be written to memory,
              we don't force it to mm register because writing to memory
              allows probably shorter code because there is no direct fpu->mm register
              copy instruction
            }
            if left.location.loc in [LOC_FPUREGISTER,LOC_CFPUREGISTER] then
              hlcg.location_force_mem(current_asmdata.CurrAsmList,left.location,left.resultdef);
            case left.location.loc of
              LOC_REFERENCE,LOC_CREFERENCE:
                begin
                  tcgx86(cg).make_simple_ref(current_asmdata.CurrAsmList,left.location.reference);
                  current_asmdata.CurrAsmList.concat(taicpu.op_ref_reg(op,S_NO,left.location.reference,right.location.register));
                end;
              LOC_MMREGISTER,LOC_CMMREGISTER:
                current_asmdata.CurrAsmList.concat(taicpu.op_reg_reg(op,S_NO,left.location.register,right.location.register));
              else
                internalerror(200402221);
            end;
            if nf_swapped in flags then
              exclude(flags,nf_swapped)
            else
              include(flags,nf_swapped)
          end
        else
          begin
            location_force_mmregscalar(current_asmdata.CurrAsmList,left.location,false);
            { force floating point reg. location to be written to memory,
              we don't force it to mm register because writing to memory
              allows probably shorter code because there is no direct fpu->mm register
              copy instruction
            }
            if right.location.loc in [LOC_FPUREGISTER,LOC_CFPUREGISTER] then
              hlcg.location_force_mem(current_asmdata.CurrAsmList,right.location,right.resultdef);
            case right.location.loc of
              LOC_REFERENCE,LOC_CREFERENCE:
                begin
                  tcgx86(cg).make_simple_ref(current_asmdata.CurrAsmList,right.location.reference);
                  current_asmdata.CurrAsmList.concat(taicpu.op_ref_reg(op,S_NO,right.location.reference,left.location.register));
                end;
              LOC_MMREGISTER,LOC_CMMREGISTER:
                current_asmdata.CurrAsmList.concat(taicpu.op_reg_reg(op,S_NO,right.location.register,left.location.register));
              else
                internalerror(200402223);
            end;
          end;
        location.resflags:=getresflags(true);
      end;


    procedure tx86addnode.second_opvector;
      var
        op : topcg;
      begin
        pass_left_right;
        if (nf_swapped in flags) then
          swapleftright;

        case nodetype of
          addn :
            op:=OP_ADD;
          muln :
            op:=OP_MUL;
          subn :
            op:=OP_SUB;
          slashn :
            op:=OP_DIV;
          else
            internalerror(200610071);
        end;

        if fits_in_mm_register(left.resultdef) then
          begin
            location_reset(location,LOC_MMREGISTER,def_cgsize(resultdef));
            { we can use only right as left operand if the operation is commutative }
            if (right.location.loc=LOC_MMREGISTER) and (op in [OP_ADD,OP_MUL]) then
              begin
                location.register:=right.location.register;
                cg.a_opmm_loc_reg(current_asmdata.CurrAsmList,op,tfloat2tcgsize[tfloatdef(left.resultdef).floattype],left.location,location.register,nil);
              end
            else
              begin
                location_force_mmreg(current_asmdata.CurrAsmList,left.location,false);
                location.register:=left.location.register;
                cg.a_opmm_loc_reg(current_asmdata.CurrAsmList,op,
                  tfloat2tcgsize[tfloatdef(tarraydef(left.resultdef).elementdef).floattype],right.location,location.register,nil);
              end;
          end
        else
          begin
            { not yet supported }
            internalerror(200610072);
          end
      end;


    procedure tx86addnode.second_addfloat;
      var
        op : TAsmOp;
      begin
        if use_vectorfpu(resultdef) then
          begin
            second_addfloatsse;
            exit;
          end;

        pass_left_right;

        case nodetype of
          addn :
            op:=A_FADDP;
          muln :
            op:=A_FMULP;
          subn :
            op:=A_FSUBP;
          slashn :
            op:=A_FDIVP;
          else
            internalerror(2003042214);
        end;

        check_left_and_right_fpureg(true);

        { if we swaped the tree nodes, then use the reverse operator }
        if nf_swapped in flags then
          begin
             if (nodetype=slashn) then
               op:=A_FDIVRP
             else if (nodetype=subn) then
               op:=A_FSUBRP;
          end;

        emit_reg_reg(op,S_NO,NR_ST,NR_ST1);
        tcgx86(cg).dec_fpu_stack;

        location_reset(location,LOC_FPUREGISTER,def_cgsize(resultdef));
        location.register:=NR_ST;
      end;


    procedure tx86addnode.second_cmpfloat;
      var
        resflags   : tresflags;
      begin
        if use_vectorfpu(left.resultdef) or use_vectorfpu(right.resultdef) then
          begin
            second_cmpfloatsse;
            exit;
          end;

        pass_left_right;
        check_left_and_right_fpureg(true);

{$ifndef x86_64}
        if current_settings.cputype<cpu_Pentium2 then
          begin
            emit_none(A_FCOMPP,S_NO);
            tcgx86(cg).dec_fpu_stack;
            tcgx86(cg).dec_fpu_stack;

            { load fpu flags }
            cg.getcpuregister(current_asmdata.CurrAsmList,NR_AX);
            emit_reg(A_FSTSW,S_NO,NR_AX);
            emit_none(A_SAHF,S_NO);
            cg.ungetcpuregister(current_asmdata.CurrAsmList,NR_AX);
            if nf_swapped in flags then
             begin
               case nodetype of
                   equaln : resflags:=F_E;
                 unequaln : resflags:=F_NE;
                      ltn : resflags:=F_A;
                     lten : resflags:=F_AE;
                      gtn : resflags:=F_B;
                     gten : resflags:=F_BE;
               end;
             end
            else
             begin
               case nodetype of
                   equaln : resflags:=F_E;
                 unequaln : resflags:=F_NE;
                      ltn : resflags:=F_B;
                     lten : resflags:=F_BE;
                      gtn : resflags:=F_A;
                     gten : resflags:=F_AE;
               end;
             end;
          end
        else
{$endif x86_64}
          begin
            current_asmdata.CurrAsmList.concat(taicpu.op_reg_reg(A_FCOMIP,S_NO,NR_ST1,NR_ST0));
            { fcomip pops only one fpu register }
            current_asmdata.CurrAsmList.concat(taicpu.op_reg(A_FSTP,S_NO,NR_ST0));
            tcgx86(cg).dec_fpu_stack;
            tcgx86(cg).dec_fpu_stack;

            { load fpu flags }
            if nf_swapped in flags then
             begin
               case nodetype of
                   equaln : resflags:=F_E;
                 unequaln : resflags:=F_NE;
                      ltn : resflags:=F_A;
                     lten : resflags:=F_AE;
                      gtn : resflags:=F_B;
                     gten : resflags:=F_BE;
               end;
             end
            else
             begin
               case nodetype of
                   equaln : resflags:=F_E;
                 unequaln : resflags:=F_NE;
                      ltn : resflags:=F_B;
                     lten : resflags:=F_BE;
                      gtn : resflags:=F_A;
                     gten : resflags:=F_AE;
               end;
             end;
          end;

        location_reset(location,LOC_FLAGS,OS_NO);
        location.resflags:=resflags;
      end;


{*****************************************************************************
                                  Add64bit
*****************************************************************************}

    procedure tx86addnode.second_add64bit;
      begin
{$ifdef cpu64bitalu}
        second_addordinal;
{$else cpu64bitalu}
        { must be implemented separate }
        internalerror(200402042);
{$endif cpu64bitalu}
      end;


    procedure tx86addnode.second_cmp64bit;
      begin
{$ifdef cpu64bitalu}
        second_cmpordinal;
{$else cpu64bitalu}
        { must be implemented separate }
        internalerror(200402043);
{$endif cpu64bitalu}
      end;


{*****************************************************************************
                                  AddOrdinal
*****************************************************************************}

    procedure tx86addnode.second_cmpordinal;
      var
         opdef  : tdef;
         opsize : tcgsize;
         unsigned : boolean;
      begin
         unsigned:=not(is_signed(left.resultdef)) or
                   not(is_signed(right.resultdef));
         opdef:=left.resultdef;
         opsize:=def_cgsize(opdef);

         pass_left_right;

         left_must_be_reg(opdef,opsize,false);
         emit_generic_code(A_CMP,opsize,unsigned,false,false);
         location_freetemp(current_asmdata.CurrAsmList,right.location);
         location_freetemp(current_asmdata.CurrAsmList,left.location);

         location_reset(location,LOC_FLAGS,OS_NO);
         location.resflags:=getresflags(unsigned);
      end;

begin
   caddnode:=tx86addnode;
end.
