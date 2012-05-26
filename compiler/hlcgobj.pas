{
    Copyright (c) 1998-2010 by Florian Klaempfl and Jonas Maebe
    Member of the Free Pascal development team

    This unit implements the basic high level code generator object

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
{# @abstract(Abstract code generator unit)
   Abstract high level code generator unit. This contains the base class
   that either lowers most code to the regular code generator, or that
   has to be implemented/overridden for higher level targets (such as LLVM).
}
unit hlcgobj;

{$i fpcdefs.inc}

{ define hlcginline}

  interface

    uses
       cclasses,globtype,constexp,
       cpubase,cgbase,cgutils,parabase,
       aasmbase,aasmtai,aasmdata,aasmcpu,
       symconst,symtype,symdef,rgobj,
       node
       ;

    type
       tsubsetloadopt = (SL_REG,SL_REGNOSRCMASK,SL_SETZERO,SL_SETMAX);
       {# @abstract(Abstract high level code generator)
          This class implements an abstract instruction generator. All
          methods of this class are generic and are mapped to low level code
          generator methods by default. They have to be overridden for higher
          level targets
       }

       { thlcgobj }

       thlcgobj = class
       public
          {************************************************}
          {                 basic routines                 }
          constructor create;

          {# Initialize the register allocators needed for the codegenerator.}
          procedure init_register_allocators;virtual;
          {# Clean up the register allocators needed for the codegenerator.}
          procedure done_register_allocators;virtual;
          {# Set whether live_start or live_end should be updated when allocating registers, needed when e.g. generating initcode after the rest of the code. }
          procedure set_regalloc_live_range_direction(dir: TRADirection);virtual;
          {# Gets a register suitable to do integer operations on.}
          function getintregister(list:TAsmList;size:tdef):Tregister;virtual;
          {# Gets a register suitable to do integer operations on.}
          function getaddressregister(list:TAsmList;size:tdef):Tregister;virtual;
          function getfpuregister(list:TAsmList;size:tdef):Tregister;virtual;
//        we don't have high level defs yet that translate into all mm cgsizes
//          function getmmregister(list:TAsmList;size:tdef):Tregister;virtual;
          function getflagregister(list:TAsmList;size:tdef):Tregister;virtual;
          function getregisterfordef(list: TAsmList;size:tdef):Tregister;virtual;
          {Does the generic cg need SIMD registers, like getmmxregister? Or should
           the cpu specific child cg object have such a method?}

          function  uses_registers(rt:Tregistertype):boolean; inline;

          procedure do_register_allocation(list:TAsmList;headertai:tai); inline;
          procedure translate_register(var reg : tregister); inline;

          {# Returns the kind of register this type should be loaded in (it does not
             check whether this is actually possible, but if it's loaded in a register
             by the compiler for any purpose other than parameter passing/function
             result loading, this is the register type used }
          function def2regtyp(def: tdef): tregistertype; virtual;
          { # Returns orddef corresponding to size }
          class function tcgsize2orddef(size: tcgsize): torddef; static;

          {# Emit a label to the instruction stream. }
          procedure a_label(list : TAsmList;l : tasmlabel); inline;

          {# Allocates register r by inserting a pai_realloc record }
          procedure a_reg_alloc(list : TAsmList;r : tregister); inline;
          {# Deallocates register r by inserting a pa_regdealloc record}
          procedure a_reg_dealloc(list : TAsmList;r : tregister); inline;
          { Synchronize register, make sure it is still valid }
          procedure a_reg_sync(list : TAsmList;r : tregister); inline;

          {# Pass a parameter, which is located in a register, to a routine.

             This routine should push/send the parameter to the routine, as
             required by the specific processor ABI and routine modifiers.
             It must generate register allocation information for the cgpara in
             case it consists of cpuregisters.

             @param(size size of the operand in the register)
             @param(r register source of the operand)
             @param(cgpara where the parameter will be stored)
          }
          procedure a_load_reg_cgpara(list : TAsmList;size : tdef;r : tregister;const cgpara : TCGPara);virtual;
          {# Pass a parameter, which is a constant, to a routine.

             A generic version is provided. This routine should
             be overridden for optimization purposes if the cpu
             permits directly sending this type of parameter.
             It must generate register allocation information for the cgpara in
             case it consists of cpuregisters.

             @param(size size of the operand in constant)
             @param(a value of constant to send)
             @param(cgpara where the parameter will be stored)
          }
          procedure a_load_const_cgpara(list : TAsmList;tosize : tdef;a : aint;const cgpara : TCGPara);virtual;
          {# Pass the value of a parameter, which is located in memory, to a routine.

             A generic version is provided. This routine should
             be overridden for optimization purposes if the cpu
             permits directly sending this type of parameter.
             It must generate register allocation information for the cgpara in
             case it consists of cpuregisters.

             @param(size size of the operand in constant)
             @param(r Memory reference of value to send)
             @param(cgpara where the parameter will be stored)
          }
          procedure a_load_ref_cgpara(list : TAsmList;size : tdef;const r : treference;const cgpara : TCGPara);virtual;
          {# Pass the value of a parameter, which can be located either in a register or memory location,
             to a routine.

             A generic version is provided.

             @param(l location of the operand to send)
             @param(nr parameter number (starting from one) of routine (from left to right))
             @param(cgpara where the parameter will be stored)
          }
          procedure a_load_loc_cgpara(list : TAsmList;size : tdef; const l : tlocation;const cgpara : TCGPara);virtual;
          {# Pass the address of a reference to a routine. This routine
             will calculate the address of the reference, and pass this
             calculated address as a parameter.
             It must generate register allocation information for the cgpara in
             case it consists of cpuregisters.

             A generic version is provided. This routine should
             be overridden for optimization purposes if the cpu
             permits directly sending this type of parameter.

             @param(fromsize type of the reference we are taking the address of)
             @param(tosize type of the pointer that we get as a result)
             @param(r reference to get address from)
          }
          procedure a_loadaddr_ref_cgpara(list : TAsmList;fromsize, tosize : tdef;const r : treference;const cgpara : TCGPara);virtual;

          { Remarks:
            * If a method specifies a size you have only to take care
              of that number of bits, i.e. load_const_reg with OP_8 must
              only load the lower 8 bit of the specified register
              the rest of the register can be undefined
              if  necessary the compiler will call a method
              to zero or sign extend the register
            * The a_load_XX_XX with OP_64 needn't to be
              implemented for 32 bit
              processors, the code generator takes care of that
            * the addr size is for work with the natural pointer
              size
            * the procedures without fpu/mm are only for integer usage
            * normally the first location is the source and the
              second the destination
          }

          {# Emits instruction to call the method specified by symbol name.
             This routine must be overridden for each new target cpu.
          }
          procedure a_call_name(list : TAsmList;pd : tprocdef;const s : TSymStr; weak: boolean);virtual;abstract;
          procedure a_call_reg(list : TAsmList;pd : tabstractprocdef;reg : tregister);virtual;abstract;
          procedure a_call_ref(list : TAsmList;pd : tabstractprocdef;const ref : treference);virtual;
          { same as a_call_name, might be overridden on certain architectures to emit
            static calls without usage of a got trampoline }
          procedure a_call_name_static(list : TAsmList;pd : tprocdef;const s : TSymStr);virtual;
          { same as a_call_name, might be overridden on certain architectures to emit
            special static calls for inherited methods }
          procedure a_call_name_inherited(list : TAsmList;pd : tprocdef;const s : TSymStr);virtual;

          { move instructions }
          procedure a_load_const_reg(list : TAsmList;tosize : tdef;a : aint;register : tregister);virtual;abstract;
          procedure a_load_const_ref(list : TAsmList;tosize : tdef;a : aint;const ref : treference);virtual;
          procedure a_load_const_loc(list : TAsmList;tosize : tdef;a : aint;const loc : tlocation);virtual;
          procedure a_load_reg_ref(list : TAsmList;fromsize, tosize : tdef;register : tregister;const ref : treference);virtual;abstract;
          procedure a_load_reg_ref_unaligned(list : TAsmList;fromsize, tosize : tdef;register : tregister;const ref : treference);virtual;
          procedure a_load_reg_reg(list : TAsmList;fromsize, tosize : tdef;reg1,reg2 : tregister);virtual;abstract;
          procedure a_load_reg_loc(list : TAsmList;fromsize, tosize : tdef;reg : tregister;const loc: tlocation);virtual;
          procedure a_load_ref_reg(list : TAsmList;fromsize, tosize : tdef;const ref : treference;register : tregister);virtual;abstract;
          procedure a_load_ref_reg_unaligned(list : TAsmList;fromsize, tosize : tdef;const ref : treference;register : tregister);virtual;
          procedure a_load_ref_ref(list : TAsmList;fromsize, tosize : tdef;const sref : treference;const dref : treference);virtual;
          procedure a_load_loc_reg(list : TAsmList;fromsize, tosize : tdef; const loc: tlocation; reg : tregister);virtual;
          procedure a_load_loc_ref(list : TAsmList;fromsize, tosize: tdef; const loc: tlocation; const ref : treference);virtual;
          procedure a_load_loc_subsetreg(list : TAsmList;fromsize, tosubsetsize: tdef; const loc: tlocation; const sreg : tsubsetregister);virtual;
          procedure a_load_loc_subsetref(list : TAsmList;fromsize, tosubsetsize: tdef; const loc: tlocation; const sref : tsubsetreference);virtual;
          procedure a_loadaddr_ref_reg(list : TAsmList;fromsize, tosize : tdef;const ref : treference;r : tregister);virtual;abstract;

          { For subsetreg/ref, the def is the size of the packed element. The
            size of the register that holds the data is a tcgsize, and hence
            always must be an orddef of the corresponding size in practice }
          procedure a_load_subsetreg_reg(list : TAsmList; subsetsize, tosize: tdef; const sreg: tsubsetregister; destreg: tregister); virtual;
          procedure a_load_reg_subsetreg(list : TAsmList; fromsize, tosubsetsize: tdef; fromreg: tregister; const sreg: tsubsetregister); virtual;
          procedure a_load_subsetreg_subsetreg(list: TAsmlist; fromsubsetsize, tosubsetsize : tdef; const fromsreg, tosreg: tsubsetregister); virtual;
          procedure a_load_subsetreg_ref(list : TAsmList; fromsubsetsize, tosize: tdef; const sreg: tsubsetregister; const destref: treference); virtual;
          procedure a_load_ref_subsetreg(list : TAsmList; fromsize, tosubsetsize: tdef; const fromref: treference; const sreg: tsubsetregister); virtual;
          procedure a_load_const_subsetreg(list: TAsmlist; tosubsetsize: tdef; a: aint; const sreg: tsubsetregister); virtual;
          procedure a_load_subsetreg_loc(list: TAsmlist; fromsubsetsize, tosize: tdef; const sreg: tsubsetregister; const loc: tlocation); virtual;

          procedure a_load_subsetref_reg(list : TAsmList; fromsubsetsize, tosize: tdef; const sref: tsubsetreference; destreg: tregister); virtual;
          procedure a_load_reg_subsetref(list : TAsmList; fromsize, tosubsetsize: tdef; fromreg: tregister; const sref: tsubsetreference); virtual;
          procedure a_load_subsetref_subsetref(list: TAsmlist; fromsubsetsize, tosubsetsize : tdef; const fromsref, tosref: tsubsetreference); virtual;
          procedure a_load_subsetref_ref(list : TAsmList; fromsubsetsize, tosize: tdef; const sref: tsubsetreference; const destref: treference); virtual;
          procedure a_load_ref_subsetref(list : TAsmList; fromsize, tosubsetsize: tdef; const fromref: treference; const sref: tsubsetreference); virtual;
          procedure a_load_const_subsetref(list: TAsmlist; tosubsetsize: tdef; a: tcgint; const sref: tsubsetreference); virtual;
          procedure a_load_subsetref_loc(list: TAsmlist; fromsubsetsize, tosize: tdef; const sref: tsubsetreference; const loc: tlocation); virtual;
          procedure a_load_subsetref_subsetreg(list: TAsmlist; fromsubsetsize, tosubsetsize : tdef; const fromsref: tsubsetreference; const tosreg: tsubsetregister); virtual;
          procedure a_load_subsetreg_subsetref(list: TAsmlist; fromsubsetsize, tosubsetsize : tdef; const fromsreg: tsubsetregister; const tosref: tsubsetreference); virtual;

          { bit test instructions }
          procedure a_bit_test_reg_reg_reg(list : TAsmList; bitnumbersize,valuesize,destsize: tdef;bitnumber,value,destreg: tregister); virtual;
          procedure a_bit_test_const_ref_reg(list: TAsmList; fromsize, destsize: tdef; bitnumber: aint; const ref: treference; destreg: tregister); virtual;
          procedure a_bit_test_const_reg_reg(list: TAsmList; setregsize, destsize: tdef; bitnumber: aint; setreg, destreg: tregister); virtual;
          procedure a_bit_test_const_subsetreg_reg(list: TAsmList; fromsubsetsize, destsize: tdef; bitnumber: aint; const setreg: tsubsetregister; destreg: tregister); virtual;
          procedure a_bit_test_reg_ref_reg(list: TAsmList; bitnumbersize, refsize, destsize: tdef; bitnumber: tregister; const ref: treference; destreg: tregister); virtual;
          procedure a_bit_test_reg_loc_reg(list: TAsmList; bitnumbersize, locsize, destsize: tdef; bitnumber: tregister; const loc: tlocation; destreg: tregister);virtual;
          procedure a_bit_test_const_loc_reg(list: TAsmList; locsize, destsize: tdef; bitnumber: aint; const loc: tlocation; destreg: tregister);virtual;

          { bit set/clear instructions }
          procedure a_bit_set_reg_reg(list : TAsmList; doset: boolean; bitnumbersize, destsize: tdef; bitnumber,dest: tregister); virtual;
          procedure a_bit_set_const_ref(list: TAsmList; doset: boolean;destsize: tdef; bitnumber: aint; const ref: treference); virtual;
          procedure a_bit_set_const_reg(list: TAsmList; doset: boolean; destsize: tdef; bitnumber: aint; destreg: tregister); virtual;
          procedure a_bit_set_const_subsetreg(list: TAsmList; doset: boolean; destsize: tdef; bitnumber: aint; const destreg: tsubsetregister); virtual;
          procedure a_bit_set_reg_ref(list: TAsmList; doset: boolean; fromsize, tosize: tdef; bitnumber: tregister; const ref: treference); virtual;
          procedure a_bit_set_reg_loc(list: TAsmList; doset: boolean; regsize, tosize: tdef; bitnumber: tregister; const loc: tlocation);virtual;
          procedure a_bit_set_const_loc(list: TAsmList; doset: boolean; tosize: tdef; bitnumber: aint; const loc: tlocation);virtual;

         protected
           procedure get_subsetref_load_info(const sref: tsubsetreference; out loadsize: torddef; out extra_load: boolean);
           procedure a_load_subsetref_regs_noindex(list: TAsmList; subsetsize: tdef; loadbitsize: byte; const sref: tsubsetreference; valuereg, extra_value_reg: tregister); virtual;
           procedure a_load_subsetref_regs_index(list: TAsmList; subsetsize: tdef; loadbitsize: byte; const sref: tsubsetreference; valuereg: tregister); virtual;

           procedure a_load_regconst_subsetref_intern(list : TAsmList; fromsize, subsetsize: tdef; fromreg: tregister; const sref: tsubsetreference; slopt: tsubsetloadopt); virtual;
           procedure a_load_regconst_subsetreg_intern(list : TAsmList; fromsize, subsetsize: tdef; fromreg: tregister; const sreg: tsubsetregister; slopt: tsubsetloadopt); virtual;

           { return a subsetref that represents bit "bitnumber" in ref, if ref
             has the type "refdef". The subsetref must be addressable via
             (unsigned) 8 bit access, unless all the *_bit_* methods are
             overloaded and use something else. }
           function get_bit_const_ref_sref(bitnumber: tcgint; refdef: tdef; const ref: treference): tsubsetreference;
           function get_bit_const_reg_sreg(setregsize: tdef; bitnumber: tcgint; setreg: tregister): tsubsetregister;
           function get_bit_reg_ref_sref(list: TAsmList; bitnumbersize, refsize: tdef; bitnumber: tregister; const ref: treference): tsubsetreference;
         public

          { bit scan instructions (still need transformation to thlcgobj) }
          procedure a_bit_scan_reg_reg(list: TAsmList; reverse: boolean; size: tdef; src, dst: tregister); virtual; abstract;

          { fpu move instructions }
          procedure a_loadfpu_reg_reg(list: TAsmList; fromsize, tosize: tdef; reg1, reg2: tregister); virtual; abstract;
          procedure a_loadfpu_ref_reg(list: TAsmList; fromsize, tosize: tdef; const ref: treference; reg: tregister); virtual; abstract;
          procedure a_loadfpu_reg_ref(list: TAsmList; fromsize, tosize: tdef; reg: tregister; const ref: treference); virtual; abstract;
          procedure a_loadfpu_ref_ref(list: TAsmList; fromsize, tosize: tdef; const ref1,ref2: treference);virtual;
          procedure a_loadfpu_loc_reg(list: TAsmList; fromsize, tosize: tdef; const loc: tlocation; const reg: tregister);virtual;
          procedure a_loadfpu_reg_loc(list: TAsmList; fromsize, tosize: tdef; const reg: tregister; const loc: tlocation);virtual;
          procedure a_loadfpu_reg_cgpara(list : TAsmList;fromsize: tdef;const r : tregister;const cgpara : TCGPara);virtual;
          procedure a_loadfpu_ref_cgpara(list : TAsmList;fromsize : tdef;const ref : treference;const cgpara : TCGPara);virtual;

          { vector register move instructions }
//        we don't have high level defs yet that translate into all mm cgsizes
{
          procedure a_loadmm_reg_reg(list: TAsmList; fromsize, tosize: tdef;reg1, reg2: tregister;shuffle : pmmshuffle); virtual;
          procedure a_loadmm_ref_reg(list: TAsmList; fromsize, tosize: tdef;const ref: treference; reg: tregister;shuffle : pmmshuffle); virtual;
          procedure a_loadmm_reg_ref(list: TAsmList; fromsize, tosize: tdef;reg: tregister; const ref: treference;shuffle : pmmshuffle); virtual;
}
          { required for subsetreg/ref; still tcgsize rather than tdef because of reason mentioned above }
          procedure a_loadmm_loc_reg(list: TAsmList; fromsize, tosize: tcgsize; const loc: tlocation; const reg: tregister;shuffle : pmmshuffle);virtual; abstract;
{
          procedure a_loadmm_reg_loc(list: TAsmList; fromsize, tosize: tdef; const reg: tregister; const loc: tlocation;shuffle : pmmshuffle);virtual;
          procedure a_loadmm_reg_cgpara(list: TAsmList; fromsize: tdef; reg: tregister;const cgpara : TCGPara;shuffle : pmmshuffle); virtual;
          procedure a_loadmm_ref_cgpara(list: TAsmList; fromsize: tdef; const ref: treference;const cgpara : TCGPara;shuffle : pmmshuffle); virtual;
          procedure a_loadmm_loc_cgpara(list: TAsmList; fromsize: tdef; const loc: tlocation; const cgpara : TCGPara;shuffle : pmmshuffle); virtual;
          procedure a_opmm_reg_reg(list: TAsmList; Op: TOpCG; size : tdef;src,dst: tregister;shuffle : pmmshuffle); virtual;
          procedure a_opmm_ref_reg(list: TAsmList; Op: TOpCG; size : tdef;const ref: treference; reg: tregister;shuffle : pmmshuffle); virtual;
          procedure a_opmm_loc_reg(list: TAsmList; Op: TOpCG; size : tdef;const loc: tlocation; reg: tregister;shuffle : pmmshuffle); virtual;
          procedure a_opmm_reg_ref(list: TAsmList; Op: TOpCG; size : tdef;reg: tregister;const ref: treference; shuffle : pmmshuffle); virtual;
}
//        we don't have high level defs yet that translate into all mm cgsizes
//          procedure a_loadmm_intreg_reg(list: TAsmList; fromsize, tosize : tdef; intreg, mmreg: tregister; shuffle: pmmshuffle); virtual;
//          procedure a_loadmm_reg_intreg(list: TAsmList; fromsize, tosize : tdef; mmreg, intreg: tregister; shuffle : pmmshuffle); virtual;

          { basic arithmetic operations }
          { note: for operators which require only one argument (not, neg), use }
          { the op_reg_reg, op_reg_ref or op_reg_loc methods and keep in mind   }
          { that in this case the *second* operand is used as both source and   }
          { destination (JM)                                                    }
          procedure a_op_const_reg(list : TAsmList; Op: TOpCG; size: tdef; a: Aint; reg: TRegister); virtual; abstract;
          procedure a_op_const_ref(list : TAsmList; Op: TOpCG; size: tdef; a: Aint; const ref: TReference); virtual;
          procedure a_op_const_subsetreg(list : TAsmList; Op : TOpCG; size, subsetsize : tdef; a : aint; const sreg: tsubsetregister); virtual;
          procedure a_op_const_subsetref(list : TAsmList; Op : TOpCG; size, subsetsize : tdef; a : aint; const sref: tsubsetreference); virtual;
          procedure a_op_const_loc(list : TAsmList; Op: TOpCG; size: tdef; a: Aint; const loc: tlocation);virtual;
          procedure a_op_reg_reg(list : TAsmList; Op: TOpCG; size: tdef; reg1, reg2: TRegister); virtual; abstract;
          procedure a_op_reg_ref(list : TAsmList; Op: TOpCG; size: tdef; reg: TRegister; const ref: TReference); virtual;
          procedure a_op_ref_reg(list : TAsmList; Op: TOpCG; size: tdef; const ref: TReference; reg: TRegister); virtual;
          procedure a_op_reg_subsetreg(list: TAsmList; Op: TOpCG; opsize, destsubsetsize: tdef; reg: TRegister; const sreg: tsubsetregister); virtual;
          procedure a_op_reg_subsetref(list: TAsmList; Op: TOpCG; opsize, destsubsetsize: tdef; reg: TRegister; const sref: tsubsetreference); virtual;
          procedure a_op_reg_loc(list : TAsmList; Op: TOpCG; size: tdef; reg: tregister; const loc: tlocation);virtual;
          procedure a_op_ref_loc(list : TAsmList; Op: TOpCG; size: tdef; const ref: TReference; const loc: tlocation);virtual;

          { trinary operations for processors that support them, 'emulated' }
          { on others. None with "ref" arguments since I don't think there  }
          { are any processors that support it (JM)                         }
          procedure a_op_const_reg_reg(list: TAsmList; op: TOpCg; size: tdef; a: aint; src, dst: tregister); virtual;
          procedure a_op_reg_reg_reg(list: TAsmList; op: TOpCg; size: tdef; src1, src2, dst: tregister); virtual;
          procedure a_op_const_reg_reg_checkoverflow(list: TAsmList; op: TOpCg; size: tdef; a: aint; src, dst: tregister;setflags : boolean;var ovloc : tlocation); virtual;
          procedure a_op_reg_reg_reg_checkoverflow(list: TAsmList; op: TOpCg; size: tdef; src1, src2, dst: tregister;setflags : boolean;var ovloc : tlocation); virtual;

          {  comparison operations }
          procedure a_cmp_const_reg_label(list : TAsmList;size : tdef;cmp_op : topcmp;a : aint;reg : tregister;
            l : tasmlabel);virtual;
          procedure a_cmp_const_ref_label(list : TAsmList;size : tdef;cmp_op : topcmp;a : aint;const ref : treference;
            l : tasmlabel); virtual;
          procedure a_cmp_const_loc_label(list: TAsmList; size: tdef;cmp_op: topcmp; a: aint; const loc: tlocation;
            l : tasmlabel);virtual;
          procedure a_cmp_reg_reg_label(list : TAsmList;size : tdef;cmp_op : topcmp;reg1,reg2 : tregister;l : tasmlabel); virtual; abstract;
          procedure a_cmp_ref_reg_label(list : TAsmList;size : tdef;cmp_op : topcmp; const ref: treference; reg : tregister; l : tasmlabel); virtual;
          procedure a_cmp_reg_ref_label(list : TAsmList;size : tdef;cmp_op : topcmp;reg : tregister; const ref: treference; l : tasmlabel); virtual;
          procedure a_cmp_subsetreg_reg_label(list: TAsmList; fromsubsetsize, cmpsize: tdef; cmp_op: topcmp; const sreg: tsubsetregister; reg: tregister; l: tasmlabel); virtual;
          procedure a_cmp_subsetref_reg_label(list: TAsmList; fromsubsetsize, cmpsize: tdef; cmp_op: topcmp; const sref: tsubsetreference; reg: tregister; l: tasmlabel); virtual;

          procedure a_cmp_loc_reg_label(list : TAsmList;size : tdef;cmp_op : topcmp; const loc: tlocation; reg : tregister; l : tasmlabel);virtual;
          procedure a_cmp_reg_loc_label(list : TAsmList;size : tdef;cmp_op : topcmp; reg: tregister; const loc: tlocation; l : tasmlabel);
          procedure a_cmp_ref_loc_label(list: TAsmList; size: tdef;cmp_op: topcmp; const ref: treference; const loc: tlocation; l : tasmlabel);virtual;

          procedure a_jmp_always(list : TAsmList;l: tasmlabel); virtual;abstract;
{$ifdef cpuflags}
          procedure a_jmp_flags(list : TAsmList;const f : TResFlags;l: tasmlabel); virtual; abstract;

          {# Depending on the value to check in the flags, either sets the register reg to one (if the flag is set)
             or zero (if the flag is cleared). The size parameter indicates the destination size register.
          }
          procedure g_flags2reg(list: TAsmList; size: tdef; const f: tresflags; reg: TRegister); virtual; abstract;
          procedure g_flags2ref(list: TAsmList; size: tdef; const f: tresflags; const ref:TReference); virtual; abstract;
{$endif cpuflags}

//          procedure g_maybe_testself(list : TAsmList;reg:tregister);
//          procedure g_maybe_testvmt(list : TAsmList;reg:tregister;objdef:tobjectdef);
          {# This should emit the opcode to copy len bytes from the source
             to destination.

             It must be overridden for each new target processor.

             @param(source Source reference of copy)
             @param(dest Destination reference of copy)

          }
          procedure g_concatcopy(list : TAsmList;size: tdef; const source,dest : treference);virtual;
          {# This should emit the opcode to copy len bytes from the an unaligned source
             to destination.

             It must be overridden for each new target processor.

             @param(source Source reference of copy)
             @param(dest Destination reference of copy)

          }
          procedure g_concatcopy_unaligned(list : TAsmList;size: tdef; const source,dest : treference);virtual;
          {# This should emit the opcode to a shortrstring from the source
             to destination.

             @param(source Source reference of copy)
             @param(dest Destination reference of copy)

          }
          procedure g_copyshortstring(list : TAsmList;const source,dest : treference;strdef:tstringdef);virtual;abstract;
          procedure g_copyvariant(list : TAsmList;const source,dest : treference;vardef:tvariantdef);virtual;abstract;

          procedure g_incrrefcount(list : TAsmList;t: tdef; const ref: treference);virtual;abstract;
          procedure g_initialize(list : TAsmList;t : tdef;const ref : treference);virtual;abstract;
          procedure g_finalize(list : TAsmList;t : tdef;const ref : treference);virtual;abstract;
          procedure g_array_rtti_helper(list: TAsmList; t: tdef; const ref: treference; const highloc: tlocation;
            const name: string);virtual;abstract;

          {# Generates range checking code. It is to note
             that this routine does not need to be overridden,
             as it takes care of everything.

             @param(p Node which contains the value to check)
             @param(todef Type definition of node to range check)
          }
          procedure g_rangecheck(list: TAsmList; const l:tlocation; fromdef,todef: tdef); virtual;

          {# Generates overflow checking code for a node }
          procedure g_overflowcheck(list: TAsmList; const Loc:tlocation; def:tdef); virtual; abstract;
          procedure g_overflowCheck_loc(List:TAsmList;const Loc:TLocation;def:TDef;var ovloc : tlocation);virtual; abstract;

          procedure g_copyvaluepara_openarray(list : TAsmList;const ref:treference;const lenloc:tlocation;arrdef: tarraydef;destreg:tregister);virtual;abstract;
          procedure g_releasevaluepara_openarray(list : TAsmList;arrdef: tarraydef;const l:tlocation);virtual;abstract;

          {# Emits instructions when compilation is done in profile
             mode (this is set as a command line option). The default
             behavior does nothing, should be overridden as required.
          }
          procedure g_profilecode(list : TAsmList);virtual;
          {# Emits instruction for allocating @var(size) bytes at the stackpointer

             @param(size Number of bytes to allocate)
          }
          procedure g_stackpointer_alloc(list : TAsmList;size : longint);virtual; abstract;
          {# Emits instruction for allocating the locals in entry
             code of a routine. This is one of the first
             routine called in @var(genentrycode).

             @param(localsize Number of bytes to allocate as locals)
          }
          procedure g_proc_entry(list : TAsmList;localsize : longint;nostackframe:boolean);virtual; abstract;
          {# Emits instructions for returning from a subroutine.
             Should also restore the framepointer and stack.

             @param(parasize  Number of bytes of parameters to deallocate from stack)
          }
          procedure g_proc_exit(list : TAsmList;parasize:longint;nostackframe:boolean);virtual; abstract;

          procedure g_intf_wrapper(list: TAsmList; procdef: tprocdef; const labelname: string; ioffset: longint);virtual; abstract;
          procedure g_adjust_self_value(list:TAsmList;procdef: tprocdef;ioffset: aint);virtual; abstract;

          { generate a stub which only purpose is to pass control the given external method,
          setting up any additional environment before doing so (if required).

          The default implementation issues a jump instruction to the external name. }
//          procedure g_external_wrapper(list : TAsmList; procdef: tprocdef; const externalname: string); virtual;

         protected
          procedure g_allocload_reg_reg(list: TAsmList; regsize: tdef; const fromreg: tregister; out toreg: tregister; regtyp: tregistertype);
         public
          { create "safe copy" of a tlocation that can be used later: all
            registers used in the tlocation are copied to new ones, so that
            even if the original ones change, things stay the same (except if
            the original location was already a register, then the register is
            kept). Must only be used on lvalue locations.
            It's intended as some kind of replacement for a_loadaddr_ref_reg()
            for targets without pointers. }
          procedure g_reference_loc(list: TAsmList; def: tdef; const fromloc: tlocation; out toloc: tlocation); virtual;


          { routines migrated from ncgutil }

          procedure location_force_reg(list:TAsmList;var l:tlocation;src_size,dst_size:tdef;maybeconst:boolean);virtual;
          procedure location_force_fpureg(list:TAsmList;var l: tlocation;size: tdef;maybeconst:boolean);virtual;
          procedure location_force_mem(list:TAsmList;var l:tlocation;size:tdef);virtual;
//          procedure location_force_mmregscalar(list:TAsmList;var l: tlocation;size:tdef;maybeconst:boolean);virtual;abstract;
//          procedure location_force_mmreg(list:TAsmList;var l: tlocation;size:tdef;maybeconst:boolean);virtual;abstract;

          { Retrieve the location of the data pointed to in location l, when the location is
            a register it is expected to contain the address of the data }
          procedure location_get_data_ref(list:TAsmList;def: tdef; const l:tlocation;var ref:treference;loadref:boolean; alignment: longint);virtual;

          procedure maketojumpbool(list:TAsmList; p : tnode);virtual;

          procedure gen_proc_symbol(list:TAsmList);virtual;
          procedure gen_proc_symbol_end(list:TAsmList);virtual;

          procedure gen_initialize_code(list:TAsmList);virtual;
          procedure gen_finalize_code(list:TAsmList);virtual;

          procedure gen_entry_code(list:TAsmList);virtual;
          procedure gen_exit_code(list:TAsmList);virtual;

         protected
          { helpers called by gen_initialize_code/gen_finalize_code }
          procedure inittempvariables(list:TAsmList);virtual;
          procedure initialize_data(p:TObject;arg:pointer);virtual;
          procedure finalizetempvariables(list:TAsmList);virtual;
          procedure initialize_regvars(p:TObject;arg:pointer);virtual;
          procedure finalize_sym(asmlist:TAsmList;sym:tsym);virtual;
          { generates the code for finalisation of local variables }
          procedure finalize_local_vars(p:TObject;arg:pointer);virtual;
          { generates the code for finalization of static symtable and
            all local (static) typed consts }
          procedure finalize_static_data(p:TObject;arg:pointer);virtual;
          { generates the code for decrementing the reference count of parameters }
          procedure final_paras(p:TObject;arg:pointer);
         public

          procedure gen_load_para_value(list:TAsmList);virtual;
         protected
          { helpers called by gen_load_para_value }
          procedure g_copyvalueparas(p:TObject;arg:pointer);virtual;
          procedure gen_loadfpu_loc_cgpara(list: TAsmList; size: tdef; const l: tlocation;const cgpara: tcgpara;locintsize: longint);virtual;
          procedure init_paras(p:TObject;arg:pointer);
         protected
          { Some targets have to put "something" in the function result
            location if it's not initialised by the Pascal code, e.g.
            stack-based architectures. By default it does nothing }
          procedure gen_load_uninitialized_function_result(list: TAsmList; pd: tprocdef; resdef: tdef; const resloc: tcgpara);virtual;
         public
          { load a tlocation into a cgpara }
          procedure gen_load_loc_cgpara(list: TAsmList; vardef: tdef; const l: tlocation; const cgpara: tcgpara);virtual;

          { load a cgpara into a tlocation }
          procedure gen_load_cgpara_loc(list: TAsmList; vardef: tdef; const para: TCGPara; var destloc: tlocation; reusepara: boolean);virtual;

          { load the function return value into the ABI-defined function return location }
          procedure gen_load_return_value(list:TAsmList);virtual;

          { extras refactored from other units }

          { queue the code/data generated for a procedure for writing out to
            the assembler/object file }
          procedure record_generated_code_for_procdef(pd: tprocdef; code, data: TAsmList); virtual;

          { generate a call to a routine in the system unit }
          procedure g_call_system_proc(list: TAsmList; const procname: string);

          { Generate code to exit an unwind-protected region. The default implementation
            produces a simple jump to destination label. }
          procedure g_local_unwind(list: TAsmList; l: TAsmLabel);virtual;abstract;
       end;

    var
       {# Main high level code generator class }
       hlcg : thlcgobj;

    procedure destroy_hlcodegen;

implementation

    uses
       globals,options,systems,
       fmodule,export,
       verbose,defutil,paramgr,
       symbase,symsym,symtable,
       ncon,nld,pass_1,pass_2,
       cpuinfo,cgobj,tgobj,cutils,procinfo,
       ncgutil,ngenutil;


    procedure destroy_hlcodegen;
      begin
        hlcg.free;
        hlcg:=nil;
        destroy_codegen;
      end;

  { thlcgobj }

  constructor thlcgobj.create;
    begin
    end;

  procedure thlcgobj.init_register_allocators;
    begin
      cg.init_register_allocators;
    end;

  procedure thlcgobj.done_register_allocators;
    begin
      cg.done_register_allocators;
    end;

  procedure thlcgobj.set_regalloc_live_range_direction(dir: TRADirection);
    begin
      cg.set_regalloc_live_range_direction(dir);
    end;

  function thlcgobj.getintregister(list: TAsmList; size: tdef): Tregister;
    begin
      result:=cg.getintregister(list,def_cgsize(size));
    end;

  function thlcgobj.getaddressregister(list: TAsmList; size: tdef): Tregister;
    begin
      result:=cg.getaddressregister(list);
    end;

  function thlcgobj.getfpuregister(list: TAsmList; size: tdef): Tregister;
    begin
      result:=cg.getfpuregister(list,def_cgsize(size));
    end;
(*
  function thlcgobj.getmmregister(list: TAsmList; size: tdef): Tregister;
    begin
      result:=cg.getmmregister(list,def_cgsize(size));
    end;
*)
  function thlcgobj.getflagregister(list: TAsmList; size: tdef): Tregister;
    begin
      result:=cg.getflagregister(list,def_cgsize(size));
    end;

    function thlcgobj.getregisterfordef(list: TAsmList; size: tdef): Tregister;
      begin
        case def2regtyp(size) of
          R_INTREGISTER:
            result:=getintregister(list,size);
          R_ADDRESSREGISTER:
            result:=getaddressregister(list,size);
          R_FPUREGISTER:
            result:=getfpuregister(list,size);
(*
          R_MMREGISTER:
            result:=getmmregister(list,size);
*)
          else
            internalerror(2010122901);
        end;
      end;

  function thlcgobj.uses_registers(rt: Tregistertype): boolean;
    begin
       result:=cg.uses_registers(rt);
    end;

  procedure thlcgobj.do_register_allocation(list: TAsmList; headertai: tai);
    begin
      cg.do_register_allocation(list,headertai);
    end;

  procedure thlcgobj.translate_register(var reg: tregister);
    begin
      cg.translate_register(reg);
    end;

  function thlcgobj.def2regtyp(def: tdef): tregistertype;
    begin
        case def.typ of
          enumdef,
          orddef,
          recorddef,
          setdef:
            result:=R_INTREGISTER;
          stringdef,
          pointerdef,
          classrefdef,
          objectdef,
          procvardef,
          procdef,
          arraydef,
          formaldef:
            result:=R_ADDRESSREGISTER;
          floatdef:
            if use_vectorfpu(def) then
              result:=R_MMREGISTER
            else if cs_fp_emulation in current_settings.moduleswitches then
              result:=R_INTREGISTER
            else
              result:=R_FPUREGISTER;
          filedef,
          variantdef:
            internalerror(2010120507);
        else
          internalerror(2010120506);
        end;
    end;

  class function thlcgobj.tcgsize2orddef(size: tcgsize): torddef;
    begin
      case size of
        OS_8:
          result:=torddef(u8inttype);
        OS_S8:
          result:=torddef(s8inttype);
        OS_16:
          result:=torddef(u16inttype);
        OS_S16:
          result:=torddef(s16inttype);
        OS_32:
          result:=torddef(u32inttype);
        OS_S32:
          result:=torddef(s32inttype);
        OS_64:
          result:=torddef(u64inttype);
        OS_S64:
          result:=torddef(s64inttype);
        else
          internalerror(2012050401);
      end;
    end;

  procedure thlcgobj.a_label(list: TAsmList; l: tasmlabel); inline;
    begin
      cg.a_label(list,l);
    end;

  procedure thlcgobj.a_reg_alloc(list: TAsmList; r: tregister);
    begin
      cg.a_reg_alloc(list,r);
    end;

  procedure thlcgobj.a_reg_dealloc(list: TAsmList; r: tregister);
    begin
      cg.a_reg_dealloc(list,r);
    end;

  procedure thlcgobj.a_reg_sync(list: TAsmList; r: tregister);
    begin
      cg.a_reg_sync(list,r);
    end;

  procedure thlcgobj.a_load_reg_cgpara(list: TAsmList; size: tdef; r: tregister; const cgpara: TCGPara);
    var
      ref: treference;
    begin
      cgpara.check_simple_location;
      paramanager.alloccgpara(list,cgpara);
      case cgpara.location^.loc of
         LOC_REGISTER,LOC_CREGISTER:
           a_load_reg_reg(list,size,cgpara.def,r,cgpara.location^.register);
         LOC_REFERENCE,LOC_CREFERENCE:
           begin
              reference_reset_base(ref,cgpara.location^.reference.index,cgpara.location^.reference.offset,cgpara.alignment);
              a_load_reg_ref(list,size,cgpara.def,r,ref);
           end;
(*
         LOC_MMREGISTER,LOC_CMMREGISTER:
           a_loadmm_intreg_reg(list,size,cgpara.def,r,cgpara.location^.register,mms_movescalar);
*)
         LOC_FPUREGISTER,LOC_CFPUREGISTER:
           begin
             tg.gethltemp(list,size,size.size,tt_normal,ref);
             a_load_reg_ref(list,size,size,r,ref);
             a_loadfpu_ref_cgpara(list,size,ref,cgpara);
             tg.ungettemp(list,ref);
           end
         else
           internalerror(2010120415);
      end;
    end;

  procedure thlcgobj.a_load_const_cgpara(list: TAsmList; tosize: tdef; a: aint; const cgpara: TCGPara);
    var
       ref : treference;
    begin
       cgpara.check_simple_location;
       paramanager.alloccgpara(list,cgpara);
       case cgpara.location^.loc of
          LOC_REGISTER,LOC_CREGISTER:
            a_load_const_reg(list,cgpara.def,a,cgpara.location^.register);
          LOC_REFERENCE,LOC_CREFERENCE:
            begin
               reference_reset_base(ref,cgpara.location^.reference.index,cgpara.location^.reference.offset,cgpara.alignment);
               a_load_const_ref(list,cgpara.def,a,ref);
            end
          else
            internalerror(2010120416);
       end;
    end;

  procedure thlcgobj.a_load_ref_cgpara(list: TAsmList; size: tdef; const r: treference; const cgpara: TCGPara);
    var
      ref: treference;
    begin
      cgpara.check_simple_location;
      paramanager.alloccgpara(list,cgpara);
      case cgpara.location^.loc of
         LOC_REGISTER,LOC_CREGISTER:
           a_load_ref_reg(list,size,cgpara.def,r,cgpara.location^.register);
         LOC_REFERENCE,LOC_CREFERENCE:
           begin
              reference_reset_base(ref,cgpara.location^.reference.index,cgpara.location^.reference.offset,cgpara.alignment);
              a_load_ref_ref(list,size,cgpara.def,r,ref);
           end
(*
         LOC_MMREGISTER,LOC_CMMREGISTER:
           begin
              case location^.size of
                OS_F32,
                OS_F64,
                OS_F128:
                  a_loadmm_ref_reg(list,cgpara.def,cgpara.def,r,location^.register,mms_movescalar);
                OS_M8..OS_M128,
                OS_MS8..OS_MS128:
                  a_loadmm_ref_reg(list,cgpara.def,cgpara.def,r,location^.register,nil);
                else
                  internalerror(2010120417);
              end;
           end
*)
         else
           internalerror(2010120418);
      end;
    end;

  procedure thlcgobj.a_load_loc_cgpara(list: TAsmList; size: tdef; const l: tlocation; const cgpara: TCGPara);
    begin
      case l.loc of
        LOC_REGISTER,
        LOC_CREGISTER :
          a_load_reg_cgpara(list,size,l.register,cgpara);
        LOC_CONSTANT :
          a_load_const_cgpara(list,size,l.value,cgpara);
        LOC_CREFERENCE,
        LOC_REFERENCE :
          a_load_ref_cgpara(list,size,l.reference,cgpara);
        else
          internalerror(2010120419);
      end;
    end;

  procedure thlcgobj.a_loadaddr_ref_cgpara(list: TAsmList; fromsize, tosize: tdef; const r: treference; const cgpara: TCGPara);
    var
       hr : tregister;
    begin
       cgpara.check_simple_location;
       if cgpara.location^.loc in [LOC_CREGISTER,LOC_REGISTER] then
         begin
           paramanager.allocparaloc(list,cgpara.location);
           a_loadaddr_ref_reg(list,fromsize,tosize,r,cgpara.location^.register)
         end
       else
         begin
           hr:=getaddressregister(list,tosize);
           a_loadaddr_ref_reg(list,fromsize,tosize,r,hr);
           a_load_reg_cgpara(list,tosize,hr,cgpara);
         end;
    end;

  procedure thlcgobj.a_call_ref(list: TAsmList; pd: tabstractprocdef; const ref: treference);
    var
      reg: tregister;
      size: tdef;
    begin
      { the loaded data is always a pointer to a procdef. A procvardef is
        implicitly a pointer already, but a procdef isn't -> create one }
      if pd.typ=procvardef then
        size:=pd
      else
        size:=getpointerdef(pd);
      reg:=getaddressregister(list,size);
      a_load_ref_reg(list,size,size,ref,reg);
      a_call_reg(list,pd,reg);
    end;

  procedure thlcgobj.a_call_name_static(list: TAsmList; pd: tprocdef; const s: TSymStr);
    begin
      a_call_name(list,pd,s,false);
    end;

    procedure thlcgobj.a_call_name_inherited(list: TAsmList; pd: tprocdef; const s: TSymStr);
      begin
        a_call_name(list,pd,s,false);
      end;

  procedure thlcgobj.a_load_const_ref(list: TAsmList; tosize: tdef; a: aint; const ref: treference);
    var
      tmpreg: tregister;
    begin
      tmpreg:=getintregister(list,tosize);
      a_load_const_reg(list,tosize,a,tmpreg);
      a_load_reg_ref(list,tosize,tosize,tmpreg,ref);
    end;

  procedure thlcgobj.a_load_const_loc(list: TAsmList; tosize: tdef; a: aint; const loc: tlocation);
    begin
      case loc.loc of
        LOC_REFERENCE,LOC_CREFERENCE:
          a_load_const_ref(list,tosize,a,loc.reference);
        LOC_REGISTER,LOC_CREGISTER:
          a_load_const_reg(list,tosize,a,loc.register);
        LOC_SUBSETREG,LOC_CSUBSETREG:
          a_load_const_subsetreg(list,tosize,a,loc.sreg);
        LOC_SUBSETREF,LOC_CSUBSETREF:
          a_load_const_subsetref(list,tosize,a,loc.sref);
        else
          internalerror(2010120401);
      end;
    end;

  procedure thlcgobj.a_load_reg_ref_unaligned(list: TAsmList; fromsize, tosize: tdef; register: tregister; const ref: treference);
    begin
      a_load_reg_ref(list,fromsize,tosize,register,ref);
    end;

  procedure thlcgobj.a_load_reg_loc(list: TAsmList; fromsize, tosize: tdef; reg: tregister; const loc: tlocation);
    begin
      case loc.loc of
        LOC_REFERENCE,LOC_CREFERENCE:
          a_load_reg_ref(list,fromsize,tosize,reg,loc.reference);
        LOC_REGISTER,LOC_CREGISTER:
          a_load_reg_reg(list,fromsize,tosize,reg,loc.register);
        LOC_SUBSETREG,LOC_CSUBSETREG:
          a_load_reg_subsetreg(list,fromsize,tosize,reg,loc.sreg);
        LOC_SUBSETREF,LOC_CSUBSETREF:
          a_load_reg_subsetref(list,fromsize,tosize,reg,loc.sref);
        { we don't have enough type information to handle these here
        LOC_MMREGISTER,LOC_CMMREGISTER:
          a_loadmm_intreg_reg(list,fromsize,loc.size,reg,loc.register,mms_movescalar);
        }
        else
          internalerror(2010120402);
      end;
    end;

  procedure thlcgobj.a_load_ref_reg_unaligned(list: TAsmList; fromsize, tosize: tdef; const ref: treference; register: tregister);
    begin
      a_load_ref_reg(list,fromsize,tosize,ref,register);
    end;

  procedure thlcgobj.a_load_ref_ref(list: TAsmList; fromsize, tosize: tdef; const sref: treference; const dref: treference);
    var
      tmpreg: tregister;
    begin
      { verify if we have the same reference }
      if references_equal(sref,dref) then
        exit;
      tmpreg:=getintregister(list,tosize);
      a_load_ref_reg(list,fromsize,tosize,sref,tmpreg);
      a_load_reg_ref(list,tosize,tosize,tmpreg,dref);
    end;

  procedure thlcgobj.a_load_loc_reg(list: TAsmList; fromsize, tosize: tdef; const loc: tlocation; reg: tregister);
    begin
      case loc.loc of
        LOC_REFERENCE,LOC_CREFERENCE:
          a_load_ref_reg(list,fromsize,tosize,loc.reference,reg);
        LOC_REGISTER,LOC_CREGISTER:
          a_load_reg_reg(list,fromsize,tosize,loc.register,reg);
        LOC_CONSTANT:
          a_load_const_reg(list,tosize,loc.value,reg);
        LOC_SUBSETREG,LOC_CSUBSETREG:
          a_load_subsetreg_reg(list,fromsize,tosize,loc.sreg,reg);
        LOC_SUBSETREF,LOC_CSUBSETREF:
          a_load_subsetref_reg(list,fromsize,tosize,loc.sref,reg);
        else
          internalerror(2010120201);
      end;
    end;

  procedure thlcgobj.a_load_loc_ref(list: TAsmList; fromsize, tosize: tdef; const loc: tlocation; const ref: treference);
    begin
      case loc.loc of
        LOC_REFERENCE,LOC_CREFERENCE:
          a_load_ref_ref(list,fromsize,tosize,loc.reference,ref);
        LOC_REGISTER,LOC_CREGISTER:
          a_load_reg_ref(list,fromsize,tosize,loc.register,ref);
        LOC_CONSTANT:
          a_load_const_ref(list,tosize,loc.value,ref);
        LOC_SUBSETREG,LOC_CSUBSETREG:
          a_load_subsetreg_ref(list,fromsize,tosize,loc.sreg,ref);
        LOC_SUBSETREF,LOC_CSUBSETREF:
          a_load_subsetref_ref(list,fromsize,tosize,loc.sref,ref);
        else
          internalerror(2010120403);
      end;
    end;

  procedure thlcgobj.a_load_loc_subsetreg(list: TAsmList; fromsize, tosubsetsize: tdef; const loc: tlocation; const sreg: tsubsetregister);
    begin
      case loc.loc of
        LOC_REFERENCE,LOC_CREFERENCE:
          a_load_ref_subsetreg(list,fromsize,tosubsetsize,loc.reference,sreg);
        LOC_REGISTER,LOC_CREGISTER:
          a_load_reg_subsetreg(list,fromsize,tosubsetsize,loc.register,sreg);
        LOC_CONSTANT:
          a_load_const_subsetreg(list,tosubsetsize,loc.value,sreg);
        LOC_SUBSETREG,LOC_CSUBSETREG:
          a_load_subsetreg_subsetreg(list,fromsize,tosubsetsize,loc.sreg,sreg);
        LOC_SUBSETREF,LOC_CSUBSETREF:
          a_load_subsetref_subsetreg(list,fromsize,tosubsetsize,loc.sref,sreg);
        else
          internalerror(2010120404);
      end;
    end;

  procedure thlcgobj.a_load_loc_subsetref(list: TAsmList; fromsize, tosubsetsize: tdef; const loc: tlocation; const sref: tsubsetreference);
    begin
      case loc.loc of
        LOC_REFERENCE,LOC_CREFERENCE:
          a_load_ref_subsetref(list,fromsize,tosubsetsize,loc.reference,sref);
        LOC_REGISTER,LOC_CREGISTER:
          a_load_reg_subsetref(list,fromsize,tosubsetsize,loc.register,sref);
        LOC_CONSTANT:
          a_load_const_subsetref(list,tosubsetsize,loc.value,sref);
        LOC_SUBSETREG,LOC_CSUBSETREG:
          a_load_subsetreg_subsetref(list,fromsize,tosubsetsize,loc.sreg,sref);
        LOC_SUBSETREF,LOC_CSUBSETREF:
          a_load_subsetref_subsetref(list,fromsize,tosubsetsize,loc.sref,sref);
        else
          internalerror(2010120405);
      end;
    end;

{$push}
{$r-,q-}

  procedure thlcgobj.a_load_subsetreg_reg(list: TAsmList; subsetsize, tosize: tdef; const sreg: tsubsetregister; destreg: tregister);
    var
      subsetregdef: torddef;
      bitmask: aword;
      tmpreg,
      subsetsizereg: tregister;
      stopbit: byte;
    begin
      subsetregdef:=tcgsize2orddef(sreg.subsetregsize);
      tmpreg:=getintregister(list,subsetregdef);
      if is_signed(subsetsize) then
        begin
          { sign extend in case the value has a bitsize mod 8 <> 0 }
          { both instructions will be optimized away if not        }
          a_op_const_reg_reg(list,OP_SHL,subsetregdef,(tcgsize2size[sreg.subsetregsize]*8)-sreg.startbit-sreg.bitlen,sreg.subsetreg,tmpreg);
          a_op_const_reg(list,OP_SAR,subsetregdef,(tcgsize2size[sreg.subsetregsize]*8)-sreg.bitlen,tmpreg);
        end
      else
        begin
          a_op_const_reg_reg(list,OP_SHR,subsetregdef,sreg.startbit,sreg.subsetreg,tmpreg);
          stopbit:=sreg.startbit+sreg.bitlen;
          // on x86(64), 1 shl 32(64) = 1 instead of 0
          // use aword to prevent overflow with 1 shl 31
          if (stopbit-sreg.startbit<>AIntBits) then
            bitmask:=(aword(1) shl (stopbit-sreg.startbit))-1
          else
            bitmask:=high(aword);
          a_op_const_reg(list,OP_AND,subsetregdef,tcgint(bitmask),tmpreg);
        end;
      subsetsizereg:=getintregister(list,subsetsize);
      a_load_reg_reg(list,subsetregdef,subsetsize,tmpreg,subsetsizereg);
      a_load_reg_reg(list,subsetsize,tosize,subsetsizereg,destreg);
    end;

  procedure thlcgobj.a_load_reg_subsetreg(list: TAsmList; fromsize, tosubsetsize: tdef; fromreg: tregister; const sreg: tsubsetregister);
    begin
      a_load_regconst_subsetreg_intern(list,fromsize,tosubsetsize,fromreg,sreg,SL_REG);
    end;

  procedure thlcgobj.a_load_subsetreg_subsetreg(list: TAsmlist; fromsubsetsize, tosubsetsize: tdef; const fromsreg, tosreg: tsubsetregister);
    var
      fromsubsetregdef,
      tosubsetregdef: torddef;
      tmpreg: tregister;
      bitmask: aword;
      stopbit: byte;
    begin
      if (fromsreg.bitlen>=tosreg.bitlen) then
        begin
          fromsubsetregdef:=tcgsize2orddef(fromsreg.subsetregsize);
          tosubsetregdef:=tcgsize2orddef(tosreg.subsetregsize);
          tmpreg:=getintregister(list,tosubsetregdef);
          a_load_reg_reg(list,fromsubsetregdef,tosubsetregdef,fromsreg.subsetreg,tmpreg);
          if (fromsreg.startbit<=tosreg.startbit) then
            a_op_const_reg(list,OP_SHL,tosubsetregdef,tosreg.startbit-fromsreg.startbit,tmpreg)
          else
            a_op_const_reg(list,OP_SHR,tosubsetregdef,fromsreg.startbit-tosreg.startbit,tmpreg);
          stopbit:=tosreg.startbit + tosreg.bitlen;
          // on x86(64), 1 shl 32(64) = 1 instead of 0
          if (stopbit<>AIntBits) then
            bitmask:=not(((aword(1) shl stopbit)-1) xor ((aword(1) shl tosreg.startbit)-1))
           else
             bitmask:=(aword(1) shl tosreg.startbit) - 1;
          a_op_const_reg(list,OP_AND,tosubsetregdef,tcgint(bitmask),tosreg.subsetreg);
          a_op_const_reg(list,OP_AND,tosubsetregdef,tcgint(not(bitmask)),tmpreg);
          a_op_reg_reg(list,OP_OR,tosubsetregdef,tmpreg,tosreg.subsetreg);
        end
      else
        begin
          tmpreg:=getintregister(list,tosubsetsize);
          a_load_subsetreg_reg(list,fromsubsetsize,tosubsetsize,fromsreg,tmpreg);
          a_load_reg_subsetreg(list,tosubsetsize,tosubsetsize,tmpreg,tosreg);
        end;
    end;

  procedure thlcgobj.a_load_subsetreg_ref(list: TAsmList; fromsubsetsize, tosize: tdef; const sreg: tsubsetregister; const destref: treference);
    var
      tmpreg: tregister;
    begin
      tmpreg:=getintregister(list,tosize);
      a_load_subsetreg_reg(list,fromsubsetsize,tosize,sreg,tmpreg);
      a_load_reg_ref(list,tosize,tosize,tmpreg,destref);
    end;

  procedure thlcgobj.a_load_ref_subsetreg(list: TAsmList; fromsize, tosubsetsize: tdef; const fromref: treference; const sreg: tsubsetregister);
    var
      tmpreg: tregister;
    begin
      tmpreg := getintregister(list,tosubsetsize);
      a_load_ref_reg(list,fromsize,tosubsetsize,fromref,tmpreg);
      a_load_reg_subsetreg(list,tosubsetsize,tosubsetsize,tmpreg,sreg);
    end;

  procedure thlcgobj.a_load_const_subsetreg(list: TAsmlist; tosubsetsize: tdef; a: aint; const sreg: tsubsetregister);
    var
      subsetregdef: torddef;
      bitmask: aword;
      stopbit: byte;
    begin
       subsetregdef:=tcgsize2orddef(sreg.subsetregsize);
       stopbit:=sreg.startbit+sreg.bitlen;
       // on x86(64), 1 shl 32(64) = 1 instead of 0
       if (stopbit<>AIntBits) then
         bitmask:=not(((aword(1) shl stopbit)-1) xor ((aword(1) shl sreg.startbit)-1))
       else
         bitmask:=(aword(1) shl sreg.startbit)-1;
       if (((aword(a) shl sreg.startbit) and not bitmask)<>not bitmask) then
         a_op_const_reg(list,OP_AND,subsetregdef,tcgint(bitmask),sreg.subsetreg);
       a_op_const_reg(list,OP_OR,subsetregdef,tcgint((aword(a) shl sreg.startbit) and not(bitmask)),sreg.subsetreg);
    end;

  procedure thlcgobj.a_load_subsetreg_loc(list: TAsmlist; fromsubsetsize, tosize: tdef; const sreg: tsubsetregister; const loc: tlocation);
    begin
      case loc.loc of
        LOC_REFERENCE,LOC_CREFERENCE:
          a_load_subsetreg_ref(list,fromsubsetsize,tosize,sreg,loc.reference);
        LOC_REGISTER,LOC_CREGISTER:
          a_load_subsetreg_reg(list,fromsubsetsize,tosize,sreg,loc.register);
        LOC_SUBSETREG,LOC_CSUBSETREG:
          a_load_subsetreg_subsetreg(list,fromsubsetsize,tosize,sreg,loc.sreg);
        LOC_SUBSETREF,LOC_CSUBSETREF:
          a_load_subsetreg_subsetref(list,fromsubsetsize,tosize,sreg,loc.sref);
        else
          internalerror(2010120406);
      end;
    end;

  procedure thlcgobj.a_load_subsetref_reg(list: TAsmList; fromsubsetsize, tosize: tdef; const sref: tsubsetreference; destreg: tregister);
    var
      tmpref: treference;
      valuereg,extra_value_reg: tregister;
      tosreg: tsubsetregister;
      loadsize: torddef;
      loadbitsize: byte;
      extra_load: boolean;
    begin
      get_subsetref_load_info(sref,loadsize,extra_load);
      loadbitsize:=loadsize.size*8;

      { load the (first part) of the bit sequence }
      valuereg:=getintregister(list,osuinttype);
      a_load_ref_reg(list,loadsize,osuinttype,sref.ref,valuereg);

      if not extra_load then
        begin
          { everything is guaranteed to be in a single register of loadsize }
          if (sref.bitindexreg=NR_NO) then
            begin
              { use subsetreg routine, it may have been overridden with an optimized version }
              tosreg.subsetreg:=valuereg;
              tosreg.subsetregsize:=def_cgsize(osuinttype);
              { subsetregs always count bits from right to left }
              if (target_info.endian=endian_big) then
                tosreg.startbit:=loadbitsize-(sref.startbit+sref.bitlen)
              else
                tosreg.startbit:=sref.startbit;
              tosreg.bitlen:=sref.bitlen;
              a_load_subsetreg_reg(list,fromsubsetsize,tosize,tosreg,destreg);
              exit;
            end
          else
            begin
              if (sref.startbit<>0) then
                internalerror(2006081510);
              if (target_info.endian=endian_big) then
                begin
                  a_op_reg_reg(list,OP_SHL,osuinttype,sref.bitindexreg,valuereg);
                  if is_signed(fromsubsetsize) then
                    begin
                      { sign extend to entire register }
                      a_op_const_reg(list,OP_SHL,osuinttype,AIntBits-loadbitsize,valuereg);
                      a_op_const_reg(list,OP_SAR,osuinttype,AIntBits-sref.bitlen,valuereg);
                    end
                  else
                    a_op_const_reg(list,OP_SHR,osuinttype,loadbitsize-sref.bitlen,valuereg);
                end
              else
                begin
                  a_op_reg_reg(list,OP_SHR,osuinttype,sref.bitindexreg,valuereg);
                  if is_signed(fromsubsetsize) then
                    begin
                      a_op_const_reg(list,OP_SHL,osuinttype,AIntBits-sref.bitlen,valuereg);
                      a_op_const_reg(list,OP_SAR,osuinttype,AIntBits-sref.bitlen,valuereg);
                    end
                end;
              { mask other bits/sign extend }
              if not is_signed(fromsubsetsize) then
                a_op_const_reg(list,OP_AND,osuinttype,tcgint((aword(1) shl sref.bitlen)-1),valuereg);
            end
        end
      else
        begin
          { load next value as well }
          extra_value_reg:=getintregister(list,osuinttype);

          if (sref.bitindexreg=NR_NO) then
            begin
              tmpref:=sref.ref;
              inc(tmpref.offset,loadbitsize div 8);
              a_load_ref_reg(list,loadsize,osuinttype,tmpref,extra_value_reg);
              { can be overridden to optimize }
              a_load_subsetref_regs_noindex(list,fromsubsetsize,loadbitsize,sref,valuereg,extra_value_reg)
            end
          else
            begin
              if (sref.startbit<>0) then
                internalerror(2006080610);
              a_load_subsetref_regs_index(list,fromsubsetsize,loadbitsize,sref,valuereg);
            end;
        end;

      { store in destination }
{$ifndef cpuhighleveltarget}
      { avoid unnecessary sign extension and zeroing }
      valuereg:=cg.makeregsize(list,valuereg,OS_INT);
      destreg:=cg.makeregsize(list,destreg,OS_INT);
      cg.a_load_reg_reg(list,OS_INT,OS_INT,valuereg,destreg);
      destreg:=cg.makeregsize(list,destreg,def_cgsize(tosize));
{$else}
      { can't juggle with register sizes, they are actually typed entities
        here }
      a_load_reg_reg(list,osuinttype,tosize,valuereg,destreg);
{$endif}
    end;

  procedure thlcgobj.a_load_reg_subsetref(list: TAsmList; fromsize, tosubsetsize: tdef; fromreg: tregister; const sref: tsubsetreference);
    begin
      a_load_regconst_subsetref_intern(list,fromsize,tosubsetsize,fromreg,sref,SL_REG);
    end;

  procedure thlcgobj.a_load_subsetref_subsetref(list: TAsmlist; fromsubsetsize, tosubsetsize: tdef; const fromsref, tosref: tsubsetreference);
    var
      tmpreg: tregister;
    begin
      tmpreg:=getintregister(list,tosubsetsize);
      a_load_subsetref_reg(list,fromsubsetsize,tosubsetsize,fromsref,tmpreg);
      a_load_reg_subsetref(list,tosubsetsize,tosubsetsize,tmpreg,tosref);
    end;

  procedure thlcgobj.a_load_subsetref_ref(list: TAsmList; fromsubsetsize, tosize: tdef; const sref: tsubsetreference; const destref: treference);
    var
      tmpreg: tregister;
    begin
      tmpreg:=getintregister(list,tosize);
      a_load_subsetref_reg(list,fromsubsetsize,tosize,sref,tmpreg);
      a_load_reg_ref(list,tosize,tosize,tmpreg,destref);
    end;

  procedure thlcgobj.a_load_ref_subsetref(list: TAsmList; fromsize, tosubsetsize: tdef; const fromref: treference; const sref: tsubsetreference);
    var
      tmpreg: tregister;
    begin
      tmpreg := getintregister(list,tosubsetsize);
      a_load_ref_reg(list,fromsize,tosubsetsize,fromref,tmpreg);
      a_load_reg_subsetref(list,tosubsetsize,tosubsetsize,tmpreg,sref);
    end;

  procedure thlcgobj.a_load_const_subsetref(list: TAsmlist; tosubsetsize: tdef; a: tcgint; const sref: tsubsetreference);
    var
      tmpreg: tregister;
      slopt: tsubsetloadopt;
    begin
      { perform masking of the source value in advance }
      slopt:=SL_REGNOSRCMASK;
      if (sref.bitlen<>AIntBits) then
        a:=tcgint(aword(a) and ((aword(1) shl sref.bitlen) -1));
      if (
          { broken x86 "x shl regbitsize = x" }
          ((sref.bitlen<>AIntBits) and
           ((aword(a) and ((aword(1) shl sref.bitlen)-1))=(aword(1) shl sref.bitlen)-1)) or
          ((sref.bitlen=AIntBits) and
           (a=-1))
         ) then
        slopt:=SL_SETMAX
      else if (a=0) then
        slopt:=SL_SETZERO;
      if not(slopt in [SL_SETZERO,SL_SETMAX]) then
        begin
          tmpreg:=getintregister(list,tosubsetsize);
          a_load_const_reg(list,tosubsetsize,a,tmpreg);
        end
      else
        tmpreg:=NR_NO;
      a_load_regconst_subsetref_intern(list,tosubsetsize,tosubsetsize,tmpreg,sref,slopt);
    end;

  procedure thlcgobj.a_load_subsetref_loc(list: TAsmlist; fromsubsetsize, tosize: tdef; const sref: tsubsetreference; const loc: tlocation);
    begin
      case loc.loc of
        LOC_REFERENCE,LOC_CREFERENCE:
          a_load_subsetref_ref(list,fromsubsetsize,tosize,sref,loc.reference);
        LOC_REGISTER,LOC_CREGISTER:
          a_load_subsetref_reg(list,fromsubsetsize,tosize,sref,loc.register);
        LOC_SUBSETREG,LOC_CSUBSETREG:
          a_load_subsetref_subsetreg(list,fromsubsetsize,tosize,sref,loc.sreg);
        LOC_SUBSETREF,LOC_CSUBSETREF:
          a_load_subsetref_subsetref(list,fromsubsetsize,tosize,sref,loc.sref);
        else
          internalerror(2010120407);
      end;
    end;

  procedure thlcgobj.a_load_subsetref_subsetreg(list: TAsmlist; fromsubsetsize, tosubsetsize: tdef; const fromsref: tsubsetreference; const tosreg: tsubsetregister);
    var
      tmpreg: tregister;
    begin
      tmpreg:=getintregister(list,tosubsetsize);
      a_load_subsetref_reg(list,fromsubsetsize,tosubsetsize,fromsref,tmpreg);
      a_load_reg_subsetreg(list,tosubsetsize,tosubsetsize,tmpreg,tosreg);
    end;

  procedure thlcgobj.a_load_subsetreg_subsetref(list: TAsmlist; fromsubsetsize, tosubsetsize: tdef; const fromsreg: tsubsetregister; const tosref: tsubsetreference);
    var
      tmpreg: tregister;
    begin
      tmpreg := getintregister(list,tosubsetsize);
      a_load_subsetreg_reg(list,fromsubsetsize,tosubsetsize,fromsreg,tmpreg);
      a_load_reg_subsetref(list,tosubsetsize,tosubsetsize,tmpreg,tosref);
    end;

  procedure thlcgobj.a_bit_test_reg_reg_reg(list: TAsmList; bitnumbersize, valuesize, destsize: tdef; bitnumber, value, destreg: tregister);
    var
      tmpvalue: tregister;
    begin
      tmpvalue:=getintregister(list,valuesize);

      if (target_info.endian=endian_little) then
        begin
          { rotate value register "bitnumber" bits to the right }
          a_op_reg_reg_reg(list,OP_SHR,valuesize,bitnumber,value,tmpvalue);
          { extract the bit we want }
          a_op_const_reg(list,OP_AND,valuesize,1,tmpvalue);
        end
      else
        begin
          { highest (leftmost) bit = bit 0 -> shl bitnumber results in wanted }
          { bit in uppermost position, then move it to the lowest position    }
          { "and" is not necessary since combination of shl/shr will clear    }
          { all other bits                                                    }
          a_op_reg_reg_reg(list,OP_SHL,valuesize,bitnumber,value,tmpvalue);
          a_op_const_reg(list,OP_SHR,valuesize,valuesize.size*8-1,tmpvalue);
        end;
      a_load_reg_reg(list,valuesize,destsize,tmpvalue,destreg);
    end;

  procedure thlcgobj.a_bit_test_const_ref_reg(list: TAsmList; fromsize, destsize: tdef; bitnumber: aint; const ref: treference; destreg: tregister);
    begin
      a_load_subsetref_reg(list,u8inttype,destsize,get_bit_const_ref_sref(bitnumber,fromsize,ref),destreg);
    end;

  procedure thlcgobj.a_bit_test_const_reg_reg(list: TAsmList; setregsize, destsize: tdef; bitnumber: aint; setreg, destreg: tregister);
    begin
      a_load_subsetreg_reg(list,setregsize,destsize,get_bit_const_reg_sreg(setregsize,bitnumber,setreg),destreg);
    end;

  procedure thlcgobj.a_bit_test_const_subsetreg_reg(list: TAsmList; fromsubsetsize, destsize: tdef; bitnumber: aint; const setreg: tsubsetregister; destreg: tregister);
    var
      tmpsreg: tsubsetregister;
    begin
      { the first parameter is used to calculate the bit offset in }
      { case of big endian, and therefore must be the size of the  }
      { set and not of the whole subsetreg                         }
      tmpsreg:=get_bit_const_reg_sreg(fromsubsetsize,bitnumber,setreg.subsetreg);
      { now fix the size of the subsetreg }
      tmpsreg.subsetregsize:=setreg.subsetregsize;
      { correct offset of the set in the subsetreg }
      inc(tmpsreg.startbit,setreg.startbit);
      a_load_subsetreg_reg(list,fromsubsetsize,destsize,tmpsreg,destreg);
    end;

  procedure thlcgobj.a_bit_test_reg_ref_reg(list: TAsmList; bitnumbersize, refsize, destsize: tdef; bitnumber: tregister; const ref: treference; destreg: tregister);
    begin
      a_load_subsetref_reg(list,u8inttype,destsize,get_bit_reg_ref_sref(list,bitnumbersize,refsize,bitnumber,ref),destreg);
    end;

  procedure thlcgobj.a_bit_test_reg_loc_reg(list: TAsmList; bitnumbersize, locsize, destsize: tdef; bitnumber: tregister; const loc: tlocation; destreg: tregister);
    var
      tmpreg: tregister;
    begin
      case loc.loc of
        LOC_REFERENCE,LOC_CREFERENCE:
          a_bit_test_reg_ref_reg(list,bitnumbersize,locsize,destsize,bitnumber,loc.reference,destreg);
        LOC_REGISTER,LOC_CREGISTER,
        LOC_SUBSETREG,LOC_CSUBSETREG,
        LOC_CONSTANT:
          begin
            case loc.loc of
              LOC_REGISTER,LOC_CREGISTER:
                tmpreg:=loc.register;
              LOC_SUBSETREG,LOC_CSUBSETREG:
                begin
                  tmpreg:=getintregister(list,locsize);
                  a_load_subsetreg_reg(list,locsize,locsize,loc.sreg,tmpreg);
                end;
              LOC_CONSTANT:
                begin
                  tmpreg:=getintregister(list,locsize);
                  a_load_const_reg(list,locsize,loc.value,tmpreg);
                end;
            end;
            a_bit_test_reg_reg_reg(list,bitnumbersize,locsize,destsize,bitnumber,tmpreg,destreg);
          end;
        { LOC_SUBSETREF is not possible, because sets are not (yet) bitpacked }
        else
          internalerror(2010120411);
      end;
    end;

  procedure thlcgobj.a_bit_test_const_loc_reg(list: TAsmList; locsize, destsize: tdef; bitnumber: aint; const loc: tlocation; destreg: tregister);
    begin
      case loc.loc of
        LOC_REFERENCE,LOC_CREFERENCE:
          a_bit_test_const_ref_reg(list,locsize,destsize,bitnumber,loc.reference,destreg);
        LOC_REGISTER,LOC_CREGISTER:
          a_bit_test_const_reg_reg(list,locsize,destsize,bitnumber,loc.register,destreg);
        LOC_SUBSETREG,LOC_CSUBSETREG:
          a_bit_test_const_subsetreg_reg(list,locsize,destsize,bitnumber,loc.sreg,destreg);
        { LOC_SUBSETREF is not possible, because sets are not (yet) bitpacked }
        else
          internalerror(2010120410);
      end;
    end;

  procedure thlcgobj.a_bit_set_reg_reg(list: TAsmList; doset: boolean; bitnumbersize, destsize: tdef; bitnumber, dest: tregister);
    var
      tmpvalue: tregister;
    begin
      tmpvalue:=getintregister(list,destsize);

      if (target_info.endian=endian_little) then
        begin
          a_load_const_reg(list,destsize,1,tmpvalue);
          { rotate bit "bitnumber" bits to the left }
          a_op_reg_reg(list,OP_SHL,destsize,bitnumber,tmpvalue);
        end
      else
        begin
          { highest (leftmost) bit = bit 0 -> "$80/$8000/$80000000/ ... }
          { shr bitnumber" results in correct mask                      }
          a_load_const_reg(list,destsize,1 shl (destsize.size*8-1),tmpvalue);
          a_op_reg_reg(list,OP_SHR,destsize,bitnumber,tmpvalue);
        end;
      { set/clear the bit we want }
      if doset then
        a_op_reg_reg(list,OP_OR,destsize,tmpvalue,dest)
      else
        begin
          a_op_reg_reg(list,OP_NOT,destsize,tmpvalue,tmpvalue);
          a_op_reg_reg(list,OP_AND,destsize,tmpvalue,dest)
        end;
    end;

  procedure thlcgobj.a_bit_set_const_ref(list: TAsmList; doset: boolean; destsize: tdef; bitnumber: aint; const ref: treference);
    begin
      a_load_const_subsetref(list,u8inttype,ord(doset),get_bit_const_ref_sref(bitnumber,destsize,ref));
    end;

  procedure thlcgobj.a_bit_set_const_reg(list: TAsmList; doset: boolean; destsize: tdef; bitnumber: aint; destreg: tregister);
    begin
      a_load_const_subsetreg(list,u8inttype,ord(doset),get_bit_const_reg_sreg(destsize,bitnumber,destreg));
    end;

  procedure thlcgobj.a_bit_set_const_subsetreg(list: TAsmList; doset: boolean; destsize: tdef; bitnumber: aint; const destreg: tsubsetregister);
    var
      tmpsreg: tsubsetregister;
    begin
      { the first parameter is used to calculate the bit offset in }
      { case of big endian, and therefore must be the size of the  }
      { set and not of the whole subsetreg                         }
      tmpsreg:=get_bit_const_reg_sreg(destsize,bitnumber,destreg.subsetreg);
      { now fix the size of the subsetreg }
      tmpsreg.subsetregsize:=destreg.subsetregsize;
      { correct offset of the set in the subsetreg }
      inc(tmpsreg.startbit,destreg.startbit);
      a_load_const_subsetreg(list,u8inttype,ord(doset),tmpsreg);
    end;

  procedure thlcgobj.a_bit_set_reg_ref(list: TAsmList; doset: boolean; fromsize, tosize: tdef; bitnumber: tregister; const ref: treference);
    begin
      a_load_const_subsetref(list,u8inttype,ord(doset),get_bit_reg_ref_sref(list,fromsize,tosize,bitnumber,ref));
    end;

  procedure thlcgobj.a_bit_set_reg_loc(list: TAsmList; doset: boolean; regsize, tosize: tdef; bitnumber: tregister; const loc: tlocation);
    var
      tmpreg: tregister;
    begin
      case loc.loc of
        LOC_REFERENCE:
          a_bit_set_reg_ref(list,doset,regsize,tosize,bitnumber,loc.reference);
        LOC_CREGISTER:
          a_bit_set_reg_reg(list,doset,regsize,tosize,bitnumber,loc.register);
        { e.g. a 2-byte set in a record regvar }
        LOC_CSUBSETREG:
          begin
            { hard to do in-place in a generic way, so operate on a copy }
            tmpreg:=getintregister(list,tosize);
            a_load_subsetreg_reg(list,tosize,tosize,loc.sreg,tmpreg);
            a_bit_set_reg_reg(list,doset,regsize,tosize,bitnumber,tmpreg);
            a_load_reg_subsetreg(list,tosize,tosize,tmpreg,loc.sreg);
          end;
        { LOC_SUBSETREF is not possible, because sets are not (yet) bitpacked }
        else
          internalerror(2010120408)
      end;
    end;

  procedure thlcgobj.a_bit_set_const_loc(list: TAsmList; doset: boolean; tosize: tdef; bitnumber: aint; const loc: tlocation);
    begin
      case loc.loc of
        LOC_REFERENCE:
          a_bit_set_const_ref(list,doset,tosize,bitnumber,loc.reference);
        LOC_CREGISTER:
          a_bit_set_const_reg(list,doset,tosize,bitnumber,loc.register);
        LOC_CSUBSETREG:
          a_bit_set_const_subsetreg(list,doset,tosize,bitnumber,loc.sreg);
        { LOC_SUBSETREF is not possible, because sets are not (yet) bitpacked }
        else
          internalerror(2010120409)
      end;
    end;


  (*
    Subsetrefs are used for (bit)packed arrays and (bit)packed records stored
    in memory. They are like a regular reference, but contain an extra bit
    offset (either constant -startbit- or variable -bitindexreg-, always OS_INT)
    and a bit length (always constant).

    Bit packed values are stored differently in memory depending on whether we
    are on a big or a little endian system (compatible with at least GPC). The
    size of the basic working unit is always the smallest power-of-2 byte size
    which can contain the bit value (so 1..8 bits -> 1 byte, 9..16 bits -> 2
    bytes, 17..32 bits -> 4 bytes etc).

    On a big endian, 5-bit: values are stored like this:
      11111222 22333334 44445555 56666677 77788888
    The leftmost bit of each 5-bit value corresponds to the most significant
    bit.

    On little endian, it goes like this:
      22211111 43333322 55554444 77666665 88888777
    In this case, per byte the left-most bit is more significant than those on
    the right, but the bits in the next byte are all more significant than
    those in the previous byte (e.g., the 222 in the first byte are the low
    three bits of that value, while the 22 in the second byte are the upper
    two bits.

    Big endian, 9 bit values:
      11111111 12222222 22333333 33344444 ...

    Little endian, 9 bit values:
      11111111 22222221 33333322 44444333 ...
    This is memory representation and the 16 bit values are byteswapped.
    Similarly as in the previous case, the 2222222 string contains the lower
    bits of value 2 and the 22 string contains the upper bits. Once loaded into
    registers (two 16 bit registers in the current implementation, although a
    single 32 bit register would be possible too, in particular if 32 bit
    alignment can be guaranteed), this becomes:
      22222221 11111111 44444333 33333322 ...
      (l)ow  u     l     l    u     l   u

    The startbit/bitindex in a subsetreference always refers to
    a) on big endian: the most significant bit of the value
       (bits counted from left to right, both memory an registers)
    b) on little endian: the least significant bit when the value
       is loaded in a register (bit counted from right to left)

    Although a) results in more complex code for big endian systems, it's
    needed for compatibility both with GPC and with e.g. bitpacked arrays in
    Apple's universal interfaces which depend on these layout differences).

    Note: when changing the loadsize calculated in get_subsetref_load_info,
    make sure the appropriate alignment is guaranteed, at least in case of
    {$defined cpurequiresproperalignment}.
  *)

  procedure thlcgobj.get_subsetref_load_info(const sref: tsubsetreference; out loadsize: torddef; out extra_load: boolean);
    var
      intloadsize: tcgint;
    begin
      intloadsize:=packedbitsloadsize(sref.bitlen);

      if (intloadsize=0) then
        internalerror(2006081310);

      if (intloadsize>sizeof(aint)) then
        intloadsize:=sizeof(aint);
      loadsize:=tcgsize2orddef(int_cgsize(intloadsize));

      if (sref.bitlen>sizeof(aint)*8) then
        internalerror(2006081312);

      extra_load:=
        (sref.bitlen<>1) and
        ((sref.bitindexreg<>NR_NO) or
         (byte(sref.startbit+sref.bitlen)>byte(intloadsize*8)));
    end;

  procedure thlcgobj.a_load_subsetref_regs_noindex(list: TAsmList; subsetsize: tdef; loadbitsize: byte; const sref: tsubsetreference; valuereg, extra_value_reg: tregister);
    var
      restbits: byte;
    begin
      if (target_info.endian=endian_big) then
        begin
          { valuereg contains the upper bits, extra_value_reg the lower }
          restbits:=(sref.bitlen-(loadbitsize-sref.startbit));
          if is_signed(subsetsize) then
            begin
              { sign extend }
              a_op_const_reg(list,OP_SHL,osuinttype,AIntBits-loadbitsize+sref.startbit,valuereg);
              a_op_const_reg(list,OP_SAR,osuinttype,AIntBits-sref.bitlen,valuereg);
            end
          else
            begin
              a_op_const_reg(list,OP_SHL,osuinttype,restbits,valuereg);
              { mask other bits }
              if (sref.bitlen<>AIntBits) then
                a_op_const_reg(list,OP_AND,osuinttype,tcgint((aword(1) shl sref.bitlen)-1),valuereg);
            end;
          a_op_const_reg(list,OP_SHR,osuinttype,loadbitsize-restbits,extra_value_reg)
        end
      else
        begin
          { valuereg contains the lower bits, extra_value_reg the upper }
          a_op_const_reg(list,OP_SHR,osuinttype,sref.startbit,valuereg);
          if is_signed(subsetsize) then
            begin
              a_op_const_reg(list,OP_SHL,osuinttype,AIntBits-sref.bitlen+loadbitsize-sref.startbit,extra_value_reg);
              a_op_const_reg(list,OP_SAR,osuinttype,AIntBits-sref.bitlen,extra_value_reg);
            end
          else
            begin
              a_op_const_reg(list,OP_SHL,osuinttype,loadbitsize-sref.startbit,extra_value_reg);
              { mask other bits }
              if (sref.bitlen <> AIntBits) then
                a_op_const_reg(list,OP_AND,osuinttype,tcgint((aword(1) shl sref.bitlen)-1),extra_value_reg);
            end;
        end;
      { merge }
      a_op_reg_reg(list,OP_OR,osuinttype,extra_value_reg,valuereg);
    end;

  procedure thlcgobj.a_load_subsetref_regs_index(list: TAsmList; subsetsize: tdef; loadbitsize: byte; const sref: tsubsetreference; valuereg: tregister);
    var
      hl: tasmlabel;
      tmpref: treference;
      extra_value_reg,
      tmpreg: tregister;
    begin
      tmpreg:=getintregister(list,osuinttype);
      tmpref:=sref.ref;
      inc(tmpref.offset,loadbitsize div 8);
      extra_value_reg:=getintregister(list,osuinttype);

      if (target_info.endian=endian_big) then
        begin
          { since this is a dynamic index, it's possible that the value   }
          { is entirely in valuereg.                                      }

          { get the data in valuereg in the right place }
          a_op_reg_reg(list,OP_SHL,osuinttype,sref.bitindexreg,valuereg);
          if is_signed(subsetsize) then
            begin
              a_op_const_reg(list,OP_SHL,osuinttype,AIntBits-loadbitsize,valuereg);
              a_op_const_reg(list,OP_SAR,osuinttype,AIntBits-sref.bitlen,valuereg)
            end
          else
            begin
              a_op_const_reg(list,OP_SHR,osuinttype,loadbitsize-sref.bitlen,valuereg);
              if (loadbitsize<>AIntBits) then
                { mask left over bits }
                a_op_const_reg(list,OP_AND,osuinttype,tcgint((aword(1) shl sref.bitlen)-1),valuereg);
            end;
          tmpreg := getintregister(list,osuinttype);

          { ensure we don't load anything past the end of the array }
          current_asmdata.getjumplabel(hl);
          a_cmp_const_reg_label(list,osuinttype,OC_BE,loadbitsize-sref.bitlen,sref.bitindexreg,hl);

          { the bits in extra_value_reg (if any) start at the most significant bit =>         }
          { extra_value_reg must be shr by (loadbitsize-sref.bitlen)+(loadsize-sref.bitindex) }
          { => = -(sref.bitindex+(sref.bitlen-2*loadbitsize))                                 }
          a_op_const_reg_reg(list,OP_ADD,osuinttype,sref.bitlen-2*loadbitsize,sref.bitindexreg,tmpreg);
          a_op_reg_reg(list,OP_NEG,osuinttype,tmpreg,tmpreg);

          { load next "loadbitsize" bits of the array }
          a_load_ref_reg(list,tcgsize2orddef(int_cgsize(loadbitsize div 8)),osuinttype,tmpref,extra_value_reg);

          a_op_reg_reg(list,OP_SHR,osuinttype,tmpreg,extra_value_reg);
          { if there are no bits in extra_value_reg, then sref.bitindex was      }
          { < loadsize-sref.bitlen, and therefore tmpreg will now be >= loadsize }
          { => extra_value_reg is now 0                                          }
          { merge }
          a_op_reg_reg(list,OP_OR,osuinttype,extra_value_reg,valuereg);
          { no need to mask, necessary masking happened earlier on }
          a_label(list,hl);
        end
      else
        begin
          a_op_reg_reg(list,OP_SHR,osuinttype,sref.bitindexreg,valuereg);

          { ensure we don't load anything past the end of the array }
          current_asmdata.getjumplabel(hl);
          a_cmp_const_reg_label(list,osuinttype,OC_BE,loadbitsize-sref.bitlen,sref.bitindexreg,hl);

          { Y-x = -(Y-x) }
          a_op_const_reg_reg(list,OP_SUB,osuinttype,loadbitsize,sref.bitindexreg,tmpreg);
          a_op_reg_reg(list,OP_NEG,osuinttype,tmpreg,tmpreg);

          { load next "loadbitsize" bits of the array }
          a_load_ref_reg(list,tcgsize2orddef(int_cgsize(loadbitsize div 8)),osuinttype,tmpref,extra_value_reg);

          { tmpreg is in the range 1..<cpu_bitsize>-1 -> always ok }
          a_op_reg_reg(list,OP_SHL,osuinttype,tmpreg,extra_value_reg);
          { merge }
          a_op_reg_reg(list,OP_OR,osuinttype,extra_value_reg,valuereg);
          a_label(list,hl);
          { sign extend or mask other bits }
          if is_signed(subsetsize) then
            begin
              a_op_const_reg(list,OP_SHL,osuinttype,AIntBits-sref.bitlen,valuereg);
              a_op_const_reg(list,OP_SAR,osuinttype,AIntBits-sref.bitlen,valuereg);
            end
          else
            a_op_const_reg(list,OP_AND,osuinttype,tcgint((aword(1) shl sref.bitlen)-1),valuereg);
        end;
    end;

  procedure thlcgobj.a_load_regconst_subsetref_intern(list: TAsmList; fromsize, subsetsize: tdef; fromreg: tregister; const sref: tsubsetreference; slopt: tsubsetloadopt);
    var
      hl: tasmlabel;
      tmpreg, tmpindexreg, valuereg, extra_value_reg, maskreg: tregister;
      tosreg, fromsreg: tsubsetregister;
      tmpref: treference;
      bitmask: aword;
      loadsize: torddef;
      loadbitsize: byte;
      extra_load: boolean;
    begin
      { the register must be able to contain the requested value }
      if (fromsize.size*8<sref.bitlen) then
        internalerror(2006081613);

      get_subsetref_load_info(sref,loadsize,extra_load);
      loadbitsize:=loadsize.size*8;

      { load the (first part) of the bit sequence }
      valuereg:=getintregister(list,osuinttype);
      a_load_ref_reg(list,loadsize,osuinttype,sref.ref,valuereg);

      { constant offset of bit sequence? }
      if not extra_load then
        begin
          if (sref.bitindexreg=NR_NO) then
            begin
              { use subsetreg routine, it may have been overridden with an optimized version }
              tosreg.subsetreg:=valuereg;
              tosreg.subsetregsize:=def_cgsize(osuinttype);
              { subsetregs always count bits from right to left }
              if (target_info.endian=endian_big) then
                tosreg.startbit:=loadbitsize-(sref.startbit+sref.bitlen)
              else
                tosreg.startbit:=sref.startbit;
              tosreg.bitlen:=sref.bitlen;
              a_load_regconst_subsetreg_intern(list,fromsize,subsetsize,fromreg,tosreg,slopt);
            end
          else
            begin
              if (sref.startbit<>0) then
                internalerror(2006081710);
              { should be handled by normal code and will give wrong result }
              { on x86 for the '1 shl bitlen' below                         }
              if (sref.bitlen=AIntBits) then
                internalerror(2006081711);

              { zero the bits we have to insert }
              if (slopt<>SL_SETMAX) then
                begin
                  maskreg:=getintregister(list,osuinttype);
                  if (target_info.endian = endian_big) then
                    begin
                      a_load_const_reg(list,osuinttype,tcgint((aword(1) shl sref.bitlen)-1) shl (loadbitsize-sref.bitlen),maskreg);
                      a_op_reg_reg(list,OP_SHR,osuinttype,sref.bitindexreg,maskreg);
                    end
                  else
                    begin
                      a_load_const_reg(list,osuinttype,tcgint((aword(1) shl sref.bitlen)-1),maskreg);
                      a_op_reg_reg(list,OP_SHL,osuinttype,sref.bitindexreg,maskreg);
                    end;
                  a_op_reg_reg(list,OP_NOT,osuinttype,maskreg,maskreg);
                  a_op_reg_reg(list,OP_AND,osuinttype,maskreg,valuereg);
                end;

              { insert the value }
              if (slopt<>SL_SETZERO) then
                begin
                  tmpreg:=getintregister(list,osuinttype);
                  if (slopt<>SL_SETMAX) then
                    a_load_reg_reg(list,fromsize,osuinttype,fromreg,tmpreg)
                  else if (sref.bitlen<>AIntBits) then
                    a_load_const_reg(list,osuinttype,tcgint((aword(1) shl sref.bitlen)-1), tmpreg)
                  else
                    a_load_const_reg(list,osuinttype,-1,tmpreg);
                  if (target_info.endian=endian_big) then
                    begin
                      a_op_const_reg(list,OP_SHL,osuinttype,loadbitsize-sref.bitlen,tmpreg);
                      if not(slopt in [SL_REGNOSRCMASK,SL_SETMAX]) then
                        begin
                          if (loadbitsize<>AIntBits) then
                            bitmask:=(((aword(1) shl loadbitsize)-1) xor ((aword(1) shl (loadbitsize-sref.bitlen))-1))
                          else
                            bitmask:=(high(aword) xor ((aword(1) shl (loadbitsize-sref.bitlen))-1));
                          a_op_const_reg(list,OP_AND,osuinttype,bitmask,tmpreg);
                        end;
                      a_op_reg_reg(list,OP_SHR,osuinttype,sref.bitindexreg,tmpreg);
                    end
                  else
                    begin
                      if not(slopt in [SL_REGNOSRCMASK,SL_SETMAX]) then
                        a_op_const_reg(list,OP_AND,osuinttype,tcgint((aword(1) shl sref.bitlen)-1),tmpreg);
                      a_op_reg_reg(list,OP_SHL,osuinttype,sref.bitindexreg,tmpreg);
                    end;
                  a_op_reg_reg(list,OP_OR,osuinttype,tmpreg,valuereg);
                end;
            end;
          { store back to memory }
          tmpreg:=getintregister(list,loadsize);
          a_load_reg_reg(list,osuinttype,loadsize,valuereg,tmpreg);
          a_load_reg_ref(list,loadsize,loadsize,tmpreg,sref.ref);
          exit;
        end
      else
        begin
          { load next value }
          extra_value_reg:=getintregister(list,osuinttype);
          tmpref:=sref.ref;
          inc(tmpref.offset,loadbitsize div 8);

          { should maybe be taken out too, can be done more efficiently }
          { on e.g. i386 with shld/shrd                                 }
          if (sref.bitindexreg = NR_NO) then
            begin
              a_load_ref_reg(list,loadsize,osuinttype,tmpref,extra_value_reg);

              fromsreg.subsetreg:=fromreg;
              fromsreg.subsetregsize:=def_cgsize(fromsize);
              tosreg.subsetreg:=valuereg;
              tosreg.subsetregsize:=def_cgsize(osuinttype);

              { transfer first part }
              fromsreg.bitlen:=loadbitsize-sref.startbit;
              tosreg.bitlen:=fromsreg.bitlen;
              if (target_info.endian=endian_big) then
                begin
                  { valuereg must contain the upper bits of the value at bits [0..loadbitsize-startbit] }

                  { upper bits of the value ... }
                  fromsreg.startbit:=sref.bitlen-(loadbitsize-sref.startbit);
                  { ... to bit 0 }
                  tosreg.startbit:=0
                end
              else
                begin
                  { valuereg must contain the lower bits of the value at bits [startbit..loadbitsize] }

                  { lower bits of the value ... }
                  fromsreg.startbit:=0;
                  { ... to startbit }
                  tosreg.startbit:=sref.startbit;
                end;
              case slopt of
                SL_SETZERO,
                SL_SETMAX:
                  a_load_regconst_subsetreg_intern(list,fromsize,subsetsize,fromreg,tosreg,slopt);
                else
                  a_load_subsetreg_subsetreg(list,subsetsize,subsetsize,fromsreg,tosreg);
              end;
{$ifndef cpuhighleveltarget}
              valuereg:=cg.makeregsize(list,valuereg,def_cgsize(loadsize));
              a_load_reg_ref(list,loadsize,loadsize,valuereg,sref.ref);
{$else}
              tmpreg:=getintregister(list,loadsize);
              a_load_reg_reg(list,osuinttype,loadsize,valuereg,tmpreg);
              a_load_reg_ref(list,loadsize,loadsize,tmpreg,sref.ref);
{$endif}

              { transfer second part }
              if (target_info.endian = endian_big) then
                begin
                  { extra_value_reg must contain the lower bits of the value at bits  }
                  { [(loadbitsize-(bitlen-(loadbitsize-startbit)))..loadbitsize]  }
                  { (loadbitsize-(bitlen-(loadbitsize-startbit))) = 2*loadbitsize }
                  { - bitlen - startbit }

                  fromsreg.startbit:=0;
                  tosreg.startbit:=2*loadbitsize-sref.bitlen-sref.startbit
                end
              else
                begin
                  { extra_value_reg must contain the upper bits of the value at bits [0..bitlen-(loadbitsize-startbit)] }

                  fromsreg.startbit:=fromsreg.bitlen;
                  tosreg.startbit:=0;
                end;
              tosreg.subsetreg:=extra_value_reg;
              fromsreg.bitlen:=sref.bitlen-fromsreg.bitlen;
              tosreg.bitlen:=fromsreg.bitlen;

              case slopt of
                SL_SETZERO,
                SL_SETMAX:
                  a_load_regconst_subsetreg_intern(list,fromsize,subsetsize,fromreg,tosreg,slopt);
                else
                  a_load_subsetreg_subsetreg(list,subsetsize,subsetsize,fromsreg,tosreg);
              end;
              tmpreg:=getintregister(list,loadsize);
              a_load_reg_reg(list,osuinttype,loadsize,extra_value_reg,tmpreg);
              a_load_reg_ref(list,loadsize,loadsize,tmpreg,tmpref);
              exit;
            end
          else
            begin
              if (sref.startbit <> 0) then
                internalerror(2006081812);
              { should be handled by normal code and will give wrong result }
              { on x86 for the '1 shl bitlen' below                         }
              if (sref.bitlen = AIntBits) then
                internalerror(2006081713);

              { generate mask to zero the bits we have to insert }
              if (slopt <> SL_SETMAX) then
                begin
                  maskreg := getintregister(list,osuinttype);
                  if (target_info.endian = endian_big) then
                    begin
                      a_load_const_reg(list,osuinttype,tcgint(((aword(1) shl sref.bitlen)-1) shl (loadbitsize-sref.bitlen)),maskreg);
                      a_op_reg_reg(list,OP_SHR,osuinttype,sref.bitindexreg,maskreg);
                    end
                  else
                    begin
                      a_load_const_reg(list,osuinttype,tcgint((aword(1) shl sref.bitlen)-1),maskreg);
                      a_op_reg_reg(list,OP_SHL,osuinttype,sref.bitindexreg,maskreg);
                    end;

                  a_op_reg_reg(list,OP_NOT,osuinttype,maskreg,maskreg);
                  a_op_reg_reg(list,OP_AND,osuinttype,maskreg,valuereg);
                end;

              { insert the value }
              if (slopt <> SL_SETZERO) then
                begin
                  tmpreg := getintregister(list,osuinttype);
                  if (slopt <> SL_SETMAX) then
                    a_load_reg_reg(list,fromsize,osuinttype,fromreg,tmpreg)
                  else if (sref.bitlen <> AIntBits) then
                    a_load_const_reg(list,osuinttype,tcgint((aword(1) shl sref.bitlen) - 1), tmpreg)
                  else
                    a_load_const_reg(list,osuinttype,-1,tmpreg);
                  if (target_info.endian = endian_big) then
                    begin
                      a_op_const_reg(list,OP_SHL,osuinttype,loadbitsize-sref.bitlen,tmpreg);
                      if not(slopt in [SL_REGNOSRCMASK,SL_SETMAX]) then
                        { mask left over bits }
                        a_op_const_reg(list,OP_AND,osuinttype,tcgint(((aword(1) shl sref.bitlen)-1) shl (loadbitsize-sref.bitlen)),tmpreg);
                      a_op_reg_reg(list,OP_SHR,osuinttype,sref.bitindexreg,tmpreg);
                    end
                  else
                    begin
                      if not(slopt in [SL_REGNOSRCMASK,SL_SETMAX]) then
                        { mask left over bits }
                        a_op_const_reg(list,OP_AND,osuinttype,tcgint((aword(1) shl sref.bitlen)-1),tmpreg);
                      a_op_reg_reg(list,OP_SHL,osuinttype,sref.bitindexreg,tmpreg);
                    end;
                  a_op_reg_reg(list,OP_OR,osuinttype,tmpreg,valuereg);
                end;
              tmpreg:=getintregister(list,loadsize);
              a_load_reg_reg(list,osuinttype,loadsize,valuereg,tmpreg);
              a_load_reg_ref(list,loadsize,loadsize,tmpreg,sref.ref);

              { make sure we do not read/write past the end of the array }
              current_asmdata.getjumplabel(hl);
              a_cmp_const_reg_label(list,osuinttype,OC_BE,loadbitsize-sref.bitlen,sref.bitindexreg,hl);

              a_load_ref_reg(list,loadsize,osuinttype,tmpref,extra_value_reg);
              tmpindexreg:=getintregister(list,osuinttype);

              { load current array value }
              if (slopt<>SL_SETZERO) then
                begin
                  tmpreg:=getintregister(list,osuinttype);
                  if (slopt<>SL_SETMAX) then
                     a_load_reg_reg(list,fromsize,osuinttype,fromreg,tmpreg)
                  else if (sref.bitlen<>AIntBits) then
                    a_load_const_reg(list,osuinttype,tcgint((aword(1) shl sref.bitlen) - 1), tmpreg)
                  else
                    a_load_const_reg(list,osuinttype,-1,tmpreg);
                end;

              { generate mask to zero the bits we have to insert }
              if (slopt<>SL_SETMAX) then
                begin
                  maskreg:=getintregister(list,osuinttype);
                  if (target_info.endian=endian_big) then
                    begin
                      a_op_const_reg_reg(list,OP_ADD,osuinttype,sref.bitlen-2*loadbitsize,sref.bitindexreg,tmpindexreg);
                      a_op_reg_reg(list,OP_NEG,osuinttype,tmpindexreg,tmpindexreg);
                      a_load_const_reg(list,osuinttype,tcgint((aword(1) shl sref.bitlen)-1),maskreg);
                      a_op_reg_reg(list,OP_SHL,osuinttype,tmpindexreg,maskreg);
                    end
                  else
                    begin
                      { Y-x = -(x-Y) }
                      a_op_const_reg_reg(list,OP_SUB,osuinttype,loadbitsize,sref.bitindexreg,tmpindexreg);
                      a_op_reg_reg(list,OP_NEG,osuinttype,tmpindexreg,tmpindexreg);
                      a_load_const_reg(list,osuinttype,tcgint((aword(1) shl sref.bitlen)-1),maskreg);
                      a_op_reg_reg(list,OP_SHR,osuinttype,tmpindexreg,maskreg);
                    end;

                  a_op_reg_reg(list,OP_NOT,osuinttype,maskreg,maskreg);
                  a_op_reg_reg(list,OP_AND,osuinttype,maskreg,extra_value_reg);
                end;

              if (slopt<>SL_SETZERO) then
                begin
                  if (target_info.endian=endian_big) then
                    a_op_reg_reg(list,OP_SHL,osuinttype,tmpindexreg,tmpreg)
                  else
                    begin
                      if not(slopt in [SL_REGNOSRCMASK,SL_SETMAX]) then
                        a_op_const_reg(list,OP_AND,osuinttype,tcgint((aword(1) shl sref.bitlen)-1),tmpreg);
                      a_op_reg_reg(list,OP_SHR,osuinttype,tmpindexreg,tmpreg);
                    end;
                  a_op_reg_reg(list,OP_OR,osuinttype,tmpreg,extra_value_reg);
                end;
{$ifndef cpuhighleveltarget}
              extra_value_reg:=cg.makeregsize(list,extra_value_reg,def_cgsize(loadsize));
              a_load_reg_ref(list,loadsize,loadsize,extra_value_reg,tmpref);
{$else}
              tmpreg:=getintregister(list,loadsize);
              a_load_reg_reg(list,osuinttype,loadsize,extra_value_reg,tmpreg);
              a_load_reg_ref(list,loadsize,loadsize,tmpreg,tmpref);
{$endif}

              a_label(list,hl);
            end;
        end;
    end;

  procedure thlcgobj.a_load_regconst_subsetreg_intern(list: TAsmList; fromsize, subsetsize: tdef; fromreg: tregister; const sreg: tsubsetregister; slopt: tsubsetloadopt);
    var
      bitmask: aword;
      tmpreg: tregister;
      subsetregdef: torddef;
      stopbit: byte;
    begin
      subsetregdef:=tcgsize2orddef(sreg.subsetregsize);
      stopbit:=sreg.startbit+sreg.bitlen;
      // on x86(64), 1 shl 32(64) = 1 instead of 0
      if (stopbit<>AIntBits) then
        bitmask:=not(((aword(1) shl stopbit)-1) xor ((aword(1) shl sreg.startbit)-1))
      else
        bitmask:=not(high(aword) xor ((aword(1) shl sreg.startbit)-1));
      if not(slopt in [SL_SETZERO,SL_SETMAX]) then
        begin
          tmpreg:=getintregister(list,subsetregdef);
          a_load_reg_reg(list,fromsize,subsetregdef,fromreg,tmpreg);
          a_op_const_reg(list,OP_SHL,subsetregdef,sreg.startbit,tmpreg);
           if (slopt<>SL_REGNOSRCMASK) then
            a_op_const_reg(list,OP_AND,subsetregdef,tcgint(not(bitmask)),tmpreg);
        end;
      if (slopt<>SL_SETMAX) then
        a_op_const_reg(list,OP_AND,subsetregdef,tcgint(bitmask),sreg.subsetreg);

      case slopt of
        SL_SETZERO : ;
        SL_SETMAX :
          if (sreg.bitlen<>AIntBits) then
            a_op_const_reg(list,OP_OR,subsetregdef,
              tcgint(((aword(1) shl sreg.bitlen)-1) shl sreg.startbit),
              sreg.subsetreg)
          else
            a_load_const_reg(list,subsetregdef,-1,sreg.subsetreg);
        else
          a_op_reg_reg(list,OP_OR,subsetregdef,tmpreg,sreg.subsetreg);
       end;
    end;

  {$pop}

  function thlcgobj.get_bit_const_ref_sref(bitnumber: tcgint; refdef: tdef; const ref: treference): tsubsetreference;
    begin
      result.ref:=ref;
      inc(result.ref.offset,bitnumber div 8);
      result.bitindexreg:=NR_NO;
      result.startbit:=bitnumber mod 8;
      result.bitlen:=1;
    end;

  function thlcgobj.get_bit_const_reg_sreg(setregsize: tdef; bitnumber: tcgint; setreg: tregister): tsubsetregister;
    begin
      result.subsetreg:=setreg;
      result.subsetregsize:=def_cgsize(setregsize);
      { subsetregs always count from the least significant to the most significant bit }
      if (target_info.endian=endian_big) then
        result.startbit:=(setregsize.size*8)-bitnumber-1
      else
        result.startbit:=bitnumber;
      result.bitlen:=1;
    end;

  function thlcgobj.get_bit_reg_ref_sref(list: TAsmList; bitnumbersize, refsize: tdef; bitnumber: tregister; const ref: treference): tsubsetreference;
    var
      tmpreg: tregister;
    begin
      result.ref:=ref;
      result.startbit:=0;
      result.bitlen:=1;

      tmpreg:=getintregister(list,ptruinttype);
      a_load_reg_reg(list,bitnumbersize,ptruinttype,bitnumber,tmpreg);
      a_op_const_reg(list,OP_SHR,ptruinttype,3,tmpreg);

      { don't assign to ref.base, that one is for pointers and this is an index
        (important for platforms like LLVM) }
      if (result.ref.index=NR_NO) then
        result.ref.index:=tmpreg
      else
        begin
          a_op_reg_reg(list,OP_ADD,ptruinttype,result.ref.index,tmpreg);
          result.ref.index:=tmpreg;
        end;
      tmpreg:=getintregister(list,ptruinttype);
      a_load_reg_reg(list,bitnumbersize,ptruinttype,bitnumber,tmpreg);
      a_op_const_reg(list,OP_AND,ptruinttype,7,tmpreg);
      result.bitindexreg:=tmpreg;
    end;

  procedure thlcgobj.a_loadfpu_ref_ref(list: TAsmList; fromsize, tosize: tdef; const ref1, ref2: treference);
    var
      reg: tregister;
      regsize: tdef;
    begin
      if (fromsize.size>=tosize.size) then
        regsize:=fromsize
      else
        regsize:=tosize;
      reg:=getfpuregister(list,regsize);
      a_loadfpu_ref_reg(list,fromsize,regsize,ref1,reg);
      a_loadfpu_reg_ref(list,regsize,tosize,reg,ref2);
    end;

  procedure thlcgobj.a_loadfpu_loc_reg(list: TAsmList; fromsize, tosize: tdef; const loc: tlocation; const reg: tregister);
    begin
      case loc.loc of
        LOC_REFERENCE, LOC_CREFERENCE:
          a_loadfpu_ref_reg(list,fromsize,tosize,loc.reference,reg);
        LOC_FPUREGISTER, LOC_CFPUREGISTER:
          a_loadfpu_reg_reg(list,fromsize,tosize,loc.register,reg);
        else
          internalerror(2010120412);
      end;
    end;

  procedure thlcgobj.a_loadfpu_reg_loc(list: TAsmList; fromsize, tosize: tdef; const reg: tregister; const loc: tlocation);
    begin
      case loc.loc of
        LOC_REFERENCE, LOC_CREFERENCE:
          a_loadfpu_reg_ref(list,fromsize,tosize,reg,loc.reference);
        LOC_FPUREGISTER, LOC_CFPUREGISTER:
          a_loadfpu_reg_reg(list,fromsize,tosize,reg,loc.register);
        else
          internalerror(2010120413);
       end;
    end;

  procedure thlcgobj.a_loadfpu_reg_cgpara(list: TAsmList; fromsize: tdef; const r: tregister; const cgpara: TCGPara);
      var
         ref : treference;
      begin
        paramanager.alloccgpara(list,cgpara);
        case cgpara.location^.loc of
          LOC_FPUREGISTER,LOC_CFPUREGISTER:
            begin
              cgpara.check_simple_location;
              a_loadfpu_reg_reg(list,fromsize,cgpara.def,r,cgpara.location^.register);
            end;
          LOC_REFERENCE,LOC_CREFERENCE:
            begin
              cgpara.check_simple_location;
              reference_reset_base(ref,cgpara.location^.reference.index,cgpara.location^.reference.offset,cgpara.alignment);
              a_loadfpu_reg_ref(list,fromsize,cgpara.def,r,ref);
            end;
          LOC_REGISTER,LOC_CREGISTER:
            begin
              { paramfpu_ref does the check_simpe_location check here if necessary }
              tg.gethltemp(list,fromsize,fromsize.size,tt_normal,ref);
              a_loadfpu_reg_ref(list,fromsize,fromsize,r,ref);
              a_loadfpu_ref_cgpara(list,fromsize,ref,cgpara);
              tg.Ungettemp(list,ref);
            end;
          else
            internalerror(2010120422);
        end;
      end;

  procedure thlcgobj.a_loadfpu_ref_cgpara(list: TAsmList; fromsize: tdef; const ref: treference; const cgpara: TCGPara);
    var
       href : treference;
//       hsize: tcgsize;
    begin
       case cgpara.location^.loc of
        LOC_FPUREGISTER,LOC_CFPUREGISTER:
          begin
            cgpara.check_simple_location;
            paramanager.alloccgpara(list,cgpara);
            a_loadfpu_ref_reg(list,fromsize,cgpara.def,ref,cgpara.location^.register);
          end;
        LOC_REFERENCE,LOC_CREFERENCE:
          begin
            cgpara.check_simple_location;
            reference_reset_base(href,cgpara.location^.reference.index,cgpara.location^.reference.offset,cgpara.alignment);
            { concatcopy should choose the best way to copy the data }
            g_concatcopy(list,fromsize,ref,href);
          end;
        (* not yet supported
        LOC_REGISTER,LOC_CREGISTER:
          begin
            { force integer size }
            hsize:=int_cgsize(tcgsize2size[size]);
{$ifndef cpu64bitalu}
            if (hsize in [OS_S64,OS_64]) then
              cg64.a_load64_ref_cgpara(list,ref,cgpara)
            else
{$endif not cpu64bitalu}
              begin
                cgpara.check_simple_location;
                a_load_ref_cgpara(list,hsize,ref,cgpara)
              end;
          end
        *)
        else
          internalerror(2010120423);
      end;
    end;
(*
  procedure thlcgobj.a_loadmm_reg_reg(list: TAsmList; fromsize, tosize: tdef; reg1, reg2: tregister; shuffle: pmmshuffle);
    begin
      cg.a_loadmm_reg_reg(list,def_cgsize(fromsize),def_cgsize(tosize),reg1,reg2,shuffle);
    end;

  procedure thlcgobj.a_loadmm_ref_reg(list: TAsmList; fromsize, tosize: tdef; const ref: treference; reg: tregister; shuffle: pmmshuffle);
    begin
      cg.a_loadmm_ref_reg(list,def_cgsize(fromsize),def_cgsize(tosize),ref,reg,shuffle);
    end;

  procedure thlcgobj.a_loadmm_reg_ref(list: TAsmList; fromsize, tosize: tdef; reg: tregister; const ref: treference; shuffle: pmmshuffle);
    begin
      cg.a_loadmm_reg_ref(list,def_cgsize(fromsize),def_cgsize(tosize),reg,ref,shuffle);
    end;

  procedure thlcgobj.a_loadmm_loc_reg(list: TAsmList; fromsize, tosize: tdef; const loc: tlocation; const reg: tregister; shuffle: pmmshuffle);
    begin
      case loc.loc of
        LOC_MMREGISTER,LOC_CMMREGISTER:
          a_loadmm_reg_reg(list,fromsize,tosize,loc.register,reg,shuffle);
        LOC_REFERENCE,LOC_CREFERENCE:
          a_loadmm_ref_reg(list,fromsize,tosize,loc.reference,reg,shuffle);
        LOC_REGISTER,LOC_CREGISTER:
          a_loadmm_intreg_reg(list,fromsize,tosize,loc.register,reg,shuffle);
        else
          internalerror(2010120414);
      end;
    end;

  procedure thlcgobj.a_loadmm_reg_loc(list: TAsmList; fromsize, tosize: tdef; const reg: tregister; const loc: tlocation; shuffle: pmmshuffle);
    begin
      case loc.loc of
        LOC_MMREGISTER,LOC_CMMREGISTER:
          a_loadmm_reg_reg(list,fromsize,tosize,reg,loc.register,shuffle);
        LOC_REFERENCE,LOC_CREFERENCE:
          a_loadmm_reg_ref(list,fromsize,tosize,reg,loc.reference,shuffle);
        else
          internalerror(2010120415);
      end;
    end;

  procedure thlcgobj.a_loadmm_reg_cgpara(list: TAsmList; fromsize: tdef; reg: tregister; const cgpara: TCGPara; shuffle: pmmshuffle);
    var
      href  : treference;
    begin
       cgpara.check_simple_location;
       paramanager.alloccgpara(list,cgpara);
       case cgpara.location^.loc of
        LOC_MMREGISTER,LOC_CMMREGISTER:
          a_loadmm_reg_reg(list,fromsize,cgpara.def,reg,cgpara.location^.register,shuffle);
        LOC_REFERENCE,LOC_CREFERENCE:
          begin
            reference_reset_base(href,cgpara.location^.reference.index,cgpara.location^.reference.offset,cgpara.alignment);
            a_loadmm_reg_ref(list,fromsize,cgpara.def,reg,href,shuffle);
          end;
        LOC_REGISTER,LOC_CREGISTER:
          begin
            if assigned(shuffle) and
               not shufflescalar(shuffle) then
              internalerror(2009112510);
             a_loadmm_reg_intreg(list,deomsize,cgpara.def,reg,cgpara.location^.register,mms_movescalar);
          end
        else
          internalerror(2010120427);
      end;
    end;

  procedure thlcgobj.a_loadmm_ref_cgpara(list: TAsmList; fromsize: tdef; const ref: treference; const cgpara: TCGPara; shuffle: pmmshuffle);
    var
       hr : tregister;
       hs : tmmshuffle;
    begin
       cgpara.check_simple_location;
       hr:=cg.getmmregister(list,cgpara.size);
       a_loadmm_ref_reg(list,deomsize,cgpara.def,ref,hr,shuffle);
       if realshuffle(shuffle) then
         begin
           hs:=shuffle^;
           removeshuffles(hs);
           a_loadmm_reg_cgpara(list,cgpara.def,hr,cgpara,@hs);
         end
       else
         a_loadmm_reg_cgpara(list,cgpara.def,hr,cgpara,shuffle);
    end;

  procedure thlcgobj.a_loadmm_loc_cgpara(list: TAsmList; fromsize: tdef; const loc: tlocation; const cgpara: TCGPara; shuffle: pmmshuffle);
    begin
{$ifdef extdebug}
      if def_cgsize(fromsize)<>loc.size then
        internalerror(2010112105);
{$endif}
      cg.a_loadmm_loc_cgpara(list,loc,cgpara,shuffle);
    end;

  procedure thlcgobj.a_opmm_reg_reg(list: TAsmList; Op: TOpCG; size: tdef; src, dst: tregister; shuffle: pmmshuffle);
    begin
      cg.a_opmm_reg_reg(list,op,def_cgsize(size),src,dst,shuffle);
    end;

  procedure thlcgobj.a_opmm_ref_reg(list: TAsmList; Op: TOpCG; size: tdef; const ref: treference; reg: tregister; shuffle: pmmshuffle);
    begin
      cg.a_opmm_ref_reg(list,op,def_cgsize(size),ref,reg,shuffle)
    end;

  procedure thlcgobj.a_opmm_loc_reg(list: TAsmList; Op: TOpCG; size: tdef; const loc: tlocation; reg: tregister; shuffle: pmmshuffle);
    begin
      cg.a_opmm_loc_reg(list,op,def_cgsize(size),loc,reg,shuffle);
    end;

  procedure thlcgobj.a_opmm_reg_ref(list: TAsmList; Op: TOpCG; size: tdef; reg: tregister; const ref: treference; shuffle: pmmshuffle);
    begin
      cg.a_opmm_reg_ref(list,op,def_cgsize(size),reg,ref,shuffle);
    end;
*)
(*
  procedure thlcgobj.a_loadmm_intreg_reg(list: TAsmList; fromsize, tosize: tdef; intreg, mmreg: tregister; shuffle: pmmshuffle);
    begin
      cg.a_loadmm_intreg_reg(list,def_cgsize(fromsize),def_cgsize(tosize),intreg,mmreg,shuffle);
    end;

  procedure thlcgobj.a_loadmm_reg_intreg(list: TAsmList; fromsize, tosize: tdef; mmreg, intreg: tregister; shuffle: pmmshuffle);
    begin
      cg.a_loadmm_reg_intreg(list,def_cgsize(fromsize),def_cgsize(tosize),mmreg,intreg,shuffle);
    end;
*)
  procedure thlcgobj.a_op_const_ref(list: TAsmList; Op: TOpCG; size: tdef; a: Aint; const ref: TReference);
    var
      tmpreg : tregister;
    begin
      tmpreg:=getintregister(list,size);
      a_load_ref_reg(list,size,size,ref,tmpreg);
      a_op_const_reg(list,op,size,a,tmpreg);
      a_load_reg_ref(list,size,size,tmpreg,ref);
    end;

  procedure thlcgobj.a_op_const_subsetreg(list: TAsmList; Op: TOpCG; size, subsetsize: tdef; a: aint; const sreg: tsubsetregister);
    var
      tmpreg: tregister;
    begin
      tmpreg:=getintregister(list,size);
      a_load_subsetreg_reg(list,subsetsize,size,sreg,tmpreg);
      a_op_const_reg(list,op,size,a,tmpreg);
      a_load_reg_subsetreg(list,size,subsetsize,tmpreg,sreg);
    end;

  procedure thlcgobj.a_op_const_subsetref(list: TAsmList; Op: TOpCG; size, subsetsize: tdef; a: aint; const sref: tsubsetreference);
    var
      tmpreg: tregister;
    begin
      tmpreg:=getintregister(list,size);
      a_load_subsetref_reg(list,subsetsize,size,sref,tmpreg);
      a_op_const_reg(list,op,size,a,tmpreg);
      a_load_reg_subsetref(list,size,subsetsize,tmpreg,sref);
    end;

  procedure thlcgobj.a_op_const_loc(list: TAsmList; Op: TOpCG; size: tdef; a: Aint; const loc: tlocation);
    begin
      case loc.loc of
        LOC_REGISTER, LOC_CREGISTER:
          a_op_const_reg(list,op,size,a,loc.register);
        LOC_REFERENCE, LOC_CREFERENCE:
          a_op_const_ref(list,op,size,a,loc.reference);
        LOC_SUBSETREG, LOC_CSUBSETREG:
          a_op_const_subsetreg(list,op,size,size,a,loc.sreg);
        LOC_SUBSETREF, LOC_CSUBSETREF:
          a_op_const_subsetref(list,op,size,size,a,loc.sref);
        else
          internalerror(2010120428);
      end;
    end;

  procedure thlcgobj.a_op_reg_ref(list: TAsmList; Op: TOpCG; size: tdef; reg: TRegister; const ref: TReference);
    var
      tmpreg: tregister;
    begin
      tmpreg:=getintregister(list,size);
      a_load_ref_reg(list,size,size,ref,tmpreg);
      case op of
        OP_NOT,OP_NEG:
          begin
            a_op_reg_reg(list,op,size,tmpreg,tmpreg);
          end;
        else
          begin
            a_op_reg_reg(list,op,size,reg,tmpreg);
          end;
      end;
      a_load_reg_ref(list,size,size,tmpreg,ref);
    end;

  procedure thlcgobj.a_op_ref_reg(list: TAsmList; Op: TOpCG; size: tdef; const ref: TReference; reg: TRegister);
      var
        tmpreg: tregister;
      begin
        case op of
          OP_NOT,OP_NEG:
            { handle it as "load ref,reg; op reg" }
            begin
              a_load_ref_reg(list,size,size,ref,reg);
              a_op_reg_reg(list,op,size,reg,reg);
            end;
          else
            begin
              tmpreg:=getintregister(list,size);
              a_load_ref_reg(list,size,size,ref,tmpreg);
              a_op_reg_reg(list,op,size,tmpreg,reg);
            end;
        end;
      end;

  procedure thlcgobj.a_op_reg_subsetreg(list: TAsmList; Op: TOpCG; opsize, destsubsetsize: tdef; reg: TRegister; const sreg: tsubsetregister);
    var
      tmpreg: tregister;
    begin
      tmpreg:=getintregister(list,opsize);
      a_load_subsetreg_reg(list,destsubsetsize,opsize,sreg,tmpreg);
      a_op_reg_reg(list,op,opsize,reg,tmpreg);
      a_load_reg_subsetreg(list,opsize,destsubsetsize,tmpreg,sreg);
    end;

  procedure thlcgobj.a_op_reg_subsetref(list: TAsmList; Op: TOpCG; opsize, destsubsetsize: tdef; reg: TRegister; const sref: tsubsetreference);
    var
      tmpreg: tregister;
    begin
      tmpreg:=getintregister(list,opsize);
      a_load_subsetref_reg(list,destsubsetsize,opsize,sref,tmpreg);
      a_op_reg_reg(list,op,opsize,reg,tmpreg);
      a_load_reg_subsetref(list,opsize,destsubsetsize,tmpreg,sref);
    end;

  procedure thlcgobj.a_op_reg_loc(list: TAsmList; Op: TOpCG; size: tdef; reg: tregister; const loc: tlocation);
    begin
      case loc.loc of
        LOC_REGISTER, LOC_CREGISTER:
          a_op_reg_reg(list,op,size,reg,loc.register);
        LOC_REFERENCE, LOC_CREFERENCE:
          a_op_reg_ref(list,op,size,reg,loc.reference);
        LOC_SUBSETREG, LOC_CSUBSETREG:
          a_op_reg_subsetreg(list,op,size,size,reg,loc.sreg);
        LOC_SUBSETREF, LOC_CSUBSETREF:
          a_op_reg_subsetref(list,op,size,size,reg,loc.sref);
        else
          internalerror(2010120429);
      end;
    end;

  procedure thlcgobj.a_op_ref_loc(list: TAsmList; Op: TOpCG; size: tdef; const ref: TReference; const loc: tlocation);
    var
      tmpreg: tregister;
    begin
      case loc.loc of
        LOC_REGISTER,LOC_CREGISTER:
          a_op_ref_reg(list,op,size,ref,loc.register);
        LOC_REFERENCE,LOC_CREFERENCE:
          begin
            tmpreg:=getintregister(list,size);
            a_load_ref_reg(list,size,size,ref,tmpreg);
            a_op_reg_ref(list,op,size,tmpreg,loc.reference);
          end;
        LOC_SUBSETREG, LOC_CSUBSETREG:
          begin
            tmpreg:=getintregister(list,size);
            a_load_subsetreg_reg(list,size,size,loc.sreg,tmpreg);
            a_op_ref_reg(list,op,size,ref,tmpreg);
            a_load_reg_subsetreg(list,size,size,tmpreg,loc.sreg);
          end;
        LOC_SUBSETREF, LOC_CSUBSETREF:
          begin
            tmpreg:=getintregister(list,size);
            a_load_subsetref_reg(list,size,size,loc.sref,tmpreg);
            a_op_ref_reg(list,op,size,ref,tmpreg);
            a_load_reg_subsetref(list,size,size,tmpreg,loc.sref);
          end;
        else
          internalerror(2010120429);
      end;
    end;

  procedure thlcgobj.a_op_const_reg_reg(list: TAsmList; op: TOpCg; size: tdef; a: aint; src, dst: tregister);
    begin
      a_load_reg_reg(list,size,size,src,dst);
      a_op_const_reg(list,op,size,a,dst);
    end;

  procedure thlcgobj.a_op_reg_reg_reg(list: TAsmList; op: TOpCg; size: tdef; src1, src2, dst: tregister);
    var
      tmpreg: tregister;
    begin
      if (dst<>src1) then
        begin
          a_load_reg_reg(list,size,size,src2,dst);
          a_op_reg_reg(list,op,size,src1,dst);
        end
      else
        begin
          { can we do a direct operation on the target register ? }
          if op in [OP_ADD,OP_MUL,OP_AND,OP_MOVE,OP_XOR,OP_IMUL,OP_OR] then
            a_op_reg_reg(list,op,size,src2,dst)
          else
            begin
              tmpreg:=getintregister(list,size);
              a_load_reg_reg(list,size,size,src2,tmpreg);
              a_op_reg_reg(list,op,size,src1,tmpreg);
              a_load_reg_reg(list,size,size,tmpreg,dst);
            end;
        end;
    end;

  procedure thlcgobj.a_op_const_reg_reg_checkoverflow(list: TAsmList; op: TOpCg; size: tdef; a: aint; src, dst: tregister; setflags: boolean; var ovloc: tlocation);
    begin
      if not setflags then
        a_op_const_reg_reg(list,op,size,a,src,dst)
      else
        internalerror(2010122910);
    end;

  procedure thlcgobj.a_op_reg_reg_reg_checkoverflow(list: TAsmList; op: TOpCg; size: tdef; src1, src2, dst: tregister; setflags: boolean; var ovloc: tlocation);
    begin
      if not setflags then
        a_op_reg_reg_reg(list,op,size,src1,src2,dst)
      else
        internalerror(2010122911);
    end;

  procedure thlcgobj.a_cmp_const_reg_label(list: TAsmList; size: tdef; cmp_op: topcmp; a: aint; reg: tregister; l: tasmlabel);
    var
      tmpreg: tregister;
    begin
      tmpreg:=getintregister(list,size);
      a_load_const_reg(list,size,a,tmpreg);
      a_cmp_reg_reg_label(list,size,cmp_op,tmpreg,reg,l);
    end;

  procedure thlcgobj.a_cmp_const_ref_label(list: TAsmList; size: tdef; cmp_op: topcmp; a: aint; const ref: treference; l: tasmlabel);
    var
      tmpreg: tregister;
    begin
      tmpreg:=getintregister(list,size);
      a_load_ref_reg(list,size,size,ref,tmpreg);
      a_cmp_const_reg_label(list,size,cmp_op,a,tmpreg,l);
    end;

  procedure thlcgobj.a_cmp_const_loc_label(list: TAsmList; size: tdef; cmp_op: topcmp; a: aint; const loc: tlocation; l: tasmlabel);
    var
      tmpreg: tregister;
    begin
      case loc.loc of
        LOC_REGISTER,LOC_CREGISTER:
          a_cmp_const_reg_label(list,size,cmp_op,a,loc.register,l);
        LOC_REFERENCE,LOC_CREFERENCE:
          a_cmp_const_ref_label(list,size,cmp_op,a,loc.reference,l);
        LOC_SUBSETREG, LOC_CSUBSETREG:
          begin
            tmpreg:=getintregister(list,size);
            a_load_subsetreg_reg(list,size,size,loc.sreg,tmpreg);
            a_cmp_const_reg_label(list,size,cmp_op,a,tmpreg,l);
          end;
        LOC_SUBSETREF, LOC_CSUBSETREF:
          begin
            tmpreg:=getintregister(list,size);
            a_load_subsetref_reg(list,size,size,loc.sref,tmpreg);
            a_cmp_const_reg_label(list,size,cmp_op,a,tmpreg,l);
          end;
        else
          internalerror(2010120430);
      end;
    end;

  procedure thlcgobj.a_cmp_ref_reg_label(list: TAsmList; size: tdef; cmp_op: topcmp; const ref: treference; reg: tregister; l: tasmlabel);
    var
      tmpreg: tregister;
    begin
      tmpreg:=getintregister(list,size);
      a_load_ref_reg(list,size,size,ref,tmpreg);
      a_cmp_reg_reg_label(list,size,cmp_op,tmpreg,reg,l);
    end;

  procedure thlcgobj.a_cmp_reg_ref_label(list: TAsmList; size: tdef; cmp_op: topcmp; reg: tregister; const ref: treference; l: tasmlabel);
    var
      tmpreg: tregister;
    begin
      tmpreg:=getintregister(list,size);
      a_load_ref_reg(list,size,size,ref,tmpreg);
      a_cmp_reg_reg_label(list,size,cmp_op,reg,tmpreg,l);
    end;

  procedure thlcgobj.a_cmp_subsetreg_reg_label(list: TAsmList; fromsubsetsize, cmpsize: tdef; cmp_op: topcmp; const sreg: tsubsetregister; reg: tregister; l: tasmlabel);
    var
      tmpreg: tregister;
    begin
      tmpreg:=getintregister(list,cmpsize);
      a_load_subsetreg_reg(list,fromsubsetsize,cmpsize,sreg,tmpreg);
      a_cmp_reg_reg_label(list,cmpsize,cmp_op,tmpreg,reg,l);
    end;

  procedure thlcgobj.a_cmp_subsetref_reg_label(list: TAsmList; fromsubsetsize, cmpsize: tdef; cmp_op: topcmp; const sref: tsubsetreference; reg: tregister; l: tasmlabel);
    var
      tmpreg: tregister;
    begin
      tmpreg:=getintregister(list,cmpsize);
      a_load_subsetref_reg(list,fromsubsetsize,cmpsize,sref,tmpreg);
      a_cmp_reg_reg_label(list,cmpsize,cmp_op,tmpreg,reg,l);
    end;

  procedure thlcgobj.a_cmp_loc_reg_label(list: TAsmList; size: tdef; cmp_op: topcmp; const loc: tlocation; reg: tregister; l: tasmlabel);
    begin
      case loc.loc of
        LOC_REGISTER,
        LOC_CREGISTER:
          a_cmp_reg_reg_label(list,size,cmp_op,loc.register,reg,l);
        LOC_REFERENCE,
        LOC_CREFERENCE :
          a_cmp_ref_reg_label(list,size,cmp_op,loc.reference,reg,l);
        LOC_CONSTANT:
          a_cmp_const_reg_label(list,size,cmp_op,loc.value,reg,l);
        LOC_SUBSETREG,
        LOC_CSUBSETREG:
          a_cmp_subsetreg_reg_label(list,size,size,cmp_op,loc.sreg,reg,l);
        LOC_SUBSETREF,
        LOC_CSUBSETREF:
          a_cmp_subsetref_reg_label(list,size,size,cmp_op,loc.sref,reg,l);
        else
          internalerror(2010120431);
      end;
    end;

  procedure thlcgobj.a_cmp_reg_loc_label(list: TAsmList; size: tdef; cmp_op: topcmp; reg: tregister; const loc: tlocation; l: tasmlabel);
    begin
      a_cmp_loc_reg_label(list,size,swap_opcmp(cmp_op),loc,reg,l);
    end;

  procedure thlcgobj.a_cmp_ref_loc_label(list: TAsmList; size: tdef; cmp_op: topcmp; const ref: treference; const loc: tlocation; l: tasmlabel);
    var
      tmpreg: tregister;
    begin
      case loc.loc of
        LOC_REGISTER,LOC_CREGISTER:
          a_cmp_ref_reg_label(list,size,cmp_op,ref,loc.register,l);
        LOC_REFERENCE,LOC_CREFERENCE:
          begin
            tmpreg:=getintregister(list,size);
            a_load_ref_reg(list,size,size,loc.reference,tmpreg);
            a_cmp_ref_reg_label(list,size,cmp_op,ref,tmpreg,l);
          end;
        LOC_CONSTANT:
          begin
            a_cmp_const_ref_label(list,size,swap_opcmp(cmp_op),loc.value,ref,l);
          end;
        LOC_SUBSETREG, LOC_CSUBSETREG:
          begin
            tmpreg:=getintregister(list,size);
            a_load_ref_reg(list,size,size,loc.reference,tmpreg);
            a_cmp_subsetreg_reg_label(list,size,size,swap_opcmp(cmp_op),loc.sreg,tmpreg,l);
          end;
        LOC_SUBSETREF, LOC_CSUBSETREF:
          begin
            tmpreg:=getintregister(list,size);
            a_load_ref_reg(list,size,size,loc.reference,tmpreg);
            a_cmp_subsetref_reg_label(list,size,size,swap_opcmp(cmp_op),loc.sref,tmpreg,l);
          end;
        else
          internalerror(2010120432);
      end;
    end;

  procedure thlcgobj.g_concatcopy(list: TAsmList; size: tdef; const source, dest: treference);
    begin
{
      if use_vectorfpu(size) then
        a_loadmm_ref_ref()
      else
 }
      if size.typ<>floatdef then
        a_load_ref_ref(list,size,size,source,dest)
      else
        a_loadfpu_ref_ref(list,size,size,source,dest);
    end;

  procedure thlcgobj.g_concatcopy_unaligned(list: TAsmList; size: tdef; const source, dest: treference);
    begin
      g_concatcopy(list,size,source,dest);
    end;

  procedure thlcgobj.g_rangecheck(list: TAsmList; const l: tlocation; fromdef, todef: tdef);
    var
{$if defined(cpu64bitalu) or defined(cpu32bitalu)}
      aintmax: aint;
{$else}
      aintmax: longint;
{$endif}
      neglabel : tasmlabel;
      hreg : tregister;
      lto,hto,
      lfrom,hfrom : TConstExprInt;
      fromsize, tosize: cardinal;
      maxdef: tdef;
      from_signed, to_signed: boolean;
    begin
      { range checking on and range checkable value? }
      if not(cs_check_range in current_settings.localswitches) or
         not(fromdef.typ in [orddef,enumdef]) or
         { C-style booleans can't really fail range checks, }
         { all values are always valid                      }
         is_cbool(todef) then
        exit;
{$if not defined(cpuhighleveltarget) and not defined(cpu64bitalu)}
        { handle 64bit rangechecks separate for 32bit processors }
        if is_64bit(fromdef) or is_64bit(todef) then
          begin
             cg64.g_rangecheck64(list,l,fromdef,todef);
             exit;
          end;
{$endif ndef cpuhighleveltarget and ndef cpu64bitalu}
      { only check when assigning to scalar, subranges are different, }
      { when todef=fromdef then the check is always generated         }
      getrange(fromdef,lfrom,hfrom);
      getrange(todef,lto,hto);
      from_signed := is_signed(fromdef);
      to_signed := is_signed(todef);
      { check the rangedef of the array, not the array itself }
      { (only change now, since getrange needs the arraydef)   }
      if (todef.typ = arraydef) then
        todef := tarraydef(todef).rangedef;
      { no range check if from and to are equal and are both longint/dword }
      { (if we have a 32bit processor) or int64/qword, since such          }
      { operations can at most cause overflows (JM)                        }
      { Note that these checks are mostly processor independent, they only }
      { have to be changed once we introduce 64bit subrange types          }
{$if defined(cpuhighleveltarget) or defined(cpu64bitalu)}
      if (fromdef=todef) and
         (fromdef.typ=orddef) and
         (((((torddef(fromdef).ordtype=s64bit) and
             (lfrom = low(int64)) and
             (hfrom = high(int64))) or
            ((torddef(fromdef).ordtype=u64bit) and
             (lfrom = low(qword)) and
             (hfrom = high(qword))) or
            ((torddef(fromdef).ordtype=scurrency) and
             (lfrom = low(int64)) and
             (hfrom = high(int64)))))) then
        exit;
{$endif cpuhighleveltarget or cpu64bitalu}
      { 32 bit operations are automatically widened to 64 bit on 64 bit addr
        targets }
{$ifdef cpu32bitaddr}
      if (fromdef = todef) and
         (fromdef.typ=orddef) and
         (((((torddef(fromdef).ordtype = s32bit) and
             (lfrom = int64(low(longint))) and
             (hfrom = int64(high(longint)))) or
            ((torddef(fromdef).ordtype = u32bit) and
             (lfrom = low(cardinal)) and
             (hfrom = high(cardinal)))))) then
        exit;
{$endif cpu32bitaddr}

      { optimize some range checks away in safe cases }
      fromsize := fromdef.size;
      tosize := todef.size;
      if ((from_signed = to_signed) or
          (not from_signed)) and
         (lto<=lfrom) and (hto>=hfrom) and
         (fromsize <= tosize) then
        begin
          { if fromsize < tosize, and both have the same signed-ness or }
          { fromdef is unsigned, then all bit patterns from fromdef are }
          { valid for todef as well                                     }
          if (fromsize < tosize) then
            exit;
          if (fromsize = tosize) and
             (from_signed = to_signed) then
            { only optimize away if all bit patterns which fit in fromsize }
            { are valid for the todef                                      }
            begin
{$ifopt Q+}
{$define overflowon}
{$Q-}
{$endif}
{$ifopt R+}
{$define rangeon}
{$R-}
{$endif}
              if to_signed then
                begin
                  { calculation of the low/high ranges must not overflow 64 bit
                   otherwise we end up comparing with zero for 64 bit data types on
                   64 bit processors }
                  if (lto = (int64(-1) << (tosize * 8 - 1))) and
                     (hto = (-((int64(-1) << (tosize * 8 - 1))+1))) then
                    exit
                end
              else
                begin
                  { calculation of the low/high ranges must not overflow 64 bit
                   otherwise we end up having all zeros for 64 bit data types on
                   64 bit processors }
                  if (lto = 0) and
                     (qword(hto) = (qword(-1) >> (64-(tosize * 8))) ) then
                    exit
                end;
{$ifdef overflowon}
{$Q+}
{$undef overflowon}
{$endif}
{$ifdef rangeon}
{$R+}
{$undef rangeon}
{$endif}
            end
        end;

      { depending on the types involved, we perform the range check for 64 or
        for 32 bit }
      if fromsize=8 then
        maxdef:=fromdef
      else
        maxdef:=todef;
{$if sizeof(aintmax) = 8}
      if maxdef.size=8 then
        aintmax:=high(int64)
      else
{$endif}
        begin
          aintmax:=high(longint);
          maxdef:=u32inttype;
        end;

      { generate the rangecheck code for the def where we are going to }
      { store the result                                               }

      { use the trick that                                                 }
      { a <= x <= b <=> 0 <= x-a <= b-a <=> unsigned(x-a) <= unsigned(b-a) }

      { To be able to do that, we have to make sure however that either    }
      { fromdef and todef are both signed or unsigned, or that we leave    }
      { the parts < 0 and > maxlongint out                                 }

      if from_signed xor to_signed then
        begin
           if from_signed then
             { from is signed, to is unsigned }
             begin
               { if high(from) < 0 -> always range error }
               if (hfrom < 0) or
                  { if low(to) > maxlongint also range error }
                  (lto > aintmax) then
                 begin
                   g_call_system_proc(list,'fpc_rangeerror');
                   exit
                 end;
               { from is signed and to is unsigned -> when looking at to }
               { as an signed value, it must be < maxaint (otherwise     }
               { it will become negative, which is invalid since "to" is unsigned) }
               if hto > aintmax then
                 hto := aintmax;
             end
           else
             { from is unsigned, to is signed }
             begin
               if (lfrom > aintmax) or
                  (hto < 0) then
                 begin
                   g_call_system_proc(list,'fpc_rangeerror');
                   exit
                 end;
               { from is unsigned and to is signed -> when looking at to }
               { as an unsigned value, it must be >= 0 (since negative   }
               { values are the same as values > maxlongint)             }
               if lto < 0 then
                 lto := 0;
             end;
        end;
      hreg:=getintregister(list,maxdef);
      a_load_loc_reg(list,fromdef,maxdef,l,hreg);
      a_op_const_reg(list,OP_SUB,maxdef,tcgint(int64(lto)),hreg);
      current_asmdata.getjumplabel(neglabel);
      {
      if from_signed then
        a_cmp_const_reg_label(list,OS_INT,OC_GTE,aint(hto-lto),hreg,neglabel)
      else
      }
      if qword(hto-lto)>qword(aintmax) then
        a_cmp_const_reg_label(list,maxdef,OC_BE,aintmax,hreg,neglabel)
      else
        a_cmp_const_reg_label(list,maxdef,OC_BE,tcgint(int64(hto-lto)),hreg,neglabel);
      g_call_system_proc(list,'fpc_rangeerror');
      a_label(list,neglabel);
    end;

  procedure thlcgobj.g_profilecode(list: TAsmList);
    begin
    end;

  procedure thlcgobj.g_allocload_reg_reg(list: TAsmList; regsize: tdef; const fromreg: tregister; out toreg: tregister; regtyp: tregistertype);
    begin
      case regtyp of
        R_INTREGISTER:
          toreg:=getintregister(list,regsize);
        R_ADDRESSREGISTER:
          toreg:=getaddressregister(list,regsize);
        R_FPUREGISTER:
          toreg:=getfpuregister(list,regsize);
      end;
      a_load_reg_reg(list,regsize,regsize,fromreg,toreg);
    end;

  procedure thlcgobj.g_reference_loc(list: TAsmList; def: tdef; const fromloc: tlocation; out toloc: tlocation);

    procedure handle_reg_move(regsize: tdef; const fromreg: tregister; out toreg: tregister; regtyp: tregistertype);
      begin
        case regtyp of
          R_INTREGISTER:
            toreg:=getintregister(list,regsize);
          R_ADDRESSREGISTER:
            toreg:=getaddressregister(list,regsize);
          R_FPUREGISTER:
            toreg:=getfpuregister(list,regsize);
        end;
        a_load_reg_reg(list,regsize,regsize,fromreg,toreg);
      end;

    begin
      toloc:=fromloc;
      case fromloc.loc of
        { volatile location, can't get a permanent reference }
        LOC_REGISTER,
        LOC_FPUREGISTER:
          internalerror(2012012702);
        LOC_CONSTANT:
          { finished }
          ;
        LOC_CREGISTER:
          handle_reg_move(def,fromloc.reference.index,toloc.reference.index,R_INTREGISTER);
        LOC_CFPUREGISTER:
          handle_reg_move(def,fromloc.reference.index,toloc.reference.index,R_FPUREGISTER);
        { although LOC_CREFERENCE cannot be an lvalue, we may want to take a
          reference to such a location for multiple reading }
        LOC_CREFERENCE,
        LOC_REFERENCE:
          begin
            if (fromloc.reference.base<>NR_NO) and
               (fromloc.reference.base<>current_procinfo.framepointer) and
               (fromloc.reference.base<>NR_STACK_POINTER_REG) then
              handle_reg_move(voidpointertype,fromloc.reference.base,toloc.reference.base,getregtype(fromloc.reference.base));
            if (fromloc.reference.index<>NR_NO) and
               (fromloc.reference.index<>current_procinfo.framepointer) and
               (fromloc.reference.index<>NR_STACK_POINTER_REG) then
              handle_reg_move(voidpointertype,fromloc.reference.index,toloc.reference.index,getregtype(fromloc.reference.index));
          end;
        else
          internalerror(2012012701);
      end;
    end;

  procedure thlcgobj.location_force_reg(list: TAsmList; var l: tlocation; src_size, dst_size: tdef; maybeconst: boolean);
    var
      hregister,
      hregister2: tregister;
      hl : tasmlabel;
      oldloc : tlocation;
    begin
      oldloc:=l;
      hregister:=getregisterfordef(list,dst_size);
      { load value in new register }
      case l.loc of
{$ifdef cpuflags}
        LOC_FLAGS :
          g_flags2reg(list,dst_size,l.resflags,hregister);
{$endif cpuflags}
        LOC_JUMP :
          begin
            a_label(list,current_procinfo.CurrTrueLabel);
            a_load_const_reg(list,dst_size,1,hregister);
            current_asmdata.getjumplabel(hl);
            a_jmp_always(list,hl);
            a_label(list,current_procinfo.CurrFalseLabel);
            a_load_const_reg(list,dst_size,0,hregister);
            a_label(list,hl);
          end;
        else
          begin
            { load_loc_reg can only handle size >= l.size, when the
              new size is smaller then we need to adjust the size
              of the orignal and maybe recalculate l.register for i386 }
            if (dst_size.size<src_size.size) then
              begin
                hregister2:=getregisterfordef(list,src_size);
                { prevent problems with memory locations -- at this high
                  level we cannot twiddle with the reference offset, since
                  that may not mean anything (e.g., it refers to fixed-sized
                  stack slots on Java) }
                a_load_loc_reg(list,src_size,src_size,l,hregister2);
                a_load_reg_reg(list,src_size,dst_size,hregister2,hregister);
              end
            else
              a_load_loc_reg(list,src_size,dst_size,l,hregister);
          end;
      end;
      if (l.loc <> LOC_CREGISTER) or
         not maybeconst then
        location_reset(l,LOC_REGISTER,def_cgsize(dst_size))
      else
        location_reset(l,LOC_CREGISTER,def_cgsize(dst_size));
      l.register:=hregister;
      { Release temp if it was a reference }
      if oldloc.loc=LOC_REFERENCE then
        location_freetemp(list,oldloc);
    end;

  procedure thlcgobj.location_force_fpureg(list: TAsmList; var l: tlocation; size: tdef; maybeconst: boolean);
    var
      reg : tregister;
    begin
      if (l.loc<>LOC_FPUREGISTER)  and
         ((l.loc<>LOC_CFPUREGISTER) or (not maybeconst)) then
        begin
          { if it's in an mm register, store to memory first }
          if (l.loc in [LOC_MMREGISTER,LOC_CMMREGISTER]) then
            internalerror(2011012903);
          reg:=getfpuregister(list,size);
          a_loadfpu_loc_reg(list,size,size,l,reg);
          location_freetemp(list,l);
          location_reset(l,LOC_FPUREGISTER,l.size);
          l.register:=reg;
        end;
    end;

  procedure thlcgobj.location_force_mem(list: TAsmList; var l: tlocation; size: tdef);
    var
      r : treference;
      forcesize: aint;
    begin
      case l.loc of
        LOC_FPUREGISTER,
        LOC_CFPUREGISTER :
          begin
            tg.gethltemp(list,size,size.size,tt_normal,r);
            a_loadfpu_reg_ref(list,size,size,l.register,r);
            location_reset_ref(l,LOC_REFERENCE,l.size,0);
            l.reference:=r;
          end;
(*
        LOC_MMREGISTER,
        LOC_CMMREGISTER:
          begin
            tg.gethltemp(list,size,size.size,tt_normal,r);
            cg.a_loadmm_reg_ref(list,l.size,l.size,l.register,r,mms_movescalar);
            location_reset_ref(l,LOC_REFERENCE,l.size,0);
            l.reference:=r;
          end;
*)
        LOC_CONSTANT,
        LOC_REGISTER,
        LOC_CREGISTER,
        LOC_SUBSETREG,
        LOC_CSUBSETREG,
        LOC_SUBSETREF,
        LOC_CSUBSETREF:
          begin
            if not is_dynamic_array(size) and
               not is_open_array(size) then
              forcesize:=size.size
            else
              forcesize:=voidpointertype.size;
            tg.gethltemp(list,size,forcesize,tt_normal,r);
            a_load_loc_ref(list,size,size,l,r);
            location_reset_ref(l,LOC_REFERENCE,l.size,0);
            l.reference:=r;
          end;
        LOC_CREFERENCE,
        LOC_REFERENCE : ;
        else
          internalerror(2011010304);
      end;
    end;

    procedure thlcgobj.location_get_data_ref(list: TAsmList; def: tdef; const l: tlocation; var ref: treference; loadref: boolean; alignment: longint);
      begin
        case l.loc of
          LOC_REGISTER,
          LOC_CREGISTER :
            begin
              if not loadref then
                internalerror(200410231);
              reference_reset_base(ref,l.register,0,alignment);
            end;
          LOC_REFERENCE,
          LOC_CREFERENCE :
            begin
              if loadref then
                begin
                  reference_reset_base(ref,getaddressregister(list,voidpointertype),0,alignment);
                  { it's a pointer to def }
                  a_load_ref_reg(list,voidpointertype,voidpointertype,l.reference,ref.base);
                end
              else
                ref:=l.reference;
            end;
          else
            internalerror(200309181);
        end;
      end;

  procedure thlcgobj.maketojumpbool(list: TAsmList; p: tnode);
  {
    produces jumps to true respectively false labels using boolean expressions

    depending on whether the loading of regvars is currently being
    synchronized manually (such as in an if-node) or automatically (most of
    the other cases where this procedure is called), loadregvars can be
    "lr_load_regvars" or "lr_dont_load_regvars"
  }
    var
      storepos : tfileposinfo;
    begin
       if nf_error in p.flags then
         exit;
       storepos:=current_filepos;
       current_filepos:=p.fileinfo;
       if is_boolean(p.resultdef) then
         begin
            if is_constboolnode(p) then
              begin
                 if Tordconstnode(p).value.uvalue<>0 then
                   a_jmp_always(list,current_procinfo.CurrTrueLabel)
                 else
                   a_jmp_always(list,current_procinfo.CurrFalseLabel)
              end
            else
              begin
                 case p.location.loc of
                   LOC_SUBSETREG,LOC_CSUBSETREG,
                   LOC_SUBSETREF,LOC_CSUBSETREF,
                   LOC_CREGISTER,LOC_REGISTER,LOC_CREFERENCE,LOC_REFERENCE :
                     begin
                       a_cmp_const_loc_label(list,p.resultdef,OC_NE,0,p.location,current_procinfo.CurrTrueLabel);
                       a_jmp_always(list,current_procinfo.CurrFalseLabel);
                     end;
                   LOC_JUMP:
                     ;
{$ifdef cpuflags}
                   LOC_FLAGS :
                     begin
                       a_jmp_flags(list,p.location.resflags,current_procinfo.CurrTrueLabel);
                       a_jmp_always(list,current_procinfo.CurrFalseLabel);
                     end;
{$endif cpuflags}
                   else
                     begin
                       printnode(output,p);
                       internalerror(2011010418);
                     end;
                 end;
              end;
         end
       else
         internalerror(2011010419);
       current_filepos:=storepos;
    end;

  procedure thlcgobj.gen_proc_symbol(list: TAsmList);
    var
      item,
      previtem : TCmdStrListItem;
    begin
      previtem:=nil;
      item := TCmdStrListItem(current_procinfo.procdef.aliasnames.first);
      while assigned(item) do
        begin
{$ifdef arm}
          if current_settings.cputype in cpu_thumb2 then
            list.concat(tai_thumb_func.create);
{$endif arm}
          { "double link" all procedure entry symbols via .reference }
          { directives on darwin, because otherwise the linker       }
          { sometimes strips the procedure if only on of the symbols }
          { is referenced                                            }
          if assigned(previtem) and
             (target_info.system in systems_darwin) then
            list.concat(tai_directive.create(asd_reference,item.str));
          if (cs_profile in current_settings.moduleswitches) or
            (po_global in current_procinfo.procdef.procoptions) then
            list.concat(Tai_symbol.createname_global(item.str,AT_FUNCTION,0))
          else
            list.concat(Tai_symbol.createname(item.str,AT_FUNCTION,0));
          if assigned(previtem) and
             (target_info.system in systems_darwin) then
            list.concat(tai_directive.create(asd_reference,previtem.str));
          if not(af_stabs_use_function_absolute_addresses in target_asm.flags) then
            list.concat(Tai_function_name.create(item.str));
          previtem:=item;
          item := TCmdStrListItem(item.next);
        end;
      current_procinfo.procdef.procstarttai:=tai(list.last);
    end;

  procedure thlcgobj.gen_proc_symbol_end(list: TAsmList);
    begin
      list.concat(Tai_symbol_end.Createname(current_procinfo.procdef.mangledname));

      current_procinfo.procdef.procendtai:=tai(list.last);

      if (current_module.islibrary) then
        if (current_procinfo.procdef.proctypeoption = potype_proginit) then
          { setinitname may generate a new section -> don't add to the
            current list, because we assume this remains a text section }
          exportlib.setinitname(current_asmdata.AsmLists[al_exports],current_procinfo.procdef.mangledname);

      if (current_procinfo.procdef.proctypeoption=potype_proginit) then
        begin
         if (target_info.system in (systems_darwin+[system_powerpc_macos]+systems_aix)) and
            not(current_module.islibrary) then
           begin
            new_section(list,sec_code,'',4);
            list.concat(tai_symbol.createname_global(
              target_info.cprefix+mainaliasname,AT_FUNCTION,0));
            { keep argc, argv and envp properly on the stack }
            if not(target_info.system in systems_aix) then
              cg.a_jmp_name(list,target_info.cprefix+'FPC_SYSTEMMAIN')
            else
              cg.a_call_name(list,target_info.cprefix+'FPC_SYSTEMMAIN',false)
           end;
        end;
    end;

  procedure thlcgobj.gen_initialize_code(list: TAsmList);
    begin
      { initialize local data like ansistrings }
      case current_procinfo.procdef.proctypeoption of
         potype_unitinit:
           begin
              { this is also used for initialization of variables in a
                program which does not have a globalsymtable }
              if assigned(current_module.globalsymtable) then
                TSymtable(current_module.globalsymtable).SymList.ForEachCall(@initialize_data,list);
              TSymtable(current_module.localsymtable).SymList.ForEachCall(@initialize_data,list);
              TSymtable(current_module.localsymtable).SymList.ForEachCall(@initialize_regvars,list);
           end;
         { units have seperate code for initilization and finalization }
         potype_unitfinalize: ;
         { program init/final is generated in separate procedure }
         potype_proginit:
           begin
             TSymtable(current_module.localsymtable).SymList.ForEachCall(@initialize_regvars,list);
           end;
         else
           current_procinfo.procdef.localst.SymList.ForEachCall(@initialize_data,list);
      end;

      { initialises temp. ansi/wide string data }
      if (current_procinfo.procdef.proctypeoption<>potype_exceptfilter) then
        inittempvariables(list);

{$ifdef OLDREGVARS}
      load_regvars(list,nil);
{$endif OLDREGVARS}
    end;

  procedure thlcgobj.gen_finalize_code(list: TAsmList);
    var
      old_current_procinfo: tprocinfo;
    begin
      old_current_procinfo:=current_procinfo;
      if (current_procinfo.procdef.proctypeoption=potype_exceptfilter) then
        begin
          if (current_procinfo.parent.finalize_procinfo<>current_procinfo) then
            exit;
          current_procinfo:=current_procinfo.parent;
        end;

{$ifdef OLDREGVARS}
      cleanup_regvars(list);
{$endif OLDREGVARS}

      { finalize temporary data }
      finalizetempvariables(list);

      { finalize local data like ansistrings}
      case current_procinfo.procdef.proctypeoption of
         potype_unitfinalize:
           begin
              { this is also used for initialization of variables in a
                program which does not have a globalsymtable }
              if assigned(current_module.globalsymtable) then
                TSymtable(current_module.globalsymtable).SymList.ForEachCall(@finalize_static_data,list);
              TSymtable(current_module.localsymtable).SymList.ForEachCall(@finalize_static_data,list);
           end;
         { units/progs have separate code for initialization and finalization }
         potype_unitinit: ;
         { program init/final is generated in separate procedure }
         potype_proginit: ;
         else
           current_procinfo.procdef.localst.SymList.ForEachCall(@finalize_local_vars,list);
      end;

      { finalize paras data }
      if assigned(current_procinfo.procdef.parast) and
         not(po_assembler in current_procinfo.procdef.procoptions) then
        current_procinfo.procdef.parast.SymList.ForEachCall(@final_paras,list);
      current_procinfo:=old_current_procinfo;
    end;

  procedure thlcgobj.gen_entry_code(list: TAsmList);
    begin
      { the actual profile code can clobber some registers,
        therefore if the context must be saved, do it before
        the actual call to the profile code
      }
      if (cs_profile in current_settings.moduleswitches) and
         not(po_assembler in current_procinfo.procdef.procoptions) then
        begin
          { non-win32 can call mcout even in main }
          if not (target_info.system in [system_i386_win32,system_i386_wdosx]) or
             not (current_procinfo.procdef.proctypeoption=potype_proginit) then
            begin
              g_profilecode(list);
            end;
        end;

      { TODO: create high level version (create compilerprocs in system unit,
          look up procdef, use hlcgobj.a_call_name()) }

      { call startup helpers from main program }
      if (current_procinfo.procdef.proctypeoption=potype_proginit) then
       begin
         { initialize units }
         cg.allocallcpuregisters(list);
         if not(current_module.islibrary) then
           cg.a_call_name(list,'FPC_INITIALIZEUNITS',false)
         else
           cg.a_call_name(list,'FPC_LIBINITIALIZEUNITS',false);
         cg.deallocallcpuregisters(list);
       end;

      list.concat(Tai_force_line.Create);

{$ifdef OLDREGVARS}
      load_regvars(list,nil);
{$endif OLDREGVARS}
    end;

  procedure thlcgobj.gen_exit_code(list: TAsmList);
    begin
      { TODO: create high level version (create compilerproc in system unit,
          look up procdef, use hlcgobj.a_call_name()) }

      { call __EXIT for main program }
      if (not DLLsource) and
         (current_procinfo.procdef.proctypeoption=potype_proginit) then
        cg.a_call_name(list,'FPC_DO_EXIT',false);
    end;

  procedure thlcgobj.inittempvariables(list: TAsmList);
    var
      hp : ptemprecord;
      href : treference;
    begin
      hp:=tg.templist;
      while assigned(hp) do
       begin
         if assigned(hp^.def) and
            is_managed_type(hp^.def) then
          begin
            reference_reset_base(href,current_procinfo.framepointer,hp^.pos,sizeof(pint));
            g_initialize(list,hp^.def,href);
          end;
         hp:=hp^.next;
       end;
    end;

  procedure thlcgobj.initialize_data(p: TObject; arg: pointer);
    var
      OldAsmList : TAsmList;
      hp : tnode;
    begin
      if (tsym(p).typ = localvarsym) and
         { local (procedure or unit) variables only need initialization if
           they are used }
         ((tabstractvarsym(p).refs>0) or
          { managed return symbols must be inited }
          ((tsym(p).typ=localvarsym) and (vo_is_funcret in tlocalvarsym(p).varoptions))
         ) and
         not(vo_is_typed_const in tabstractvarsym(p).varoptions) and
         not(vo_is_external in tabstractvarsym(p).varoptions) and
         not(vo_is_default_var in tabstractvarsym(p).varoptions) and
         (is_managed_type(tabstractvarsym(p).vardef) or
          ((m_iso in current_settings.modeswitches) and (tabstractvarsym(p).vardef.typ=filedef))
         ) then
        begin
          OldAsmList:=current_asmdata.CurrAsmList;
          current_asmdata.CurrAsmList:=TAsmList(arg);
          hp:=cnodeutils.initialize_data_node(cloadnode.create(tsym(p),tsym(p).owner),false);
          firstpass(hp);
          secondpass(hp);
          hp.free;
          current_asmdata.CurrAsmList:=OldAsmList;
        end;
    end;

  procedure thlcgobj.finalizetempvariables(list: TAsmList);
    var
      hp : ptemprecord;
      href : treference;
    begin
      hp:=tg.templist;
      while assigned(hp) do
       begin
         if assigned(hp^.def) and
            is_managed_type(hp^.def) then
          begin
            include(current_procinfo.flags,pi_needs_implicit_finally);
            reference_reset_base(href,current_procinfo.framepointer,hp^.pos,sizeof(pint));
            g_finalize(list,hp^.def,href);
          end;
         hp:=hp^.next;
       end;
    end;

  procedure thlcgobj.initialize_regvars(p: TObject; arg: pointer);
    var
      href : treference;
    begin
      if (tsym(p).typ=staticvarsym) then
       begin
         { Static variables can have the initialloc only set to LOC_CxREGISTER
           or LOC_INVALID, for explaination see gen_alloc_symtable (PFV) }
         case tstaticvarsym(p).initialloc.loc of
           LOC_CREGISTER :
             begin
{$ifndef cpu64bitalu}
               if (tstaticvarsym(p).initialloc.size in [OS_64,OS_S64]) then
                 cg64.a_load64_const_reg(TAsmList(arg),0,tstaticvarsym(p).initialloc.register64)
               else
{$endif not cpu64bitalu}
                 a_load_const_reg(TAsmList(arg),tstaticvarsym(p).vardef,0,
                     tstaticvarsym(p).initialloc.register);
             end;
(*
           LOC_CMMREGISTER :
             { clear the whole register }
             cg.a_opmm_reg_reg(TAsmList(arg),OP_XOR,reg_cgsize(tstaticvarsym(p).initialloc.register),
               tstaticvarsym(p).initialloc.register,
               tstaticvarsym(p).initialloc.register,
               nil);
*)
           LOC_CFPUREGISTER :
             begin
               { initialize fpu regvar by loading from memory }
               reference_reset_symbol(href,
                 current_asmdata.RefAsmSymbol(tstaticvarsym(p).mangledname), 0,
                 var_align(tstaticvarsym(p).vardef.alignment));
               a_loadfpu_ref_reg(TAsmList(arg), tstaticvarsym(p).vardef,
                 tstaticvarsym(p).vardef, href, tstaticvarsym(p).initialloc.register);
             end;
           LOC_INVALID :
             ;
           else
             internalerror(200410124);
         end;
       end;
    end;

  procedure thlcgobj.finalize_sym(asmlist: TAsmList; sym: tsym);
    var
      hp : tnode;
      OldAsmList : TAsmList;
    begin
      include(current_procinfo.flags,pi_needs_implicit_finally);
      OldAsmList:=current_asmdata.CurrAsmList;
      current_asmdata.CurrAsmList:=asmlist;
      hp:=cloadnode.create(sym,sym.owner);
      if (sym.typ=staticvarsym) and (vo_force_finalize in tstaticvarsym(sym).varoptions) then
        include(tloadnode(hp).loadnodeflags,loadnf_isinternal_ignoreconst);
      hp:=cnodeutils.finalize_data_node(hp);
      firstpass(hp);
      secondpass(hp);
      hp.free;
      current_asmdata.CurrAsmList:=OldAsmList;
    end;

  procedure thlcgobj.finalize_local_vars(p: TObject; arg: pointer);
    begin
      if (tsym(p).typ=localvarsym) and
         (tlocalvarsym(p).refs>0) and
         not(vo_is_external in tlocalvarsym(p).varoptions) and
         not(vo_is_funcret in tlocalvarsym(p).varoptions) and
         not(vo_is_default_var in tabstractvarsym(p).varoptions) and
         is_managed_type(tlocalvarsym(p).vardef) then
        finalize_sym(TAsmList(arg),tsym(p));
    end;

  procedure thlcgobj.finalize_static_data(p: TObject; arg: pointer);
    var
      i : longint;
      pd : tprocdef;
    begin
      case tsym(p).typ of
        staticvarsym :
          begin
                { local (procedure or unit) variables only need finalization
                  if they are used
                }
            if ((tstaticvarsym(p).refs>0) or
                { global (unit) variables always need finalization, since
                  they may also be used in another unit
                }
                (tstaticvarsym(p).owner.symtabletype=globalsymtable)) and
                (
                  (tstaticvarsym(p).varspez<>vs_const) or
                  (vo_force_finalize in tstaticvarsym(p).varoptions)
                ) and
               not(vo_is_funcret in tstaticvarsym(p).varoptions) and
               not(vo_is_external in tstaticvarsym(p).varoptions) and
               is_managed_type(tstaticvarsym(p).vardef) then
              finalize_sym(TAsmList(arg),tsym(p));
          end;
        procsym :
          begin
            for i:=0 to tprocsym(p).ProcdefList.Count-1 do
              begin
                pd:=tprocdef(tprocsym(p).ProcdefList[i]);
                if assigned(pd.localst) and
                   (pd.procsym=tprocsym(p)) and
                   (pd.localst.symtabletype<>staticsymtable) then
                  pd.localst.SymList.ForEachCall(@finalize_static_data,arg);
              end;
          end;
      end;
    end;

  procedure thlcgobj.final_paras(p: TObject; arg: pointer);
    var
      list : TAsmList;
      href : treference;
      hsym : tparavarsym;
      eldef : tdef;
      highloc : tlocation;
    begin
      if not(tsym(p).typ=paravarsym) then
        exit;
      list:=TAsmList(arg);
      if is_managed_type(tparavarsym(p).vardef) then
       begin
         if (tparavarsym(p).varspez=vs_value) then
          begin
            include(current_procinfo.flags,pi_needs_implicit_finally);
            location_get_data_ref(list,tparavarsym(p).vardef,tparavarsym(p).localloc,href,is_open_array(tparavarsym(p).vardef),sizeof(pint));
            if is_open_array(tparavarsym(p).vardef) then
              begin
                if paramanager.push_high_param(tparavarsym(p).varspez,tparavarsym(p).vardef,current_procinfo.procdef.proccalloption) then
                  begin
                    hsym:=tparavarsym(get_high_value_sym(tparavarsym(p)));
                    if not assigned(hsym) then
                      internalerror(201003032);
                    highloc:=hsym.initialloc
                  end
                else
                  highloc.loc:=LOC_INVALID;
                eldef:=tarraydef(tparavarsym(p).vardef).elementdef;
                g_array_rtti_helper(list,eldef,href,highloc,'FPC_FINALIZE_ARRAY');
              end
            else
              g_finalize(list,tparavarsym(p).vardef,href);
          end;
       end;
      { open arrays can contain elements requiring init/final code, so the else has been removed here }
      if (tparavarsym(p).varspez=vs_value) and
         (is_open_array(tparavarsym(p).vardef) or
          is_array_of_const(tparavarsym(p).vardef)) then
        begin
          { cdecl functions don't have a high pointer so it is not possible to generate
            a local copy }
          if not(current_procinfo.procdef.proccalloption in cdecl_pocalls) then
            g_releasevaluepara_openarray(list,tarraydef(tparavarsym(p).vardef),tparavarsym(p).localloc);
        end;
    end;





{ generates the code for incrementing the reference count of parameters and
  initialize out parameters }
  { generates the code for incrementing the reference count of parameters and
    initialize out parameters }
  procedure thlcgobj.init_paras(p:TObject;arg:pointer);
    var
      href : treference;
      hsym : tparavarsym;
      eldef : tdef;
      list : TAsmList;
      highloc : tlocation;
      needs_inittable  : boolean;
    begin
      list:=TAsmList(arg);
      if (tsym(p).typ=paravarsym) then
       begin
         needs_inittable:=is_managed_type(tparavarsym(p).vardef);
         case tparavarsym(p).varspez of
           vs_value :
             if needs_inittable then
               begin
                 { variants are already handled by the call to fpc_variant_copy_overwrite if
                   they are passed by reference }
                 if not((tparavarsym(p).vardef.typ=variantdef) and
                   paramanager.push_addr_param(tparavarsym(p).varspez,tparavarsym(p).vardef,current_procinfo.procdef.proccalloption)) then
                   begin
                     location_get_data_ref(list,tparavarsym(p).vardef,tparavarsym(p).initialloc,href,is_open_array(tparavarsym(p).vardef),sizeof(pint));
                     if is_open_array(tparavarsym(p).vardef) then
                       begin
                         if paramanager.push_high_param(tparavarsym(p).varspez,tparavarsym(p).vardef,current_procinfo.procdef.proccalloption) then
                           begin
                             hsym:=tparavarsym(get_high_value_sym(tparavarsym(p)));
                             if not assigned(hsym) then
                               internalerror(201003032);
                             highloc:=hsym.initialloc
                           end
                         else
                           highloc.loc:=LOC_INVALID;
                         { open arrays do not contain correct element count in their rtti,
                           the actual count must be passed separately. }
                         eldef:=tarraydef(tparavarsym(p).vardef).elementdef;
                         g_array_rtti_helper(list,eldef,href,highloc,'FPC_ADDREF_ARRAY');
                       end
                     else
                      g_incrrefcount(list,tparavarsym(p).vardef,href);
                   end;
               end;
           vs_out :
             begin
               if needs_inittable then
                 begin
                   { we have no idea about the alignment at the callee side,
                     and the user also cannot specify "unaligned" here, so
                     assume worst case }
                   location_get_data_ref(list,tparavarsym(p).vardef,tparavarsym(p).initialloc,href,true,1);
                   if needs_inittable then
                     begin
                       if is_open_array(tparavarsym(p).vardef) then
                         begin
                           if paramanager.push_high_param(tparavarsym(p).varspez,tparavarsym(p).vardef,current_procinfo.procdef.proccalloption) then
                             begin
                               hsym:=tparavarsym(get_high_value_sym(tparavarsym(p)));
                               if not assigned(hsym) then
                                 internalerror(201003032);
                               highloc:=hsym.initialloc
                             end
                           else
                             highloc.loc:=LOC_INVALID;
                           eldef:=tarraydef(tparavarsym(p).vardef).elementdef;
                           g_array_rtti_helper(list,eldef,href,highloc,'FPC_INITIALIZE_ARRAY');
                         end
                       else
                         g_initialize(list,tparavarsym(p).vardef,href);
                     end;
                 end;
             end;
         end;
       end;
    end;

  procedure thlcgobj.gen_load_para_value(list: TAsmList);
    var
      i: longint;
      currpara: tparavarsym;
    begin
      if (po_assembler in current_procinfo.procdef.procoptions) or
      { exceptfilters have a single hidden 'parentfp' parameter, which
        is handled by tcg.g_proc_entry. }
         (current_procinfo.procdef.proctypeoption=potype_exceptfilter) then
        exit;

      { Copy parameters to local references/registers }
      for i:=0 to current_procinfo.procdef.paras.count-1 do
        begin
          currpara:=tparavarsym(current_procinfo.procdef.paras[i]);
          gen_load_cgpara_loc(list,currpara.vardef,currpara.paraloc[calleeside],currpara.initialloc,paramanager.param_use_paraloc(currpara.paraloc[calleeside]));
        end;

      { generate copies of call by value parameters, must be done before
        the initialization and body is parsed because the refcounts are
        incremented using the local copies }
      current_procinfo.procdef.parast.SymList.ForEachCall(@g_copyvalueparas,list);

      if not(po_assembler in current_procinfo.procdef.procoptions) then
        begin
          { initialize refcounted paras, and trash others. Needed here
            instead of in gen_initialize_code, because when a reference is
            intialised or trashed while the pointer to that reference is kept
            in a regvar, we add a register move and that one again has to
            come after the parameter loading code as far as the register
            allocator is concerned }
          current_procinfo.procdef.parast.SymList.ForEachCall(@init_paras,list);
        end;
    end;

  procedure thlcgobj.g_copyvalueparas(p: TObject; arg: pointer);
    var
      href : treference;
      hreg : tregister;
      list : TAsmList;
      hsym : tparavarsym;
      l    : longint;
      highloc,
      localcopyloc : tlocation;
    begin
      list:=TAsmList(arg);
      if (tsym(p).typ=paravarsym) and
         (tparavarsym(p).varspez=vs_value) and
        (paramanager.push_addr_param(tparavarsym(p).varspez,tparavarsym(p).vardef,current_procinfo.procdef.proccalloption)) then
        begin
          { we have no idea about the alignment at the caller side }
          location_get_data_ref(list,tparavarsym(p).vardef,tparavarsym(p).initialloc,href,true,1);
          if is_open_array(tparavarsym(p).vardef) or
             is_array_of_const(tparavarsym(p).vardef) then
            begin
              { cdecl functions don't have a high pointer so it is not possible to generate
                a local copy }
              if not(current_procinfo.procdef.proccalloption in cdecl_pocalls) then
                begin
                  if paramanager.push_high_param(tparavarsym(p).varspez,tparavarsym(p).vardef,current_procinfo.procdef.proccalloption) then
                    begin
                      hsym:=tparavarsym(get_high_value_sym(tparavarsym(p)));
                      if not assigned(hsym) then
                        internalerror(2011020506);
                      highloc:=hsym.initialloc
                    end
                  else
                    highloc.loc:=LOC_INVALID;
                  hreg:=getaddressregister(list,voidpointertype);
                  if not is_packed_array(tparavarsym(p).vardef) then
                    g_copyvaluepara_openarray(list,href,highloc,tarraydef(tparavarsym(p).vardef),hreg)
                  else
                    internalerror(2011020507);
//                      cg.g_copyvaluepara_packedopenarray(list,href,hsym.intialloc,tarraydef(tparavarsym(p).vardef).elepackedbitsize,hreg);
                  a_load_reg_loc(list,tparavarsym(p).vardef,tparavarsym(p).vardef,hreg,tparavarsym(p).initialloc);
                end;
            end
          else
            begin
              { Allocate space for the local copy }
              l:=tparavarsym(p).getsize;
              localcopyloc.loc:=LOC_REFERENCE;
              localcopyloc.size:=int_cgsize(l);
              tg.GetLocal(list,l,tparavarsym(p).vardef,localcopyloc.reference);
              { Copy data }
              if is_shortstring(tparavarsym(p).vardef) then
                begin
                  { this code is only executed before the code for the body and the entry/exit code is generated
                    so we're allowed to include pi_do_call here; after pass1 is run, this isn't allowed anymore
                  }
                  include(current_procinfo.flags,pi_do_call);
                  g_copyshortstring(list,href,localcopyloc.reference,tstringdef(tparavarsym(p).vardef))
                end
              else if tparavarsym(p).vardef.typ=variantdef then
                begin
                  { this code is only executed before the code for the body and the entry/exit code is generated
                    so we're allowed to include pi_do_call here; after pass1 is run, this isn't allowed anymore
                  }
                  include(current_procinfo.flags,pi_do_call);
                  g_copyvariant(list,href,localcopyloc.reference,tvariantdef(tparavarsym(p).vardef))
                end
              else
                begin
                  { pass proper alignment info }
                  localcopyloc.reference.alignment:=tparavarsym(p).vardef.alignment;
                  g_concatcopy(list,tparavarsym(p).vardef,href,localcopyloc.reference);
                end;
              { update localloc of varsym }
              tg.Ungetlocal(list,tparavarsym(p).localloc.reference);
              tparavarsym(p).localloc:=localcopyloc;
              tparavarsym(p).initialloc:=localcopyloc;
            end;
        end;
    end;

  procedure thlcgobj.gen_loadfpu_loc_cgpara(list: TAsmList; size: tdef; const l: tlocation; const cgpara: tcgpara; locintsize: longint);
    begin
      case l.loc of
(*
        LOC_MMREGISTER,
        LOC_CMMREGISTER:
          case cgpara.location^.loc of
            LOC_REFERENCE,
            LOC_CREFERENCE,
            LOC_MMREGISTER,
            LOC_CMMREGISTER,
            LOC_REGISTER,
            LOC_CREGISTER :
              cg.a_loadmm_reg_cgpara(list,locsize,l.register,cgpara,mms_movescalar);
            LOC_FPUREGISTER,
            LOC_CFPUREGISTER:
              begin
                tmploc:=l;
                location_force_fpureg(list,tmploc,false);
                cg.a_loadfpu_reg_cgpara(list,tmploc.size,tmploc.register,cgpara);
              end;
            else
              internalerror(200204249);
          end;
*)
        LOC_FPUREGISTER,
        LOC_CFPUREGISTER:
          case cgpara.location^.loc of
(*
            LOC_MMREGISTER,
            LOC_CMMREGISTER:
              begin
                tmploc:=l;
                location_force_mmregscalar(list,tmploc,false);
                cg.a_loadmm_reg_cgpara(list,tmploc.size,tmploc.register,cgpara,mms_movescalar);
              end;
*)
            { Some targets pass floats in normal registers }
            LOC_REGISTER,
            LOC_CREGISTER,
            LOC_REFERENCE,
            LOC_CREFERENCE,
            LOC_FPUREGISTER,
            LOC_CFPUREGISTER:
              a_loadfpu_reg_cgpara(list,size,l.register,cgpara);
            else
              internalerror(2011010210);
          end;
        LOC_REFERENCE,
        LOC_CREFERENCE:
          case cgpara.location^.loc of
(*
            LOC_MMREGISTER,
            LOC_CMMREGISTER:
              cg.a_loadmm_ref_cgpara(list,locsize,l.reference,cgpara,mms_movescalar);
*)
            { Some targets pass floats in normal registers }
            LOC_REGISTER,
            LOC_CREGISTER,
            LOC_REFERENCE,
            LOC_CREFERENCE,
            LOC_FPUREGISTER,
            LOC_CFPUREGISTER:
              a_loadfpu_ref_cgpara(list,size,l.reference,cgpara);
            else
              internalerror(2011010211);
          end;
        LOC_REGISTER,
        LOC_CREGISTER :
          a_load_loc_cgpara(list,size,l,cgpara);
         else
           internalerror(2011010212);
      end;
    end;

  procedure thlcgobj.gen_load_uninitialized_function_result(list: TAsmList; pd: tprocdef; resdef: tdef; const resloc: tcgpara);
    begin
      { do nothing by default }
    end;

  procedure thlcgobj.gen_load_loc_cgpara(list: TAsmList; vardef: tdef; const l: tlocation; const cgpara: tcgpara);
    begin
      { Handle Floating point types differently

        This doesn't depend on emulator settings, emulator settings should
        be handled by cpupara }
      if (vardef.typ=floatdef) or
         { some ABIs return certain records in an fpu register }
         (l.loc in [LOC_FPUREGISTER,LOC_CFPUREGISTER]) or
         (assigned(cgpara.location) and
          (cgpara.Location^.loc in [LOC_FPUREGISTER,LOC_CFPUREGISTER])) then
        begin
          gen_loadfpu_loc_cgpara(list,vardef,l,cgpara,vardef.size);
          exit;
        end;

      case l.loc of
        LOC_CONSTANT,
        LOC_REGISTER,
        LOC_CREGISTER,
        LOC_REFERENCE,
        LOC_CREFERENCE :
          begin
            a_load_loc_cgpara(list,vardef,l,cgpara);
          end;
(*
        LOC_MMREGISTER,
        LOC_CMMREGISTER:
          begin
            case l.size of
              OS_F32,
              OS_F64:
                cg.a_loadmm_loc_cgpara(list,l,cgpara,mms_movescalar);
              else
                cg.a_loadmm_loc_cgpara(list,l,cgpara,nil);
            end;
          end;
*)
        else
          internalerror(2011010213);
      end;
    end;

  procedure thlcgobj.gen_load_cgpara_loc(list: TAsmList; vardef: tdef; const para: TCGPara; var destloc: tlocation; reusepara: boolean);
    var
      href     : treference;
    begin
      para.check_simple_location;
      { skip e.g. empty records }
      if (para.location^.loc = LOC_VOID) then
        exit;
      case destloc.loc of
        LOC_REFERENCE :
          begin
            { If the parameter location is reused we don't need to copy
              anything }
            if not reusepara then
              begin
                reference_reset_base(href,para.location^.reference.index,para.location^.reference.offset,para.alignment);
                a_load_ref_ref(list,para.def,para.def,href,destloc.reference);
              end;
          end;
        { TODO other possible locations }
        else
          internalerror(2011010308);
      end;
    end;

  procedure thlcgobj.gen_load_return_value(list: TAsmList);
    var
      ressym : tabstractnormalvarsym;
      funcretloc : TCGPara;
    begin
      { Is the loading needed? }
      if is_void(current_procinfo.procdef.returndef) or
         (
          (po_assembler in current_procinfo.procdef.procoptions) and
          (not(assigned(current_procinfo.procdef.funcretsym)) or
           (tabstractvarsym(current_procinfo.procdef.funcretsym).refs=0))
         ) then
         exit;

      funcretloc:=current_procinfo.procdef.funcretloc[calleeside];

      { constructors return self }
      if (current_procinfo.procdef.proctypeoption=potype_constructor) then
        ressym:=tabstractnormalvarsym(current_procinfo.procdef.parast.Find('self'))
      else
        ressym:=tabstractnormalvarsym(current_procinfo.procdef.funcretsym);
      if (ressym.refs>0) or
         is_managed_type(ressym.vardef) then
        begin
          { was: don't do anything if funcretloc.loc in [LOC_INVALID,LOC_REFERENCE] }
          if not paramanager.ret_in_param(current_procinfo.procdef.returndef,current_procinfo.procdef.proccalloption) then
            gen_load_loc_cgpara(list,ressym.vardef,ressym.localloc,funcretloc);
        end
      else
        gen_load_uninitialized_function_result(list,current_procinfo.procdef,ressym.vardef,funcretloc)
    end;

  procedure thlcgobj.record_generated_code_for_procdef(pd: tprocdef; code, data: TAsmList);
    begin
      { add the procedure to the al_procedures }
      maybe_new_object_file(current_asmdata.asmlists[al_procedures]);
      new_section(current_asmdata.asmlists[al_procedures],sec_code,lower(pd.mangledname),getprocalign);
      current_asmdata.asmlists[al_procedures].concatlist(code);
      { save local data (casetable) also in the same file }
      if assigned(data) and
         (not data.empty) then
        current_asmdata.asmlists[al_procedures].concatlist(data);
    end;

  procedure thlcgobj.g_call_system_proc(list: TAsmList; const procname: string);
    var
      srsym: tsym;
      pd: tprocdef;
    begin
      srsym:=tsym(systemunit.find(procname));
      if not assigned(srsym) and
         (cs_compilesystem in current_settings.moduleswitches) then
        srsym:=tsym(systemunit.Find(upper(procname)));
      if not assigned(srsym) or
         (srsym.typ<>procsym) then
        Message1(cg_f_unknown_compilerproc,procname);
      pd:=tprocdef(tprocsym(srsym).procdeflist[0]);
      a_call_name(list,pd,pd.mangledname,false);
    end;



end.
