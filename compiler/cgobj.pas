{
    Copyright (c) 1998-2005 by Florian Klaempfl
    Member of the Free Pascal development team

    This unit implements the basic code generator object

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
   Abstreact code generator unit. This contains the base class
   to implement for all new supported processors.

   WARNING: None of the routines implemented in these modules,
   or their descendants, should use the temp. allocator, as
   these routines may be called inside genentrycode, and the
   stack frame is already setup!
}
unit cgobj;

{$i fpcdefs.inc}

  interface

    uses
       cclasses,globtype,constexp,
       cpubase,cgbase,cgutils,parabase,
       aasmbase,aasmtai,aasmdata,aasmcpu,
       symconst,symtype,symdef,rgobj
       ;

    type
       talignment = (AM_NATURAL,AM_NONE,AM_2BYTE,AM_4BYTE,AM_8BYTE);

       {# @abstract(Abstract code generator)
          This class implements an abstract instruction generator. Some of
          the methods of this class are generic, while others must
          be overridden for all new processors which will be supported
          by Free Pascal. For 32-bit processors, the base class
          should be @link(tcg64f32) and not @var(tcg).
       }
       tcg = class
       public
          { how many times is this current code executed }
          executionweight : longint;
          alignment : talignment;
          rg        : array[tregistertype] of trgobj;
       {$ifdef flowgraph}
          aktflownode:word;
       {$endif}
          {************************************************}
          {                 basic routines                 }
          constructor create;

          {# Initialize the register allocators needed for the codegenerator.}
          procedure init_register_allocators;virtual;
          {# Clean up the register allocators needed for the codegenerator.}
          procedure done_register_allocators;virtual;
          {# Set whether live_start or live_end should be updated when allocating registers, needed when e.g. generating initcode after the rest of the code. }
          procedure set_regalloc_live_range_direction(dir: TRADirection);

       {$ifdef flowgraph}
          procedure init_flowgraph;
          procedure done_flowgraph;
       {$endif}
          {# Gets a register suitable to do integer operations on.}
          function getintregister(list:TAsmList;size:Tcgsize):Tregister;virtual;
          {# Gets a register suitable to do integer operations on.}
          function getaddressregister(list:TAsmList):Tregister;virtual;
          function getfpuregister(list:TAsmList;size:Tcgsize):Tregister;virtual;
          function getmmregister(list:TAsmList;size:Tcgsize):Tregister;virtual;
          function getflagregister(list:TAsmList;size:Tcgsize):Tregister;virtual;
          {Does the generic cg need SIMD registers, like getmmxregister? Or should
           the cpu specific child cg object have such a method?}

          procedure add_reg_instruction(instr:Tai;r:tregister);virtual;
          procedure add_move_instruction(instr:Taicpu);virtual;

          function  uses_registers(rt:Tregistertype):boolean;virtual;
          {# Get a specific register.}
          procedure getcpuregister(list:TAsmList;r:Tregister);virtual;
          procedure ungetcpuregister(list:TAsmList;r:Tregister);virtual;
          {# Get multiple registers specified.}
          procedure alloccpuregisters(list:TAsmList;rt:Tregistertype;const r:Tcpuregisterset);virtual;
          {# Free multiple registers specified.}
          procedure dealloccpuregisters(list:TAsmList;rt:Tregistertype;const r:Tcpuregisterset);virtual;

          procedure allocallcpuregisters(list:TAsmList);virtual;
          procedure deallocallcpuregisters(list:TAsmList);virtual;
          procedure do_register_allocation(list:TAsmList;headertai:tai);virtual;
          procedure translate_register(var reg : tregister);

          function makeregsize(list:TAsmList;reg:Tregister;size:Tcgsize):Tregister;

          {# Emit a label to the instruction stream. }
          procedure a_label(list : TAsmList;l : tasmlabel);virtual;

          {# Allocates register r by inserting a pai_realloc record }
          procedure a_reg_alloc(list : TAsmList;r : tregister);
          {# Deallocates register r by inserting a pa_regdealloc record}
          procedure a_reg_dealloc(list : TAsmList;r : tregister);
          { Synchronize register, make sure it is still valid }
          procedure a_reg_sync(list : TAsmList;r : tregister);

          {# Pass a parameter, which is located in a register, to a routine.

             This routine should push/send the parameter to the routine, as
             required by the specific processor ABI and routine modifiers.
             It must generate register allocation information for the cgpara in
             case it consists of cpuregisters.

             @param(size size of the operand in the register)
             @param(r register source of the operand)
             @param(cgpara where the parameter will be stored)
          }
          procedure a_load_reg_cgpara(list : TAsmList;size : tcgsize;r : tregister;const cgpara : TCGPara);virtual;
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
          procedure a_load_const_cgpara(list : TAsmList;size : tcgsize;a : tcgint;const cgpara : TCGPara);virtual;
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
          procedure a_load_ref_cgpara(list : TAsmList;size : tcgsize;const r : treference;const cgpara : TCGPara);virtual;
          {# Pass the value of a parameter, which can be located either in a register or memory location,
             to a routine.

             A generic version is provided.

             @param(l location of the operand to send)
             @param(nr parameter number (starting from one) of routine (from left to right))
             @param(cgpara where the parameter will be stored)
          }
          procedure a_load_loc_cgpara(list : TAsmList;const l : tlocation;const cgpara : TCGPara);
          {# Pass the address of a reference to a routine. This routine
             will calculate the address of the reference, and pass this
             calculated address as a parameter.
             It must generate register allocation information for the cgpara in
             case it consists of cpuregisters.

             A generic version is provided. This routine should
             be overridden for optimization purposes if the cpu
             permits directly sending this type of parameter.

             @param(r reference to get address from)
             @param(nr parameter number (starting from one) of routine (from left to right))
          }
          procedure a_loadaddr_ref_cgpara(list : TAsmList;const r : treference;const cgpara : TCGPara);virtual;

          {# Load a cgparaloc into a memory reference.
             It must generate register allocation information for the cgpara in
             case it consists of cpuregisters.

           @param(paraloc the source parameter sublocation)
           @param(ref the destination reference)
           @param(sizeleft indicates the total number of bytes left in all of
                  the remaining sublocations of this parameter (the current
                  sublocation and all of the sublocations coming after it).
                  In case this location is also a reference, it is assumed
                  to be the final part sublocation of the parameter and that it
                  contains all of the "sizeleft" bytes).)
           @param(align the alignment of the paraloc in case it's a reference)
          }
          procedure a_load_cgparaloc_ref(list : TAsmList;const paraloc : TCGParaLocation;const ref : treference;sizeleft : tcgint;align : longint);

          {# Load a cgparaloc into any kind of register (int, fp, mm).

           @param(regsize the size of the destination register)
           @param(paraloc the source parameter sublocation)
           @param(reg the destination register)
           @param(align the alignment of the paraloc in case it's a reference)
          }
          procedure a_load_cgparaloc_anyreg(list : TAsmList;regsize : tcgsize;const paraloc : TCGParaLocation;reg : tregister;align : longint);

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
          procedure a_call_name(list : TAsmList;const s : string; weak: boolean);virtual; abstract;
          procedure a_call_reg(list : TAsmList;reg : tregister);virtual; abstract;
          procedure a_call_ref(list : TAsmList;ref : treference);virtual;
          { same as a_call_name, might be overridden on certain architectures to emit
            static calls without usage of a got trampoline }
          procedure a_call_name_static(list : TAsmList;const s : string);virtual;

          { move instructions }
          procedure a_load_const_reg(list : TAsmList;size : tcgsize;a : tcgint;register : tregister);virtual; abstract;
          procedure a_load_const_ref(list : TAsmList;size : tcgsize;a : tcgint;const ref : treference);virtual;
          procedure a_load_const_loc(list : TAsmList;a : tcgint;const loc : tlocation);
          procedure a_load_reg_ref(list : TAsmList;fromsize,tosize : tcgsize;register : tregister;const ref : treference);virtual; abstract;
          procedure a_load_reg_ref_unaligned(list : TAsmList;fromsize,tosize : tcgsize;register : tregister;const ref : treference);virtual;
          procedure a_load_reg_reg(list : TAsmList;fromsize,tosize : tcgsize;reg1,reg2 : tregister);virtual; abstract;
          procedure a_load_reg_loc(list : TAsmList;fromsize : tcgsize;reg : tregister;const loc: tlocation);
          procedure a_load_ref_reg(list : TAsmList;fromsize,tosize : tcgsize;const ref : treference;register : tregister);virtual; abstract;
          procedure a_load_ref_reg_unaligned(list : TAsmList;fromsize,tosize : tcgsize;const ref : treference;register : tregister);virtual;
          procedure a_load_ref_ref(list : TAsmList;fromsize,tosize : tcgsize;const sref : treference;const dref : treference);virtual;
          procedure a_load_loc_reg(list : TAsmList;tosize: tcgsize; const loc: tlocation; reg : tregister);
          procedure a_load_loc_ref(list : TAsmList;tosize: tcgsize; const loc: tlocation; const ref : treference);
          procedure a_loadaddr_ref_reg(list : TAsmList;const ref : treference;r : tregister);virtual; abstract;

          { bit scan instructions }
          procedure a_bit_scan_reg_reg(list: TAsmList; reverse: boolean; size: tcgsize; src, dst: TRegister); virtual; abstract;

          { fpu move instructions }
          procedure a_loadfpu_reg_reg(list: TAsmList; fromsize, tosize:tcgsize; reg1, reg2: tregister); virtual; abstract;
          procedure a_loadfpu_ref_reg(list: TAsmList; fromsize, tosize: tcgsize; const ref: treference; reg: tregister); virtual; abstract;
          procedure a_loadfpu_reg_ref(list: TAsmList; fromsize, tosize: tcgsize; reg: tregister; const ref: treference); virtual; abstract;
          procedure a_loadfpu_ref_ref(list: TAsmList; fromsize, tosize: tcgsize; const ref1,ref2: treference);
          procedure a_loadfpu_loc_reg(list: TAsmList; tosize: tcgsize; const loc: tlocation; const reg: tregister);
          procedure a_loadfpu_reg_loc(list: TAsmList; fromsize: tcgsize; const reg: tregister; const loc: tlocation);
          procedure a_loadfpu_reg_cgpara(list : TAsmList;size : tcgsize;const r : tregister;const cgpara : TCGPara);virtual;
          procedure a_loadfpu_ref_cgpara(list : TAsmList;size : tcgsize;const ref : treference;const cgpara : TCGPara);virtual;

          { vector register move instructions }
          procedure a_loadmm_reg_reg(list: TAsmList; fromsize, tosize : tcgsize;reg1, reg2: tregister;shuffle : pmmshuffle); virtual;
          procedure a_loadmm_ref_reg(list: TAsmList; fromsize, tosize : tcgsize;const ref: treference; reg: tregister;shuffle : pmmshuffle); virtual;
          procedure a_loadmm_reg_ref(list: TAsmList; fromsize, tosize : tcgsize;reg: tregister; const ref: treference;shuffle : pmmshuffle); virtual;
          procedure a_loadmm_loc_reg(list: TAsmList; size: tcgsize; const loc: tlocation; const reg: tregister;shuffle : pmmshuffle);
          procedure a_loadmm_reg_loc(list: TAsmList; size: tcgsize; const reg: tregister; const loc: tlocation;shuffle : pmmshuffle);
          procedure a_loadmm_reg_cgpara(list: TAsmList; size: tcgsize; reg: tregister;const cgpara : TCGPara;shuffle : pmmshuffle); virtual;
          procedure a_loadmm_ref_cgpara(list: TAsmList; size: tcgsize; const ref: treference;const cgpara : TCGPara;shuffle : pmmshuffle); virtual;
          procedure a_loadmm_loc_cgpara(list: TAsmList; const loc: tlocation; const cgpara : TCGPara;shuffle : pmmshuffle); virtual;
          procedure a_opmm_reg_reg(list: TAsmList; Op: TOpCG; size : tcgsize;src,dst: tregister;shuffle : pmmshuffle); virtual;
          procedure a_opmm_ref_reg(list: TAsmList; Op: TOpCG; size : tcgsize;const ref: treference; reg: tregister;shuffle : pmmshuffle); virtual;
          procedure a_opmm_loc_reg(list: TAsmList; Op: TOpCG; size : tcgsize;const loc: tlocation; reg: tregister;shuffle : pmmshuffle); virtual;
          procedure a_opmm_reg_ref(list: TAsmList; Op: TOpCG; size : tcgsize;reg: tregister;const ref: treference; shuffle : pmmshuffle); virtual;

          procedure a_loadmm_intreg_reg(list: TAsmList; fromsize, tosize : tcgsize; intreg, mmreg: tregister; shuffle: pmmshuffle); virtual;
          procedure a_loadmm_reg_intreg(list: TAsmList; fromsize, tosize : tcgsize; mmreg, intreg: tregister; shuffle : pmmshuffle); virtual;

          { basic arithmetic operations }
          { note: for operators which require only one argument (not, neg), use }
          { the op_reg_reg, op_reg_ref or op_reg_loc methods and keep in mind   }
          { that in this case the *second* operand is used as both source and   }
          { destination (JM)                                                    }
          procedure a_op_const_reg(list : TAsmList; Op: TOpCG; size: TCGSize; a: tcgint; reg: TRegister); virtual; abstract;
          procedure a_op_const_ref(list : TAsmList; Op: TOpCG; size: TCGSize; a: tcgint; const ref: TReference); virtual;
          procedure a_op_const_loc(list : TAsmList; Op: TOpCG; a: tcgint; const loc: tlocation);
          procedure a_op_reg_reg(list : TAsmList; Op: TOpCG; size: TCGSize; reg1, reg2: TRegister); virtual; abstract;
          procedure a_op_reg_ref(list : TAsmList; Op: TOpCG; size: TCGSize; reg: TRegister; const ref: TReference); virtual;
          procedure a_op_ref_reg(list : TAsmList; Op: TOpCG; size: TCGSize; const ref: TReference; reg: TRegister); virtual;
          procedure a_op_reg_loc(list : TAsmList; Op: TOpCG; reg: tregister; const loc: tlocation);
          procedure a_op_ref_loc(list : TAsmList; Op: TOpCG; const ref: TReference; const loc: tlocation);

          { trinary operations for processors that support them, 'emulated' }
          { on others. None with "ref" arguments since I don't think there  }
          { are any processors that support it (JM)                         }
          procedure a_op_const_reg_reg(list: TAsmList; op: TOpCg; size: tcgsize; a: tcgint; src, dst: tregister); virtual;
          procedure a_op_reg_reg_reg(list: TAsmList; op: TOpCg; size: tcgsize; src1, src2, dst: tregister); virtual;
          procedure a_op_const_reg_reg_checkoverflow(list: TAsmList; op: TOpCg; size: tcgsize; a: tcgint; src, dst: tregister;setflags : boolean;var ovloc : tlocation); virtual;
          procedure a_op_reg_reg_reg_checkoverflow(list: TAsmList; op: TOpCg; size: tcgsize; src1, src2, dst: tregister;setflags : boolean;var ovloc : tlocation); virtual;

          {  comparison operations }
          procedure a_cmp_const_reg_label(list : TAsmList;size : tcgsize;cmp_op : topcmp;a : tcgint;reg : tregister;
            l : tasmlabel); virtual;
          procedure a_cmp_const_ref_label(list : TAsmList;size : tcgsize;cmp_op : topcmp;a : tcgint;const ref : treference;
            l : tasmlabel); virtual;
          procedure a_cmp_const_loc_label(list: TAsmList; size: tcgsize;cmp_op: topcmp; a: tcgint; const loc: tlocation;
            l : tasmlabel);
          procedure a_cmp_reg_reg_label(list : TAsmList;size : tcgsize;cmp_op : topcmp;reg1,reg2 : tregister;l : tasmlabel); virtual; abstract;
          procedure a_cmp_ref_reg_label(list : TAsmList;size : tcgsize;cmp_op : topcmp; const ref: treference; reg : tregister; l : tasmlabel); virtual;
          procedure a_cmp_reg_ref_label(list : TAsmList;size : tcgsize;cmp_op : topcmp;reg : tregister; const ref: treference; l : tasmlabel); virtual;

          procedure a_cmp_loc_reg_label(list : TAsmList;size : tcgsize;cmp_op : topcmp; const loc: tlocation; reg : tregister; l : tasmlabel);
          procedure a_cmp_reg_loc_label(list : TAsmList;size : tcgsize;cmp_op : topcmp; reg: tregister; const loc: tlocation; l : tasmlabel);
          procedure a_cmp_ref_loc_label(list: TAsmList; size: tcgsize;cmp_op: topcmp; const ref: treference; const loc: tlocation;
            l : tasmlabel);

          procedure a_jmp_name(list : TAsmList;const s : string); virtual; abstract;
          procedure a_jmp_always(list : TAsmList;l: tasmlabel); virtual; abstract;
{$ifdef cpuflags}
          procedure a_jmp_flags(list : TAsmList;const f : TResFlags;l: tasmlabel); virtual; abstract;

          {# Depending on the value to check in the flags, either sets the register reg to one (if the flag is set)
             or zero (if the flag is cleared). The size parameter indicates the destination size register.
          }
          procedure g_flags2reg(list: TAsmList; size: TCgSize; const f: tresflags; reg: TRegister); virtual; abstract;
          procedure g_flags2ref(list: TAsmList; size: TCgSize; const f: tresflags; const ref:TReference); virtual;
{$endif cpuflags}

          {
             This routine tries to optimize the op_const_reg/ref opcode, and should be
             called at the start of a_op_const_reg/ref. It returns the actual opcode
             to emit, and the constant value to emit. This function can opcode OP_NONE to
             remove the opcode and OP_MOVE to replace it with a simple load

             @param(op The opcode to emit, returns the opcode which must be emitted)
             @param(a  The constant which should be emitted, returns the constant which must
                    be emitted)
          }
          procedure optimize_op_const(var op: topcg; var a : tcgint);virtual;

         {#
             This routine is used in exception management nodes. It should
             save the exception reason currently in the FUNCTION_RETURN_REG. The
             save should be done either to a temp (pointed to by href).
             or on the stack (pushing the value on the stack).

             The size of the value to save is OS_S32. The default version
             saves the exception reason to a temp. memory area.
          }
         procedure g_exception_reason_save(list : TAsmList; const href : treference);virtual;
         {#
             This routine is used in exception management nodes. It should
             save the exception reason constant. The
             save should be done either to a temp (pointed to by href).
             or on the stack (pushing the value on the stack).

             The size of the value to save is OS_S32. The default version
             saves the exception reason to a temp. memory area.
          }
         procedure g_exception_reason_save_const(list : TAsmList; const href : treference; a: tcgint);virtual;
         {#
             This routine is used in exception management nodes. It should
             load the exception reason to the FUNCTION_RETURN_REG. The saved value
             should either be in the temp. area (pointed to by href , href should
             *NOT* be freed) or on the stack (the value should be popped).

             The size of the value to save is OS_S32. The default version
             saves the exception reason to a temp. memory area.
          }
         procedure g_exception_reason_load(list : TAsmList; const href : treference);virtual;

          procedure g_maybe_testself(list : TAsmList;reg:tregister);
          procedure g_maybe_testvmt(list : TAsmList;reg:tregister;objdef:tobjectdef);
          {# This should emit the opcode to copy len bytes from the source
             to destination.

             It must be overridden for each new target processor.

             @param(source Source reference of copy)
             @param(dest Destination reference of copy)

          }
          procedure g_concatcopy(list : TAsmList;const source,dest : treference;len : tcgint);virtual; abstract;
          {# This should emit the opcode to copy len bytes from the an unaligned source
             to destination.

             It must be overridden for each new target processor.

             @param(source Source reference of copy)
             @param(dest Destination reference of copy)

          }
          procedure g_concatcopy_unaligned(list : TAsmList;const source,dest : treference;len : tcgint);virtual;
          {# This should emit the opcode to a shortrstring from the source
             to destination.

             @param(source Source reference of copy)
             @param(dest Destination reference of copy)

          }
          procedure g_copyshortstring(list : TAsmList;const source,dest : treference;len:byte);
          procedure g_copyvariant(list : TAsmList;const source,dest : treference);

          procedure g_incrrefcount(list : TAsmList;t: tdef; const ref: treference);
          procedure g_array_rtti_helper(list: TAsmList; t: tdef; const ref: treference; const highloc: tlocation;
            const name: string);
          procedure g_initialize(list : TAsmList;t : tdef;const ref : treference);
          procedure g_finalize(list : TAsmList;t : tdef;const ref : treference);

          {# Generates overflow checking code for a node }
          procedure g_overflowcheck(list: TAsmList; const Loc:tlocation; def:tdef); virtual;abstract;
          procedure g_overflowCheck_loc(List:TAsmList;const Loc:TLocation;def:TDef;ovloc : tlocation);virtual;

          procedure g_copyvaluepara_openarray(list : TAsmList;const ref:treference;const lenloc:tlocation;elesize:tcgint;destreg:tregister);virtual;
          procedure g_releasevaluepara_openarray(list : TAsmList;const l:tlocation);virtual;

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
          procedure g_proc_exit(list : TAsmList;parasize:longint;nostackframe:boolean);virtual;abstract;
          {# This routine is called when generating the code for the entry point
             of a routine. It should save all registers which are not used in this
             routine, and which should be declared as saved in the std_saved_registers
             set.

             This routine is mainly used when linking to code which is generated
             by ABI-compliant compilers (like GCC), to make sure that the reserved
             registers of that ABI are not clobbered.

             @param(usedinproc Registers which are used in the code of this routine)
          }
          procedure g_save_registers(list:TAsmList);virtual;
          {# This routine is called when generating the code for the exit point
             of a routine. It should restore all registers which were previously
             saved in @var(g_save_standard_registers).

             @param(usedinproc Registers which are used in the code of this routine)
          }
          procedure g_restore_registers(list:TAsmList);virtual;

          procedure g_intf_wrapper(list: TAsmList; procdef: tprocdef; const labelname: string; ioffset: longint);virtual;abstract;
          procedure g_adjust_self_value(list:TAsmList;procdef: tprocdef;ioffset: tcgint);virtual;

          function g_indirect_sym_load(list:TAsmList;const symname: string; const flags: tindsymflags): tregister;virtual;
          { generate a stub which only purpose is to pass control the given external method,
          setting up any additional environment before doing so (if required).

          The default implementation issues a jump instruction to the external name. }
          procedure g_external_wrapper(list : TAsmList; procdef: tprocdef; const externalname: string); virtual;

          { initialize the pic/got register }
          procedure g_maybe_got_init(list: TAsmList); virtual;
          { allocallcpuregisters, a_call_name, deallocallcpuregisters sequence }
          procedure g_call(list: TAsmList; const s: string);
          { Generate code to exit an unwind-protected region. The default implementation
            produces a simple jump to destination label. }
          procedure g_local_unwind(list: TAsmList; l: TAsmLabel);virtual;
       end;

{$ifndef cpu64bitalu}
    {# @abstract(Abstract code generator for 64 Bit operations)
       This class implements an abstract code generator class
       for 64 Bit operations.
    }
    tcg64 = class
        procedure a_load64_const_ref(list : TAsmList;value : int64;const ref : treference);virtual;abstract;
        procedure a_load64_reg_ref(list : TAsmList;reg : tregister64;const ref : treference);virtual;abstract;
        procedure a_load64_ref_reg(list : TAsmList;const ref : treference;reg : tregister64);virtual;abstract;
        procedure a_load64_reg_reg(list : TAsmList;regsrc,regdst : tregister64);virtual;abstract;
        procedure a_load64_const_reg(list : TAsmList;value : int64;reg : tregister64);virtual;abstract;
        procedure a_load64_loc_reg(list : TAsmList;const l : tlocation;reg : tregister64);virtual;abstract;
        procedure a_load64_loc_ref(list : TAsmList;const l : tlocation;const ref : treference);virtual;abstract;
        procedure a_load64_const_loc(list : TAsmList;value : int64;const l : tlocation);virtual;abstract;
        procedure a_load64_reg_loc(list : TAsmList;reg : tregister64;const l : tlocation);virtual;abstract;


        procedure a_load64_subsetref_reg(list : TAsmList; const sref: tsubsetreference; destreg: tregister64);virtual;abstract;
        procedure a_load64_reg_subsetref(list : TAsmList; fromreg: tregister64; const sref: tsubsetreference);virtual;abstract;
        procedure a_load64_const_subsetref(list: TAsmlist; a: int64; const sref: tsubsetreference);virtual;abstract;
        procedure a_load64_ref_subsetref(list : TAsmList; const fromref: treference; const sref: tsubsetreference);virtual;abstract;
        procedure a_load64_subsetref_subsetref(list: TAsmlist; const fromsref, tosref: tsubsetreference); virtual;abstract;
        procedure a_load64_subsetref_ref(list : TAsmList; const sref: tsubsetreference; const destref: treference); virtual;abstract;
        procedure a_load64_loc_subsetref(list : TAsmList; const l: tlocation; const sref : tsubsetreference);
        procedure a_load64_subsetref_loc(list: TAsmlist; const sref: tsubsetreference; const l: tlocation);

        procedure a_load64high_reg_ref(list : TAsmList;reg : tregister;const ref : treference);virtual;abstract;
        procedure a_load64low_reg_ref(list : TAsmList;reg : tregister;const ref : treference);virtual;abstract;
        procedure a_load64high_ref_reg(list : TAsmList;const ref : treference;reg : tregister);virtual;abstract;
        procedure a_load64low_ref_reg(list : TAsmList;const ref : treference;reg : tregister);virtual;abstract;
        procedure a_load64high_loc_reg(list : TAsmList;const l : tlocation;reg : tregister);virtual;abstract;
        procedure a_load64low_loc_reg(list : TAsmList;const l : tlocation;reg : tregister);virtual;abstract;

        procedure a_op64_ref_reg(list : TAsmList;op:TOpCG;size : tcgsize;const ref : treference;reg : tregister64);virtual;abstract;
        procedure a_op64_reg_reg(list : TAsmList;op:TOpCG;size : tcgsize;regsrc,regdst : tregister64);virtual;abstract;
        procedure a_op64_reg_ref(list : TAsmList;op:TOpCG;size : tcgsize;regsrc : tregister64;const ref : treference);virtual;abstract;
        procedure a_op64_const_reg(list : TAsmList;op:TOpCG;size : tcgsize;value : int64;regdst : tregister64);virtual;abstract;
        procedure a_op64_const_ref(list : TAsmList;op:TOpCG;size : tcgsize;value : int64;const ref : treference);virtual;abstract;
        procedure a_op64_const_loc(list : TAsmList;op:TOpCG;size : tcgsize;value : int64;const l: tlocation);virtual;abstract;
        procedure a_op64_reg_loc(list : TAsmList;op:TOpCG;size : tcgsize;reg : tregister64;const l : tlocation);virtual;abstract;
        procedure a_op64_loc_reg(list : TAsmList;op:TOpCG;size : tcgsize;const l : tlocation;reg64 : tregister64);virtual;abstract;
        procedure a_op64_const_reg_reg(list: TAsmList;op:TOpCG;size : tcgsize;value : int64;regsrc,regdst : tregister64);virtual;
        procedure a_op64_reg_reg_reg(list: TAsmList;op:TOpCG;size : tcgsize;regsrc1,regsrc2,regdst : tregister64);virtual;
        procedure a_op64_const_reg_reg_checkoverflow(list: TAsmList;op:TOpCG;size : tcgsize;value : int64;regsrc,regdst : tregister64;setflags : boolean;var ovloc : tlocation);virtual;
        procedure a_op64_reg_reg_reg_checkoverflow(list: TAsmList;op:TOpCG;size : tcgsize;regsrc1,regsrc2,regdst : tregister64;setflags : boolean;var ovloc : tlocation);virtual;

        procedure a_op64_const_subsetref(list : TAsmList; Op : TOpCG; size : TCGSize; a : int64; const sref: tsubsetreference);
        procedure a_op64_reg_subsetref(list : TAsmList; Op : TOpCG; size : TCGSize; reg: tregister64; const sref: tsubsetreference);
        procedure a_op64_ref_subsetref(list : TAsmList; Op : TOpCG; size : TCGSize; const ref: treference; const sref: tsubsetreference);
        procedure a_op64_subsetref_subsetref(list : TAsmList; Op : TOpCG; size : TCGSize; const ssref,dsref: tsubsetreference);

        procedure a_load64_reg_cgpara(list : TAsmList;reg64 : tregister64;const loc : TCGPara);virtual;abstract;
        procedure a_load64_const_cgpara(list : TAsmList;value : int64;const loc : TCGPara);virtual;abstract;
        procedure a_load64_ref_cgpara(list : TAsmList;const r : treference;const loc : TCGPara);virtual;abstract;
        procedure a_load64_loc_cgpara(list : TAsmList;const l : tlocation;const loc : TCGPara);virtual;abstract;

        procedure a_loadmm_intreg64_reg(list: TAsmList; mmsize: tcgsize; intreg: tregister64; mmreg: tregister); virtual;abstract;
        procedure a_loadmm_reg_intreg64(list: TAsmList; mmsize: tcgsize; mmreg: tregister; intreg: tregister64); virtual;abstract;
        {
             This routine tries to optimize the const_reg opcode, and should be
             called at the start of a_op64_const_reg. It returns the actual opcode
             to emit, and the constant value to emit. If this routine returns
             TRUE, @var(no) instruction should be emitted (.eg : imul reg by 1 )

             @param(op The opcode to emit, returns the opcode which must be emitted)
             @param(a  The constant which should be emitted, returns the constant which must
                    be emitted)
             @param(reg The register to emit the opcode with, returns the register with
                   which the opcode will be emitted)
        }
        function optimize64_op_const_reg(list: TAsmList; var op: topcg; var a : int64; var reg: tregister64): boolean;virtual;abstract;


        { override to catch 64bit rangechecks }
        procedure g_rangecheck64(list: TAsmList; const l:tlocation; fromdef,todef: tdef);virtual;abstract;
    end;
{$endif cpu64bitalu}

    var
       {# Main code generator class }
       cg : tcg;
{$ifndef cpu64bitalu}
       {# Code generator class for all operations working with 64-Bit operands }
       cg64 : tcg64;
{$endif cpu64bitalu}

    function asmsym2indsymflags(sym: TAsmSymbol): tindsymflags;

    procedure destroy_codegen;

implementation

    uses
       globals,options,systems,
       verbose,defutil,paramgr,symsym,
       tgobj,cutils,procinfo,
       ncgrtti;


{*****************************************************************************
                            basic functionallity
******************************************************************************}

    constructor tcg.create;
      begin
      end;


{*****************************************************************************
                                register allocation
******************************************************************************}


    procedure tcg.init_register_allocators;
      begin
        fillchar(rg,sizeof(rg),0);
        add_reg_instruction_hook:=@add_reg_instruction;
        executionweight:=1;
      end;


    procedure tcg.done_register_allocators;
      begin
        { Safety }
        fillchar(rg,sizeof(rg),0);
        add_reg_instruction_hook:=nil;
      end;

    {$ifdef flowgraph}
    procedure Tcg.init_flowgraph;

    begin
      aktflownode:=0;
    end;

    procedure Tcg.done_flowgraph;

    begin
    end;
    {$endif}

    function tcg.getintregister(list:TAsmList;size:Tcgsize):Tregister;
      begin
        if not assigned(rg[R_INTREGISTER]) then
          internalerror(200312122);
        result:=rg[R_INTREGISTER].getregister(list,cgsize2subreg(R_INTREGISTER,size));
      end;


    function tcg.getfpuregister(list:TAsmList;size:Tcgsize):Tregister;
      begin
        if not assigned(rg[R_FPUREGISTER]) then
          internalerror(200312123);
        result:=rg[R_FPUREGISTER].getregister(list,cgsize2subreg(R_FPUREGISTER,size));
      end;


    function tcg.getmmregister(list:TAsmList;size:Tcgsize):Tregister;
      begin
        if not assigned(rg[R_MMREGISTER]) then
          internalerror(2003121214);
        result:=rg[R_MMREGISTER].getregister(list,cgsize2subreg(R_MMREGISTER,size));
      end;


    function tcg.getaddressregister(list:TAsmList):Tregister;
      begin
        if assigned(rg[R_ADDRESSREGISTER]) then
          result:=rg[R_ADDRESSREGISTER].getregister(list,R_SUBWHOLE)
        else
          begin
            if not assigned(rg[R_INTREGISTER]) then
              internalerror(200312121);
            result:=rg[R_INTREGISTER].getregister(list,R_SUBWHOLE);
          end;
      end;


    function Tcg.makeregsize(list:TAsmList;reg:Tregister;size:Tcgsize):Tregister;
      var
        subreg:Tsubregister;
      begin
        subreg:=cgsize2subreg(getregtype(reg),size);
        result:=reg;
        setsubreg(result,subreg);
        { notify RA }
        if result<>reg then
          list.concat(tai_regalloc.resize(result));
      end;


    procedure tcg.getcpuregister(list:TAsmList;r:Tregister);
      begin
        if not assigned(rg[getregtype(r)]) then
          internalerror(200312125);
        rg[getregtype(r)].getcpuregister(list,r);
      end;


    procedure tcg.ungetcpuregister(list:TAsmList;r:Tregister);
      begin
        if not assigned(rg[getregtype(r)]) then
          internalerror(200312126);
        rg[getregtype(r)].ungetcpuregister(list,r);
      end;


    procedure tcg.alloccpuregisters(list:TAsmList;rt:Tregistertype;const r:Tcpuregisterset);
      begin
        if assigned(rg[rt]) then
          rg[rt].alloccpuregisters(list,r)
        else
          internalerror(200310092);
      end;


    procedure tcg.allocallcpuregisters(list:TAsmList);
      begin
        alloccpuregisters(list,R_INTREGISTER,paramanager.get_volatile_registers_int(pocall_default));
{$if not(defined(i386)) and not(defined(avr))}
        if uses_registers(R_FPUREGISTER) then
          alloccpuregisters(list,R_FPUREGISTER,paramanager.get_volatile_registers_fpu(pocall_default));
{$ifdef cpumm}
        if uses_registers(R_MMREGISTER) then
          alloccpuregisters(list,R_MMREGISTER,paramanager.get_volatile_registers_mm(pocall_default));
{$endif cpumm}
{$endif not(defined(i386)) and not(defined(avr))}
      end;


    procedure tcg.dealloccpuregisters(list:TAsmList;rt:Tregistertype;const r:Tcpuregisterset);
      begin
        if assigned(rg[rt]) then
          rg[rt].dealloccpuregisters(list,r)
        else
          internalerror(200310093);
      end;


    procedure tcg.deallocallcpuregisters(list:TAsmList);
      begin
        dealloccpuregisters(list,R_INTREGISTER,paramanager.get_volatile_registers_int(pocall_default));
{$if not(defined(i386)) and not(defined(avr))}
        if uses_registers(R_FPUREGISTER) then
          dealloccpuregisters(list,R_FPUREGISTER,paramanager.get_volatile_registers_fpu(pocall_default));
{$ifdef cpumm}
        if uses_registers(R_MMREGISTER) then
          dealloccpuregisters(list,R_MMREGISTER,paramanager.get_volatile_registers_mm(pocall_default));
{$endif cpumm}
{$endif not(defined(i386)) and not(defined(avr))}
      end;


    function tcg.uses_registers(rt:Tregistertype):boolean;
      begin
        if assigned(rg[rt]) then
          result:=rg[rt].uses_registers
        else
          result:=false;
      end;


    procedure tcg.add_reg_instruction(instr:Tai;r:tregister);
      var
        rt : tregistertype;
      begin
        rt:=getregtype(r);
        { Only add it when a register allocator is configured.
          No IE can be generated, because the VMT is written
          without a valid rg[] }
        if assigned(rg[rt]) then
          rg[rt].add_reg_instruction(instr,r,cg.executionweight);
      end;


    procedure tcg.add_move_instruction(instr:Taicpu);
      var
        rt : tregistertype;
      begin
        rt:=getregtype(instr.oper[O_MOV_SOURCE]^.reg);
        if assigned(rg[rt]) then
          rg[rt].add_move_instruction(instr)
        else
          internalerror(200310095);
      end;


    procedure tcg.set_regalloc_live_range_direction(dir: TRADirection);
      var
        rt : tregistertype;
      begin
        for rt:=low(rg) to high(rg) do
          begin
            if assigned(rg[rt]) then
              rg[rt].live_range_direction:=dir;
          end;
      end;


    procedure tcg.do_register_allocation(list:TAsmList;headertai:tai);
      var
        rt : tregistertype;
      begin
        for rt:=R_FPUREGISTER to R_SPECIALREGISTER do
          begin
            if assigned(rg[rt]) then
              rg[rt].do_register_allocation(list,headertai);
          end;
         { running the other register allocator passes could require addition int/addr. registers
           when spilling so run int/addr register allocation at the end }
         if assigned(rg[R_INTREGISTER]) then
           rg[R_INTREGISTER].do_register_allocation(list,headertai);
         if assigned(rg[R_ADDRESSREGISTER]) then
           rg[R_ADDRESSREGISTER].do_register_allocation(list,headertai);
      end;


    procedure tcg.translate_register(var reg : tregister);
      begin
        rg[getregtype(reg)].translate_register(reg);
      end;


    procedure tcg.a_reg_alloc(list : TAsmList;r : tregister);
      begin
         list.concat(tai_regalloc.alloc(r,nil));
      end;


    procedure tcg.a_reg_dealloc(list : TAsmList;r : tregister);
      begin
         list.concat(tai_regalloc.dealloc(r,nil));
      end;


    procedure tcg.a_reg_sync(list : TAsmList;r : tregister);
      var
        instr : tai;
      begin
        instr:=tai_regalloc.sync(r);
        list.concat(instr);
        add_reg_instruction(instr,r);
      end;


    procedure tcg.a_label(list : TAsmList;l : tasmlabel);
      begin
         list.concat(tai_label.create(l));
      end;


{*****************************************************************************
          for better code generation these methods should be overridden
******************************************************************************}

    procedure tcg.a_load_reg_cgpara(list : TAsmList;size : tcgsize;r : tregister;const cgpara : TCGPara);
      var
         ref : treference;
         tmpreg : tregister;
      begin
         cgpara.check_simple_location;
         paramanager.alloccgpara(list,cgpara);
         if cgpara.location^.shiftval<0 then
           begin
             tmpreg:=getintregister(list,cgpara.location^.size);
             a_op_const_reg_reg(list,OP_SHL,cgpara.location^.size,-cgpara.location^.shiftval,r,tmpreg);
             r:=tmpreg;
           end;
         case cgpara.location^.loc of
            LOC_REGISTER,LOC_CREGISTER:
              a_load_reg_reg(list,size,cgpara.location^.size,r,cgpara.location^.register);
            LOC_REFERENCE,LOC_CREFERENCE:
              begin
                 reference_reset_base(ref,cgpara.location^.reference.index,cgpara.location^.reference.offset,cgpara.alignment);
                 a_load_reg_ref(list,size,cgpara.location^.size,r,ref);
              end;
            LOC_MMREGISTER,LOC_CMMREGISTER:
              a_loadmm_intreg_reg(list,size,cgpara.location^.size,r,cgpara.location^.register,mms_movescalar);
            LOC_FPUREGISTER,LOC_CFPUREGISTER:
              begin
                tg.GetTemp(list,TCGSize2Size[size],TCGSize2Size[size],tt_normal,ref);
                a_load_reg_ref(list,size,size,r,ref);
                a_loadfpu_ref_cgpara(list,cgpara.location^.size,ref,cgpara);
                tg.Ungettemp(list,ref);
              end
            else
              internalerror(2002071004);
         end;
      end;


    procedure tcg.a_load_const_cgpara(list : TAsmList;size : tcgsize;a : tcgint;const cgpara : TCGPara);
      var
         ref : treference;
      begin
         cgpara.check_simple_location;
         paramanager.alloccgpara(list,cgpara);
         if cgpara.location^.shiftval<0 then
           a:=a shl -cgpara.location^.shiftval;
         case cgpara.location^.loc of
            LOC_REGISTER,LOC_CREGISTER:
              a_load_const_reg(list,cgpara.location^.size,a,cgpara.location^.register);
            LOC_REFERENCE,LOC_CREFERENCE:
              begin
                 reference_reset_base(ref,cgpara.location^.reference.index,cgpara.location^.reference.offset,cgpara.alignment);
                 a_load_const_ref(list,cgpara.location^.size,a,ref);
              end
            else
              internalerror(2010053109);
         end;
      end;


    procedure tcg.a_load_ref_cgpara(list : TAsmList;size : tcgsize;const r : treference;const cgpara : TCGPara);
      var
        tmpref, ref: treference;
        tmpreg: tregister;
        location: pcgparalocation;
        orgsizeleft,
        sizeleft: tcgint;
        reghasvalue: boolean;
      begin
        location:=cgpara.location;
        tmpref:=r;
        sizeleft:=cgpara.intsize;
        while assigned(location) do
          begin
            paramanager.allocparaloc(list,location);
            case location^.loc of
              LOC_REGISTER,LOC_CREGISTER:
                begin
                   { Parameter locations are often allocated in multiples of
                     entire registers. If a parameter only occupies a part of
                     such a register (e.g. a 16 bit int on a 32 bit
                     architecture), the size of this parameter can only be
                     determined by looking at the "size" parameter of this
                     method -> if the size parameter is <= sizeof(aint), then
                     we check that there is only one parameter location and
                     then use this "size" to load the value into the parameter
                     location }
                   if (size<>OS_NO) and
                      (tcgsize2size[size]<=sizeof(aint)) then
                     begin
                       cgpara.check_simple_location;
                       a_load_ref_reg(list,size,location^.size,tmpref,location^.register);
                       if location^.shiftval<0 then
                         a_op_const_reg(list,OP_SHL,location^.size,-location^.shiftval,location^.register);
                     end
                   { there's a lot more data left, and the current paraloc's
                     register is entirely filled with part of that data }
                   else if (sizeleft>sizeof(aint)) then
                     begin
                       a_load_ref_reg(list,location^.size,location^.size,tmpref,location^.register);
                     end
                   { we're at the end of the data, and it can be loaded into
                     the current location's register with a single regular
                     load }
                   else if (sizeleft in [1,2{$ifndef cpu16bitalu},4{$endif}{$ifdef cpu64bitalu},8{$endif}]) then
                     begin
                       a_load_ref_reg(list,int_cgsize(sizeleft),location^.size,tmpref,location^.register);
                       if location^.shiftval<0 then
                         a_op_const_reg(list,OP_SHL,location^.size,-location^.shiftval,location^.register);
                     end
                   { we're at the end of the data, and we need multiple loads
                     to get it in the register because it's an irregular size }
                   else
                     begin
                       { should be the last part }
                       if assigned(location^.next) then
                         internalerror(2010052907);
                       { load the value piecewise to get it into the register }
                       orgsizeleft:=sizeleft;
                       reghasvalue:=false;
{$ifdef cpu64bitalu}
                       if sizeleft>=4 then
                         begin
                           a_load_ref_reg(list,OS_32,location^.size,tmpref,location^.register);
                           dec(sizeleft,4);
                           if target_info.endian=endian_big then
                             a_op_const_reg(list,OP_SHL,location^.size,sizeleft*8,location^.register);
                           inc(tmpref.offset,4);
                           reghasvalue:=true;
                         end;
{$endif cpu64bitalu}
                       if sizeleft>=2 then
                         begin
                           tmpreg:=getintregister(list,location^.size);
                           a_load_ref_reg(list,OS_16,location^.size,tmpref,tmpreg);
                           dec(sizeleft,2);
                           if reghasvalue then
                             begin
                               if target_info.endian=endian_big then
                                 a_op_const_reg(list,OP_SHL,location^.size,sizeleft*8,tmpreg)
                               else
                                 a_op_const_reg(list,OP_SHL,location^.size,(orgsizeleft-(sizeleft+2))*8,tmpreg);
                               a_op_reg_reg(list,OP_OR,location^.size,tmpreg,location^.register);
                             end
                           else
                             begin
                               if target_info.endian=endian_big then
                                 a_op_const_reg_reg(list,OP_SHL,location^.size,sizeleft*8,tmpreg,location^.register)
                               else
                                 a_load_reg_reg(list,location^.size,location^.size,tmpreg,location^.register);
                             end;
                           inc(tmpref.offset,2);
                           reghasvalue:=true;
                         end;
                       if sizeleft=1 then
                         begin
                           tmpreg:=getintregister(list,location^.size);
                           a_load_ref_reg(list,OS_8,location^.size,tmpref,tmpreg);
                           dec(sizeleft,1);
                           if reghasvalue then
                             begin
                               if target_info.endian=endian_little then
                                 a_op_const_reg(list,OP_SHL,location^.size,(orgsizeleft-(sizeleft+1))*8,tmpreg);
                               a_op_reg_reg(list,OP_OR,location^.size,tmpreg,location^.register)
                             end
                           else
                             a_load_reg_reg(list,location^.size,location^.size,tmpreg,location^.register);
                           inc(tmpref.offset);
                         end;
                       if location^.shiftval<0 then
                         a_op_const_reg(list,OP_SHL,location^.size,-location^.shiftval,location^.register);
                       { the loop will already adjust the offset and sizeleft }
                       dec(tmpref.offset,orgsizeleft);
                       sizeleft:=orgsizeleft;
                     end;
                end;
              LOC_REFERENCE,LOC_CREFERENCE:
                begin
                   if assigned(location^.next) then
                     internalerror(2010052906);
                   reference_reset_base(ref,location^.reference.index,location^.reference.offset,newalignment(cgpara.alignment,cgpara.intsize-sizeleft));
                   if (size <> OS_NO) and
                      (tcgsize2size[size] <= sizeof(aint)) then
                     a_load_ref_ref(list,size,location^.size,tmpref,ref)
                   else
                     { use concatcopy, because the parameter can be larger than }
                     { what the OS_* constants can handle                       }
                     g_concatcopy(list,tmpref,ref,sizeleft);
                end;
              LOC_MMREGISTER,LOC_CMMREGISTER:
                begin
                   case location^.size of
                     OS_F32,
                     OS_F64,
                     OS_F128:
                       a_loadmm_ref_reg(list,location^.size,location^.size,tmpref,location^.register,mms_movescalar);
                     OS_M8..OS_M128,
                     OS_MS8..OS_MS128:
                       a_loadmm_ref_reg(list,location^.size,location^.size,tmpref,location^.register,nil);
                     else
                       internalerror(2010053101);
                   end;
                end
              else
                internalerror(2010053111);
            end;
            inc(tmpref.offset,tcgsize2size[location^.size]);
            dec(sizeleft,tcgsize2size[location^.size]);
            location:=location^.next;
          end;
      end;


    procedure tcg.a_load_loc_cgpara(list : TAsmList;const l:tlocation;const cgpara : TCGPara);
      begin
        case l.loc of
          LOC_REGISTER,
          LOC_CREGISTER :
            a_load_reg_cgpara(list,l.size,l.register,cgpara);
          LOC_CONSTANT :
            a_load_const_cgpara(list,l.size,l.value,cgpara);
          LOC_CREFERENCE,
          LOC_REFERENCE :
            a_load_ref_cgpara(list,l.size,l.reference,cgpara);
          else
            internalerror(2002032211);
        end;
      end;


    procedure tcg.a_loadaddr_ref_cgpara(list : TAsmList;const r : treference;const cgpara : TCGPara);
      var
         hr : tregister;
      begin
         cgpara.check_simple_location;
         if cgpara.location^.loc in [LOC_CREGISTER,LOC_REGISTER] then
           begin
             paramanager.allocparaloc(list,cgpara.location);
             a_loadaddr_ref_reg(list,r,cgpara.location^.register)
           end
         else
           begin
             hr:=getaddressregister(list);
             a_loadaddr_ref_reg(list,r,hr);
             a_load_reg_cgpara(list,OS_ADDR,hr,cgpara);
           end;
      end;


    procedure tcg.a_load_cgparaloc_ref(list : TAsmList;const paraloc : TCGParaLocation;const ref : treference;sizeleft : tcgint;align : longint);
      var
        href : treference;
        hreg : tregister;
        cgsize: tcgsize;
      begin
         case paraloc.loc of
           LOC_REGISTER :
             begin
               hreg:=paraloc.register;
               cgsize:=paraloc.size;
               if paraloc.shiftval>0 then
                 a_op_const_reg_reg(list,OP_SHL,OS_INT,paraloc.shiftval,paraloc.register,paraloc.register)
               else if (paraloc.shiftval<0) and
                       (sizeleft in [1,2,4]) then
                 begin
                   a_op_const_reg_reg(list,OP_SHR,OS_INT,-paraloc.shiftval,paraloc.register,paraloc.register);
                   { convert to a register of 1/2/4 bytes in size, since the
                     original register had to be made larger to be able to hold
                     the shifted value }
                   cgsize:=int_cgsize(tcgsize2size[OS_INT]-(-paraloc.shiftval div 8));
                   hreg:=getintregister(list,cgsize);
                   a_load_reg_reg(list,OS_INT,cgsize,paraloc.register,hreg);
                 end;
               a_load_reg_ref(list,paraloc.size,cgsize,hreg,ref);
             end;
           LOC_MMREGISTER :
             begin
               case paraloc.size of
                 OS_F32,
                 OS_F64,
                 OS_F128:
                   a_loadmm_reg_ref(list,paraloc.size,paraloc.size,paraloc.register,ref,mms_movescalar);
                 OS_M8..OS_M128,
                 OS_MS8..OS_MS128:
                   a_loadmm_reg_ref(list,paraloc.size,paraloc.size,paraloc.register,ref,nil);
                 else
                   internalerror(2010053102);
               end;
             end;
           LOC_FPUREGISTER :
             cg.a_loadfpu_reg_ref(list,paraloc.size,paraloc.size,paraloc.register,ref);
           LOC_REFERENCE :
             begin
               reference_reset_base(href,paraloc.reference.index,paraloc.reference.offset,align);
               { use concatcopy, because it can also be a float which fails when
                 load_ref_ref is used. Don't copy data when the references are equal }
               if not((href.base=ref.base) and (href.offset=ref.offset)) then
                 g_concatcopy(list,href,ref,sizeleft);
             end;
           else
             internalerror(2002081302);
         end;
      end;


    procedure tcg.a_load_cgparaloc_anyreg(list: TAsmList;regsize: tcgsize;const paraloc: TCGParaLocation;reg: tregister;align: longint);
      var
        href : treference;
      begin
         case paraloc.loc of
           LOC_REGISTER :
             begin
               if paraloc.shiftval<0 then
                 a_op_const_reg_reg(list,OP_SHR,OS_INT,-paraloc.shiftval,paraloc.register,paraloc.register);
               case getregtype(reg) of
                 R_INTREGISTER:
                   a_load_reg_reg(list,paraloc.size,regsize,paraloc.register,reg);
                 R_MMREGISTER:
                   a_loadmm_intreg_reg(list,paraloc.size,regsize,paraloc.register,reg,mms_movescalar);
                 else
                   internalerror(2009112422);
               end;
             end;
           LOC_MMREGISTER :
             begin
               case getregtype(reg) of
                 R_INTREGISTER:
                   a_loadmm_reg_intreg(list,paraloc.size,regsize,paraloc.register,reg,mms_movescalar);
                 R_MMREGISTER:
                   begin
                     case paraloc.size of
                       OS_F32,
                       OS_F64,
                       OS_F128:
                        a_loadmm_reg_reg(list,paraloc.size,regsize,paraloc.register,reg,mms_movescalar);
                       OS_M8..OS_M128,
                       OS_MS8..OS_MS128:
                         a_loadmm_reg_reg(list,paraloc.size,paraloc.size,paraloc.register,reg,nil);
                       else
                         internalerror(2010053102);
                     end;
                   end;
                 else
                   internalerror(2010053104);
               end;
             end;
           LOC_FPUREGISTER :
             a_loadfpu_reg_reg(list,paraloc.size,regsize,paraloc.register,reg);
           LOC_REFERENCE :
             begin
               reference_reset_base(href,paraloc.reference.index,paraloc.reference.offset,align);
               case getregtype(reg) of
                 R_INTREGISTER :
                   a_load_ref_reg(list,paraloc.size,regsize,href,reg);
                 R_FPUREGISTER :
                   a_loadfpu_ref_reg(list,paraloc.size,regsize,href,reg);
                 R_MMREGISTER :
                   { not paraloc.size, because it may be OS_64 instead of
                     OS_F64 in case the parameter is passed using integer
                     conventions (e.g., on ARM) }
                   a_loadmm_ref_reg(list,regsize,regsize,href,reg,mms_movescalar);
                 else
                   internalerror(2004101012);
               end;
             end;
           else
             internalerror(2002081302);
         end;
      end;


{****************************************************************************
                       some generic implementations
****************************************************************************}

    { memory/register loading }

    procedure tcg.a_load_reg_ref_unaligned(list : TAsmList;fromsize,tosize : tcgsize;register : tregister;const ref : treference);
      var
        tmpref : treference;
        tmpreg : tregister;
        i : longint;
      begin
        if ref.alignment<tcgsize2size[fromsize] then
          begin
            tmpref:=ref;
            { we take care of the alignment now }
            tmpref.alignment:=0;
            case FromSize of
              OS_16,OS_S16:
                begin
                  tmpreg:=getintregister(list,OS_16);
                  a_load_reg_reg(list,fromsize,OS_16,register,tmpreg);
                  if target_info.endian=endian_big then
                    inc(tmpref.offset);
                  tmpreg:=makeregsize(list,tmpreg,OS_8);
                  a_load_reg_ref(list,OS_8,OS_8,tmpreg,tmpref);
                  tmpreg:=makeregsize(list,tmpreg,OS_16);
                  a_op_const_reg(list,OP_SHR,OS_16,8,tmpreg);
                  if target_info.endian=endian_big then
                    dec(tmpref.offset)
                  else
                    inc(tmpref.offset);
                  tmpreg:=makeregsize(list,tmpreg,OS_8);
                  a_load_reg_ref(list,OS_8,OS_8,tmpreg,tmpref);
                end;
              OS_32,OS_S32:
                begin
                  { could add an optimised case for ref.alignment=2 }
                  tmpreg:=getintregister(list,OS_32);
                  a_load_reg_reg(list,fromsize,OS_32,register,tmpreg);
                  if target_info.endian=endian_big then
                    inc(tmpref.offset,3);
                  tmpreg:=makeregsize(list,tmpreg,OS_8);
                  a_load_reg_ref(list,OS_8,OS_8,tmpreg,tmpref);
                  tmpreg:=makeregsize(list,tmpreg,OS_32);
                  for i:=1 to 3 do
                    begin
                      a_op_const_reg(list,OP_SHR,OS_32,8,tmpreg);
                      if target_info.endian=endian_big then
                        dec(tmpref.offset)
                      else
                        inc(tmpref.offset);
                      tmpreg:=makeregsize(list,tmpreg,OS_8);
                      a_load_reg_ref(list,OS_8,OS_8,tmpreg,tmpref);
                      tmpreg:=makeregsize(list,tmpreg,OS_32);
                    end;
                end
              else
                a_load_reg_ref(list,fromsize,tosize,register,tmpref);
            end;
          end
        else
          a_load_reg_ref(list,fromsize,tosize,register,ref);
      end;


    procedure tcg.a_load_ref_reg_unaligned(list : TAsmList;fromsize,tosize : tcgsize;const ref : treference;register : tregister);
      var
        tmpref : treference;
        tmpreg,
        tmpreg2 : tregister;
        i : longint;
      begin
        if ref.alignment in [1,2] then
          begin
            tmpref:=ref;
            { we take care of the alignment now }
            tmpref.alignment:=0;
            case FromSize of
              OS_16,OS_S16:
                if ref.alignment=2 then
                  a_load_ref_reg(list,fromsize,tosize,tmpref,register)
                else
                  begin
                    { first load in tmpreg, because the target register }
                    { may be used in ref as well                        }
                    if target_info.endian=endian_little then
                      inc(tmpref.offset);
                    tmpreg:=getintregister(list,OS_8);
                    a_load_ref_reg(list,OS_8,OS_8,tmpref,tmpreg);
                    tmpreg:=makeregsize(list,tmpreg,OS_16);
                    a_op_const_reg(list,OP_SHL,OS_16,8,tmpreg);
                    if target_info.endian=endian_little then
                      dec(tmpref.offset)
                    else
                      inc(tmpref.offset);
                    a_load_ref_reg(list,OS_8,OS_16,tmpref,register);
                    a_op_reg_reg(list,OP_OR,OS_16,tmpreg,register);
                  end;
              OS_32,OS_S32:
                if ref.alignment=2 then
                  begin
                    if target_info.endian=endian_little then
                      inc(tmpref.offset,2);
                    tmpreg:=getintregister(list,OS_32);
                    a_load_ref_reg(list,OS_16,OS_32,tmpref,tmpreg);
                    a_op_const_reg(list,OP_SHL,OS_32,16,tmpreg);
                    if target_info.endian=endian_little then
                      dec(tmpref.offset,2)
                    else
                      inc(tmpref.offset,2);
                    a_load_ref_reg(list,OS_16,OS_32,tmpref,register);
                    a_op_reg_reg(list,OP_OR,OS_32,tmpreg,register);
                  end
                else
                  begin
                    if target_info.endian=endian_little then
                      inc(tmpref.offset,3);
                    tmpreg:=getintregister(list,OS_32);
                    a_load_ref_reg(list,OS_8,OS_32,tmpref,tmpreg);
                    tmpreg2:=getintregister(list,OS_32);
                    for i:=1 to 3 do
                      begin
                        a_op_const_reg(list,OP_SHL,OS_32,8,tmpreg);
                        if target_info.endian=endian_little then
                          dec(tmpref.offset)
                        else
                          inc(tmpref.offset);
                        a_load_ref_reg(list,OS_8,OS_32,tmpref,tmpreg2);
                        a_op_reg_reg(list,OP_OR,OS_32,tmpreg2,tmpreg);
                      end;
                    a_load_reg_reg(list,OS_32,OS_32,tmpreg,register);
                  end
              else
                a_load_ref_reg(list,fromsize,tosize,tmpref,register);
            end;
          end
        else
          a_load_ref_reg(list,fromsize,tosize,ref,register);
      end;


    procedure tcg.a_load_ref_ref(list : TAsmList;fromsize,tosize : tcgsize;const sref : treference;const dref : treference);
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


    procedure tcg.a_load_const_ref(list : TAsmList;size : tcgsize;a : tcgint;const ref : treference);
      var
        tmpreg: tregister;
      begin
        tmpreg:=getintregister(list,size);
        a_load_const_reg(list,size,a,tmpreg);
        a_load_reg_ref(list,size,size,tmpreg,ref);
      end;


    procedure tcg.a_load_const_loc(list : TAsmList;a : tcgint;const loc: tlocation);
      begin
        case loc.loc of
          LOC_REFERENCE,LOC_CREFERENCE:
            a_load_const_ref(list,loc.size,a,loc.reference);
          LOC_REGISTER,LOC_CREGISTER:
            a_load_const_reg(list,loc.size,a,loc.register);
          else
            internalerror(200203272);
        end;
      end;


    procedure tcg.a_load_reg_loc(list : TAsmList;fromsize : tcgsize;reg : tregister;const loc: tlocation);
      begin
        case loc.loc of
          LOC_REFERENCE,LOC_CREFERENCE:
            a_load_reg_ref(list,fromsize,loc.size,reg,loc.reference);
          LOC_REGISTER,LOC_CREGISTER:
            a_load_reg_reg(list,fromsize,loc.size,reg,loc.register);
          LOC_MMREGISTER,LOC_CMMREGISTER:
            a_loadmm_intreg_reg(list,fromsize,loc.size,reg,loc.register,mms_movescalar);
          else
            internalerror(200203271);
        end;
      end;


    procedure tcg.a_load_loc_reg(list : TAsmList; tosize: tcgsize; const loc: tlocation; reg : tregister);
      begin
        case loc.loc of
          LOC_REFERENCE,LOC_CREFERENCE:
            a_load_ref_reg(list,loc.size,tosize,loc.reference,reg);
          LOC_REGISTER,LOC_CREGISTER:
            a_load_reg_reg(list,loc.size,tosize,loc.register,reg);
          LOC_CONSTANT:
            a_load_const_reg(list,tosize,loc.value,reg);
          else
            internalerror(200109092);
        end;
      end;


    procedure tcg.a_load_loc_ref(list : TAsmList;tosize: tcgsize; const loc: tlocation; const ref : treference);
      begin
        case loc.loc of
          LOC_REFERENCE,LOC_CREFERENCE:
            a_load_ref_ref(list,loc.size,tosize,loc.reference,ref);
          LOC_REGISTER,LOC_CREGISTER:
            a_load_reg_ref(list,loc.size,tosize,loc.register,ref);
          LOC_CONSTANT:
            a_load_const_ref(list,tosize,loc.value,ref);
          else
            internalerror(200109302);
        end;
      end;


    procedure tcg.optimize_op_const(var op: topcg; var a : tcgint);
      var
        powerval : longint;
      begin
        case op of
          OP_OR :
            begin
              { or with zero returns same result }
              if a = 0 then
                op:=OP_NONE
              else
              { or with max returns max }
                if a = -1 then
                  op:=OP_MOVE;
            end;
          OP_AND :
            begin
              { and with max returns same result }
              if (a = -1) then
                op:=OP_NONE
              else
              { and with 0 returns 0 }
                if a=0 then
                  op:=OP_MOVE;
            end;
          OP_DIV :
            begin
              { division by 1 returns result }
              if a = 1 then
                op:=OP_NONE
              else if ispowerof2(int64(a), powerval) and not(cs_check_overflow in current_settings.localswitches) then
                begin
                  a := powerval;
                  op:= OP_SHR;
                end;
            end;
          OP_IDIV:
            begin
              if a = 1 then
                op:=OP_NONE;
            end;
         OP_MUL,OP_IMUL:
            begin
               if a = 1 then
                 op:=OP_NONE
               else
                 if a=0 then
                   op:=OP_MOVE
               else if ispowerof2(int64(a), powerval) and not(cs_check_overflow in current_settings.localswitches)  then
                 begin
                   a := powerval;
                   op:= OP_SHL;
                 end;
            end;
        OP_ADD,OP_SUB:
            begin
               if a = 0 then
                 op:=OP_NONE;
            end;
        OP_SAR,OP_SHL,OP_SHR,OP_ROL,OP_ROR:
           begin
              if a = 0 then
                op:=OP_NONE;
           end;
        end;
      end;


    procedure tcg.a_loadfpu_loc_reg(list: TAsmList; tosize: tcgsize; const loc: tlocation; const reg: tregister);
      begin
        case loc.loc of
          LOC_REFERENCE, LOC_CREFERENCE:
            a_loadfpu_ref_reg(list,loc.size,tosize,loc.reference,reg);
          LOC_FPUREGISTER, LOC_CFPUREGISTER:
            a_loadfpu_reg_reg(list,loc.size,tosize,loc.register,reg);
          else
            internalerror(200203301);
        end;
      end;


    procedure tcg.a_loadfpu_reg_loc(list: TAsmList; fromsize: tcgsize; const reg: tregister; const loc: tlocation);
      begin
        case loc.loc of
          LOC_REFERENCE, LOC_CREFERENCE:
            a_loadfpu_reg_ref(list,fromsize,loc.size,reg,loc.reference);
          LOC_FPUREGISTER, LOC_CFPUREGISTER:
            a_loadfpu_reg_reg(list,fromsize,loc.size,reg,loc.register);
          else
            internalerror(48991);
         end;
      end;


    procedure tcg.a_loadfpu_ref_ref(list: TAsmList; fromsize, tosize: tcgsize; const ref1,ref2: treference);
      var
        reg: tregister;
        regsize: tcgsize;
      begin
        if (fromsize>=tosize) then
          regsize:=fromsize
        else
          regsize:=tosize;
        reg:=getfpuregister(list,regsize);
        a_loadfpu_ref_reg(list,fromsize,regsize,ref1,reg);
        a_loadfpu_reg_ref(list,regsize,tosize,reg,ref2);
      end;


    procedure tcg.a_loadfpu_reg_cgpara(list : TAsmList;size : tcgsize;const r : tregister;const cgpara : TCGPara);
      var
         ref : treference;
      begin
        paramanager.alloccgpara(list,cgpara);
         case cgpara.location^.loc of
            LOC_FPUREGISTER,LOC_CFPUREGISTER:
              begin
                cgpara.check_simple_location;
                a_loadfpu_reg_reg(list,size,size,r,cgpara.location^.register);
              end;
            LOC_REFERENCE,LOC_CREFERENCE:
              begin
                cgpara.check_simple_location;
                reference_reset_base(ref,cgpara.location^.reference.index,cgpara.location^.reference.offset,cgpara.alignment);
                a_loadfpu_reg_ref(list,size,size,r,ref);
              end;
            LOC_REGISTER,LOC_CREGISTER:
              begin
                { paramfpu_ref does the check_simpe_location check here if necessary }
                tg.GetTemp(list,TCGSize2Size[size],TCGSize2Size[size],tt_normal,ref);
                a_loadfpu_reg_ref(list,size,size,r,ref);
                a_loadfpu_ref_cgpara(list,size,ref,cgpara);
                tg.Ungettemp(list,ref);
              end;
            else
              internalerror(2010053112);
         end;
      end;


    procedure tcg.a_loadfpu_ref_cgpara(list : TAsmList;size : tcgsize;const ref : treference;const cgpara : TCGPara);
      var
         href : treference;
         hsize: tcgsize;
      begin
         case cgpara.location^.loc of
          LOC_FPUREGISTER,LOC_CFPUREGISTER:
            begin
              cgpara.check_simple_location;
              paramanager.alloccgpara(list,cgpara);
              a_loadfpu_ref_reg(list,size,size,ref,cgpara.location^.register);
            end;
          LOC_REFERENCE,LOC_CREFERENCE:
            begin
              cgpara.check_simple_location;
              reference_reset_base(href,cgpara.location^.reference.index,cgpara.location^.reference.offset,cgpara.alignment);
              { concatcopy should choose the best way to copy the data }
              g_concatcopy(list,ref,href,tcgsize2size[size]);
            end;
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
          else
            internalerror(200402201);
        end;
      end;


    procedure tcg.a_op_const_ref(list : TAsmList; Op: TOpCG; size: TCGSize; a: tcgint; const ref: TReference);
      var
        tmpreg : tregister;
      begin
        tmpreg:=getintregister(list,size);
        a_load_ref_reg(list,size,size,ref,tmpreg);
        a_op_const_reg(list,op,size,a,tmpreg);
        a_load_reg_ref(list,size,size,tmpreg,ref);
      end;


    procedure tcg.a_op_const_loc(list : TAsmList; Op: TOpCG; a: tcgint; const loc: tlocation);
      begin
        case loc.loc of
          LOC_REGISTER, LOC_CREGISTER:
            a_op_const_reg(list,op,loc.size,a,loc.register);
          LOC_REFERENCE, LOC_CREFERENCE:
            a_op_const_ref(list,op,loc.size,a,loc.reference);
          else
            internalerror(200109061);
        end;
      end;


    procedure tcg.a_op_reg_ref(list : TAsmList; Op: TOpCG; size: TCGSize;reg: TRegister;  const ref: TReference);
      var
        tmpreg : tregister;
      begin
        tmpreg:=getintregister(list,size);
        a_load_ref_reg(list,size,size,ref,tmpreg);
        a_op_reg_reg(list,op,size,reg,tmpreg);
        a_load_reg_ref(list,size,size,tmpreg,ref);
      end;


    procedure tcg.a_op_ref_reg(list : TAsmList; Op: TOpCG; size: TCGSize; const ref: TReference; reg: TRegister);

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


    procedure tcg.a_op_reg_loc(list : TAsmList; Op: TOpCG; reg: tregister; const loc: tlocation);

      begin
        case loc.loc of
          LOC_REGISTER, LOC_CREGISTER:
            a_op_reg_reg(list,op,loc.size,reg,loc.register);
          LOC_REFERENCE, LOC_CREFERENCE:
            a_op_reg_ref(list,op,loc.size,reg,loc.reference);
          else
            internalerror(200109061);
        end;
      end;


    procedure tcg.a_op_ref_loc(list : TAsmList; Op: TOpCG; const ref: TReference; const loc: tlocation);

      var
        tmpreg: tregister;

      begin
        case loc.loc of
          LOC_REGISTER,LOC_CREGISTER:
            a_op_ref_reg(list,op,loc.size,ref,loc.register);
          LOC_REFERENCE,LOC_CREFERENCE:
            begin
              tmpreg:=getintregister(list,loc.size);
              a_load_ref_reg(list,loc.size,loc.size,ref,tmpreg);
              a_op_reg_ref(list,op,loc.size,tmpreg,loc.reference);
            end;
          else
            internalerror(200109061);
        end;
      end;


    procedure Tcg.a_op_const_reg_reg(list:TAsmList;op:Topcg;size:Tcgsize;
                                     a:tcgint;src,dst:Tregister);

    begin
      a_load_reg_reg(list,size,size,src,dst);
      a_op_const_reg(list,op,size,a,dst);
    end;

    procedure tcg.a_op_reg_reg_reg(list: TAsmList; op: TOpCg;
        size: tcgsize; src1, src2, dst: tregister);
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


    procedure tcg.a_op_const_reg_reg_checkoverflow(list: TAsmList; op: TOpCg; size: tcgsize; a: tcgint; src, dst: tregister;setflags : boolean;var ovloc : tlocation);
      begin
        a_op_const_reg_reg(list,op,size,a,src,dst);
        ovloc.loc:=LOC_VOID;
      end;


    procedure tcg.a_op_reg_reg_reg_checkoverflow(list: TAsmList; op: TOpCg; size: tcgsize; src1, src2, dst: tregister;setflags : boolean;var ovloc : tlocation);
      begin
        a_op_reg_reg_reg(list,op,size,src1,src2,dst);
        ovloc.loc:=LOC_VOID;
      end;


    procedure tcg.a_cmp_const_reg_label(list: TAsmList; size: tcgsize;
      cmp_op: topcmp; a: tcgint; reg: tregister; l: tasmlabel);
      var
        tmpreg: tregister;
      begin
        tmpreg:=getintregister(list,size);
        a_load_const_reg(list,size,a,tmpreg);
        a_cmp_reg_reg_label(list,size,cmp_op,tmpreg,reg,l);
      end;


    procedure tcg.a_cmp_const_ref_label(list : TAsmList;size : tcgsize;cmp_op : topcmp;a : tcgint;const ref : treference;
      l : tasmlabel);
      var
        tmpreg: tregister;
      begin
        tmpreg:=getintregister(list,size);
        a_load_ref_reg(list,size,size,ref,tmpreg);
        a_cmp_const_reg_label(list,size,cmp_op,a,tmpreg,l);
      end;


    procedure tcg.a_cmp_const_loc_label(list : TAsmList;size : tcgsize;cmp_op : topcmp;a : tcgint;const loc : tlocation;
      l : tasmlabel);
      begin
        case loc.loc of
          LOC_REGISTER,LOC_CREGISTER:
            a_cmp_const_reg_label(list,size,cmp_op,a,loc.register,l);
          LOC_REFERENCE,LOC_CREFERENCE:
            a_cmp_const_ref_label(list,size,cmp_op,a,loc.reference,l);
          else
            internalerror(200109061);
        end;
      end;


    procedure tcg.a_cmp_ref_reg_label(list : TAsmList;size : tcgsize;cmp_op : topcmp; const ref: treference; reg : tregister; l : tasmlabel);
      var
        tmpreg: tregister;
      begin
        tmpreg:=getintregister(list,size);
        a_load_ref_reg(list,size,size,ref,tmpreg);
        a_cmp_reg_reg_label(list,size,cmp_op,tmpreg,reg,l);
      end;


    procedure tcg.a_cmp_reg_ref_label(list : TAsmList;size : tcgsize;cmp_op : topcmp; reg : tregister; const ref: treference; l : tasmlabel);
      var
        tmpreg: tregister;
      begin
        tmpreg:=getintregister(list,size);
        a_load_ref_reg(list,size,size,ref,tmpreg);
        a_cmp_reg_reg_label(list,size,cmp_op,reg,tmpreg,l);
      end;


    procedure tcg.a_cmp_reg_loc_label(list : TAsmList;size : tcgsize;cmp_op : topcmp; reg: tregister; const loc: tlocation; l : tasmlabel);
      begin
        a_cmp_loc_reg_label(list,size,swap_opcmp(cmp_op),loc,reg,l);
      end;


    procedure tcg.a_cmp_loc_reg_label(list : TAsmList;size : tcgsize;cmp_op : topcmp; const loc: tlocation; reg : tregister; l : tasmlabel);
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
          else
            internalerror(200203231);
        end;
      end;


    procedure tcg.a_cmp_ref_loc_label(list : TAsmList;size : tcgsize;cmp_op : topcmp;const ref: treference;const loc : tlocation;
      l : tasmlabel);
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
          else
            internalerror(200109061);
        end;
      end;


    procedure tcg.a_loadmm_loc_reg(list: TAsmList; size: tcgsize; const loc: tlocation; const reg: tregister;shuffle : pmmshuffle);
      var
        tmpreg: tregister;
      begin
        case loc.loc of
          LOC_MMREGISTER,LOC_CMMREGISTER:
            a_loadmm_reg_reg(list,loc.size,size,loc.register,reg,shuffle);
          LOC_REFERENCE,LOC_CREFERENCE:
            a_loadmm_ref_reg(list,loc.size,size,loc.reference,reg,shuffle);
          LOC_REGISTER,LOC_CREGISTER:
            a_loadmm_intreg_reg(list,loc.size,size,loc.register,reg,shuffle);
          else
            internalerror(200310121);
        end;
      end;


    procedure tcg.a_loadmm_reg_loc(list: TAsmList; size: tcgsize; const reg: tregister; const loc: tlocation;shuffle : pmmshuffle);
      begin
        case loc.loc of
          LOC_MMREGISTER,LOC_CMMREGISTER:
            a_loadmm_reg_reg(list,size,loc.size,reg,loc.register,shuffle);
          LOC_REFERENCE,LOC_CREFERENCE:
            a_loadmm_reg_ref(list,size,loc.size,reg,loc.reference,shuffle);
          else
            internalerror(200310122);
        end;
      end;


    procedure tcg.a_loadmm_reg_cgpara(list: TAsmList; size: tcgsize; reg: tregister;const cgpara : TCGPara;shuffle : pmmshuffle);
      var
        href  : treference;
{$ifndef cpu64bitalu}
        tmpreg : tregister;
        reg64 : tregister64;
{$endif not cpu64bitalu}
      begin
{$ifndef cpu64bitalu}
         if not(cgpara.location^.loc in [LOC_REGISTER,LOC_CREGISTER]) or
            (size<>OS_F64) then
{$endif not cpu64bitalu}
           cgpara.check_simple_location;
         paramanager.alloccgpara(list,cgpara);
         case cgpara.location^.loc of
          LOC_MMREGISTER,LOC_CMMREGISTER:
            a_loadmm_reg_reg(list,size,cgpara.location^.size,reg,cgpara.location^.register,shuffle);
          LOC_REFERENCE,LOC_CREFERENCE:
            begin
              reference_reset_base(href,cgpara.location^.reference.index,cgpara.location^.reference.offset,cgpara.alignment);
              a_loadmm_reg_ref(list,size,cgpara.location^.size,reg,href,shuffle);
            end;
          LOC_REGISTER,LOC_CREGISTER:
            begin
              if assigned(shuffle) and
                 not shufflescalar(shuffle) then
                internalerror(2009112510);
{$ifndef cpu64bitalu}
              if (size=OS_F64) then
                begin
                  if not assigned(cgpara.location^.next) or
                     assigned(cgpara.location^.next^.next) then
                    internalerror(2009112512);
                  case cgpara.location^.next^.loc of
                    LOC_REGISTER,LOC_CREGISTER:
                      tmpreg:=cgpara.location^.next^.register;
                    LOC_REFERENCE,LOC_CREFERENCE:
                      tmpreg:=getintregister(list,OS_32);
                    else
                      internalerror(2009112910);
                  end;
                  if (target_info.endian=ENDIAN_BIG) then
                    begin
                      { paraloc^ -> high
                        paraloc^.next -> low }
                      reg64.reghi:=cgpara.location^.register;
                      reg64.reglo:=tmpreg;
                    end
                  else
                    begin
                      { paraloc^ -> low
                        paraloc^.next -> high }
                      reg64.reglo:=cgpara.location^.register;
                      reg64.reghi:=tmpreg;
                    end;
                  cg64.a_loadmm_reg_intreg64(list,size,reg,reg64);
                  if (cgpara.location^.next^.loc in [LOC_REFERENCE,LOC_CREFERENCE]) then
                    begin
                      if not(cgpara.location^.next^.size in [OS_32,OS_S32]) then
                        internalerror(2009112911);
                      reference_reset_base(href,cgpara.location^.next^.reference.index,cgpara.location^.next^.reference.offset,cgpara.alignment);
                      a_load_reg_ref(list,OS_32,cgpara.location^.next^.size,tmpreg,href);
                    end;
                end
              else
{$endif not cpu64bitalu}
                a_loadmm_reg_intreg(list,size,cgpara.location^.size,reg,cgpara.location^.register,mms_movescalar);
            end
          else
            internalerror(200310123);
        end;
      end;


    procedure tcg.a_loadmm_ref_cgpara(list: TAsmList; size: tcgsize;const ref: treference;const cgpara : TCGPara;shuffle : pmmshuffle);
      var
         hr : tregister;
         hs : tmmshuffle;
      begin
         cgpara.check_simple_location;
         hr:=getmmregister(list,cgpara.location^.size);
         a_loadmm_ref_reg(list,size,cgpara.location^.size,ref,hr,shuffle);
         if realshuffle(shuffle) then
           begin
             hs:=shuffle^;
             removeshuffles(hs);
             a_loadmm_reg_cgpara(list,cgpara.location^.size,hr,cgpara,@hs);
           end
         else
           a_loadmm_reg_cgpara(list,cgpara.location^.size,hr,cgpara,shuffle);
      end;


    procedure tcg.a_loadmm_loc_cgpara(list: TAsmList;const loc: tlocation; const cgpara : TCGPara;shuffle : pmmshuffle);
      begin
        case loc.loc of
          LOC_MMREGISTER,LOC_CMMREGISTER:
            a_loadmm_reg_cgpara(list,loc.size,loc.register,cgpara,shuffle);
          LOC_REFERENCE,LOC_CREFERENCE:
            a_loadmm_ref_cgpara(list,loc.size,loc.reference,cgpara,shuffle);
          else
            internalerror(200310123);
        end;
      end;


    procedure tcg.a_opmm_ref_reg(list: TAsmList; Op: TOpCG; size : tcgsize;const ref: treference; reg: tregister;shuffle : pmmshuffle);
      var
         hr : tregister;
         hs : tmmshuffle;
      begin
         hr:=getmmregister(list,size);
         a_loadmm_ref_reg(list,size,size,ref,hr,shuffle);
         if realshuffle(shuffle) then
           begin
             hs:=shuffle^;
             removeshuffles(hs);
             a_opmm_reg_reg(list,op,size,hr,reg,@hs);
           end
         else
           a_opmm_reg_reg(list,op,size,hr,reg,shuffle);
      end;


    procedure tcg.a_opmm_reg_ref(list: TAsmList; Op: TOpCG; size : tcgsize;reg: tregister; const ref: treference; shuffle : pmmshuffle);
      var
         hr : tregister;
         hs : tmmshuffle;
      begin
         hr:=getmmregister(list,size);
         a_loadmm_ref_reg(list,size,size,ref,hr,shuffle);
         if realshuffle(shuffle) then
           begin
             hs:=shuffle^;
             removeshuffles(hs);
             a_opmm_reg_reg(list,op,size,reg,hr,@hs);
             a_loadmm_reg_ref(list,size,size,hr,ref,@hs);
           end
         else
           begin
             a_opmm_reg_reg(list,op,size,reg,hr,shuffle);
             a_loadmm_reg_ref(list,size,size,hr,ref,shuffle);
           end;
      end;


    procedure tcg.a_loadmm_intreg_reg(list: tasmlist; fromsize,tosize: tcgsize; intreg,mmreg: tregister; shuffle: pmmshuffle);
      var
        tmpref: treference;
      begin
        if (tcgsize2size[fromsize]<>4) or
           (tcgsize2size[tosize]<>4) then
          internalerror(2009112503);
        tg.gettemp(list,4,4,tt_normal,tmpref);
        a_load_reg_ref(list,fromsize,fromsize,intreg,tmpref);
        a_loadmm_ref_reg(list,tosize,tosize,tmpref,mmreg,shuffle);
        tg.ungettemp(list,tmpref);
      end;


    procedure tcg.a_loadmm_reg_intreg(list: tasmlist; fromsize,tosize: tcgsize; mmreg,intreg: tregister; shuffle: pmmshuffle);
      var
        tmpref: treference;
      begin
        if (tcgsize2size[fromsize]<>4) or
           (tcgsize2size[tosize]<>4) then
          internalerror(2009112504);
        tg.gettemp(list,8,8,tt_normal,tmpref);
        cg.a_loadmm_reg_ref(list,fromsize,fromsize,mmreg,tmpref,shuffle);
        a_load_ref_reg(list,tosize,tosize,tmpref,intreg);
        tg.ungettemp(list,tmpref);
      end;


    procedure tcg.a_opmm_loc_reg(list: TAsmList; Op: TOpCG; size : tcgsize;const loc: tlocation; reg: tregister;shuffle : pmmshuffle);
      begin
        case loc.loc of
          LOC_CMMREGISTER,LOC_MMREGISTER:
            a_opmm_reg_reg(list,op,size,loc.register,reg,shuffle);
          LOC_CREFERENCE,LOC_REFERENCE:
            a_opmm_ref_reg(list,op,size,loc.reference,reg,shuffle);
          else
            internalerror(200312232);
        end;
      end;


    procedure tcg.g_concatcopy_unaligned(list : TAsmList;const source,dest : treference;len : tcgint);
      begin
        g_concatcopy(list,source,dest,len);
      end;


    procedure tcg.g_copyshortstring(list : TAsmList;const source,dest : treference;len:byte);
      var
        cgpara1,cgpara2,cgpara3 : TCGPara;
      begin
        cgpara1.init;
        cgpara2.init;
        cgpara3.init;
        paramanager.getintparaloc(pocall_default,1,cgpara1);
        paramanager.getintparaloc(pocall_default,2,cgpara2);
        paramanager.getintparaloc(pocall_default,3,cgpara3);
        a_loadaddr_ref_cgpara(list,dest,cgpara3);
        a_loadaddr_ref_cgpara(list,source,cgpara2);
        a_load_const_cgpara(list,OS_INT,len,cgpara1);
        paramanager.freecgpara(list,cgpara3);
        paramanager.freecgpara(list,cgpara2);
        paramanager.freecgpara(list,cgpara1);
        allocallcpuregisters(list);
        a_call_name(list,'FPC_SHORTSTR_ASSIGN',false);
        deallocallcpuregisters(list);
        cgpara3.done;
        cgpara2.done;
        cgpara1.done;
      end;


    procedure tcg.g_copyvariant(list : TAsmList;const source,dest : treference);
      var
        cgpara1,cgpara2 : TCGPara;
      begin
        cgpara1.init;
        cgpara2.init;
        paramanager.getintparaloc(pocall_default,1,cgpara1);
        paramanager.getintparaloc(pocall_default,2,cgpara2);
        a_loadaddr_ref_cgpara(list,dest,cgpara2);
        a_loadaddr_ref_cgpara(list,source,cgpara1);
        paramanager.freecgpara(list,cgpara2);
        paramanager.freecgpara(list,cgpara1);
        allocallcpuregisters(list);
        a_call_name(list,'FPC_VARIANT_COPY_OVERWRITE',false);
        deallocallcpuregisters(list);
        cgpara2.done;
        cgpara1.done;
      end;


    procedure tcg.g_incrrefcount(list : TAsmList;t: tdef; const ref: treference);
      var
        href : treference;
        incrfunc : string;
        cgpara1,cgpara2 : TCGPara;
      begin
         cgpara1.init;
         cgpara2.init;
         paramanager.getintparaloc(pocall_default,1,cgpara1);
         paramanager.getintparaloc(pocall_default,2,cgpara2);
         if is_interfacecom_or_dispinterface(t) then
           incrfunc:='FPC_INTF_INCR_REF'
         else if is_ansistring(t) then
           incrfunc:='FPC_ANSISTR_INCR_REF'
         else if is_widestring(t) then
           incrfunc:='FPC_WIDESTR_INCR_REF'
         else if is_unicodestring(t) then
           incrfunc:='FPC_UNICODESTR_INCR_REF'
         else if is_dynamic_array(t) then
           incrfunc:='FPC_DYNARRAY_INCR_REF'
         else
          incrfunc:='';
         { call the special incr function or the generic addref }
         if incrfunc<>'' then
          begin
            { widestrings aren't ref. counted on all platforms so we need the address
              to create a real copy }
            if is_widestring(t) then
              a_loadaddr_ref_cgpara(list,ref,cgpara1)
            else
              { these functions get the pointer by value }
              a_load_ref_cgpara(list,OS_ADDR,ref,cgpara1);
            paramanager.freecgpara(list,cgpara1);
            allocallcpuregisters(list);
            a_call_name(list,incrfunc,false);
            deallocallcpuregisters(list);
          end
         else
          begin
            if is_open_array(t) then
              InternalError(201103054);
            reference_reset_symbol(href,RTTIWriter.get_rtti_label(t,initrtti),0,sizeof(pint));
            a_loadaddr_ref_cgpara(list,href,cgpara2);
            a_loadaddr_ref_cgpara(list,ref,cgpara1);
            paramanager.freecgpara(list,cgpara1);
            paramanager.freecgpara(list,cgpara2);
            allocallcpuregisters(list);
            a_call_name(list,'FPC_ADDREF',false);
            deallocallcpuregisters(list);
          end;
         cgpara2.done;
         cgpara1.done;
      end;


    procedure tcg.g_array_rtti_helper(list: TAsmList; t: tdef; const ref: treference; const highloc: tlocation; const name: string);
      var
        cgpara1,cgpara2,cgpara3: TCGPara;
        href: TReference;
        hreg, lenreg: TRegister;
      begin
        cgpara1.init;
        cgpara2.init;
        cgpara3.init;
        paramanager.getintparaloc(pocall_default,1,cgpara1);
        paramanager.getintparaloc(pocall_default,2,cgpara2);
        paramanager.getintparaloc(pocall_default,3,cgpara3);

        reference_reset_symbol(href,RTTIWriter.get_rtti_label(t,initrtti),0,sizeof(pint));
        if highloc.loc=LOC_CONSTANT then
          a_load_const_cgpara(list,OS_INT,highloc.value+1,cgpara3)
        else
          begin
            if highloc.loc in [LOC_REGISTER,LOC_CREGISTER] then
              hreg:=highloc.register
            else
              begin
                hreg:=getintregister(list,OS_INT);
                a_load_loc_reg(list,OS_INT,highloc,hreg);
              end;
            { increment, converts high(x) to length(x) }
            lenreg:=getintregister(list,OS_INT);
            a_op_const_reg_reg(list,OP_ADD,OS_INT,1,hreg,lenreg);
            a_load_reg_cgpara(list,OS_INT,lenreg,cgpara3);
          end;

        a_loadaddr_ref_cgpara(list,href,cgpara2);
        a_loadaddr_ref_cgpara(list,ref,cgpara1);
        paramanager.freecgpara(list,cgpara1);
        paramanager.freecgpara(list,cgpara2);
        paramanager.freecgpara(list,cgpara3);
        allocallcpuregisters(list);
        a_call_name(list,name,false);
        deallocallcpuregisters(list);

        cgpara3.done;
        cgpara2.done;
        cgpara1.done;
      end;

    procedure tcg.g_initialize(list : TAsmList;t : tdef;const ref : treference);
      var
         href : treference;
         cgpara1,cgpara2 : TCGPara;
      begin
        cgpara1.init;
        cgpara2.init;
         if is_ansistring(t) or
            is_widestring(t) or
            is_unicodestring(t) or
            is_interfacecom_or_dispinterface(t) or
            is_dynamic_array(t) then
           a_load_const_ref(list,OS_ADDR,0,ref)
         else if t.typ=variantdef then
           begin
             paramanager.getintparaloc(pocall_default,1,cgpara1);
             a_loadaddr_ref_cgpara(list,ref,cgpara1);
             paramanager.freecgpara(list,cgpara1);
             allocallcpuregisters(list);
             a_call_name(list,'FPC_VARIANT_INIT',false);
             deallocallcpuregisters(list);
           end
         else
           begin
              if is_open_array(t) then
                InternalError(201103052);
              paramanager.getintparaloc(pocall_default,1,cgpara1);
              paramanager.getintparaloc(pocall_default,2,cgpara2);
              reference_reset_symbol(href,RTTIWriter.get_rtti_label(t,initrtti),0,sizeof(pint));
              a_loadaddr_ref_cgpara(list,href,cgpara2);
              a_loadaddr_ref_cgpara(list,ref,cgpara1);
              paramanager.freecgpara(list,cgpara1);
              paramanager.freecgpara(list,cgpara2);
              allocallcpuregisters(list);
              a_call_name(list,'FPC_INITIALIZE',false);
              deallocallcpuregisters(list);
           end;
        cgpara1.done;
        cgpara2.done;
      end;


    procedure tcg.g_finalize(list : TAsmList;t : tdef;const ref : treference);
      var
         href : treference;
         cgpara1,cgpara2 : TCGPara;
         decrfunc : string;
      begin
        if is_interfacecom_or_dispinterface(t) then
          decrfunc:='FPC_INTF_DECR_REF'
        else if is_ansistring(t) then
          decrfunc:='FPC_ANSISTR_DECR_REF'
        else if is_widestring(t) then
          decrfunc:='FPC_WIDESTR_DECR_REF'
        else if is_unicodestring(t) then
          decrfunc:='FPC_UNICODESTR_DECR_REF'
        else if t.typ=variantdef then
          decrfunc:='FPC_VARIANT_CLEAR'
        else
          begin
            cgpara1.init;
            cgpara2.init;
            if is_open_array(t) then
              InternalError(201103051);
            paramanager.getintparaloc(pocall_default,1,cgpara1);
            paramanager.getintparaloc(pocall_default,2,cgpara2);
            reference_reset_symbol(href,RTTIWriter.get_rtti_label(t,initrtti),0,sizeof(pint));
            a_loadaddr_ref_cgpara(list,href,cgpara2);
            a_loadaddr_ref_cgpara(list,ref,cgpara1);
            paramanager.freecgpara(list,cgpara1);
            paramanager.freecgpara(list,cgpara2);
            if is_dynamic_array(t) then
              g_call(list,'FPC_DYNARRAY_CLEAR')
            else
              g_call(list,'FPC_FINALIZE');
            cgpara1.done;
            cgpara2.done;
            exit;
          end;
        cgpara1.init;
        paramanager.getintparaloc(pocall_default,1,cgpara1);
        a_loadaddr_ref_cgpara(list,ref,cgpara1);
        paramanager.freecgpara(list,cgpara1);
        g_call(list,decrfunc);
        cgpara1.done;
      end;


    procedure tcg.g_overflowCheck_loc(List:TAsmList;const Loc:TLocation;def:TDef;ovloc : tlocation);
      begin
        g_overflowCheck(list,loc,def);
      end;


{$ifdef cpuflags}
    procedure tcg.g_flags2ref(list: TAsmList; size: TCgSize; const f: tresflags; const ref:TReference);

      var
        tmpreg : tregister;
      begin
        tmpreg:=getintregister(list,size);
        g_flags2reg(list,size,f,tmpreg);
        a_load_reg_ref(list,size,size,tmpreg,ref);
      end;
{$endif cpuflags}


    procedure tcg.g_maybe_testself(list : TAsmList;reg:tregister);
      var
        OKLabel : tasmlabel;
        cgpara1 : TCGPara;
      begin
        if (cs_check_object in current_settings.localswitches) or
           (cs_check_range in current_settings.localswitches) then
         begin
           current_asmdata.getjumplabel(oklabel);
           a_cmp_const_reg_label(list,OS_ADDR,OC_NE,0,reg,oklabel);
           cgpara1.init;
           paramanager.getintparaloc(pocall_default,1,cgpara1);
           a_load_const_cgpara(list,OS_INT,tcgint(210),cgpara1);
           paramanager.freecgpara(list,cgpara1);
           a_call_name(list,'FPC_HANDLEERROR',false);
           a_label(list,oklabel);
           cgpara1.done;
         end;
      end;


    procedure tcg.g_maybe_testvmt(list : TAsmList;reg:tregister;objdef:tobjectdef);
      var
        hrefvmt : treference;
        cgpara1,cgpara2 : TCGPara;
      begin
        cgpara1.init;
        cgpara2.init;
        paramanager.getintparaloc(pocall_default,1,cgpara1);
        paramanager.getintparaloc(pocall_default,2,cgpara2);
        if (cs_check_object in current_settings.localswitches) then
         begin
           reference_reset_symbol(hrefvmt,current_asmdata.RefAsmSymbol(objdef.vmt_mangledname),0,sizeof(pint));
           a_loadaddr_ref_cgpara(list,hrefvmt,cgpara2);
           a_load_reg_cgpara(list,OS_ADDR,reg,cgpara1);
           paramanager.freecgpara(list,cgpara1);
           paramanager.freecgpara(list,cgpara2);
           allocallcpuregisters(list);
           a_call_name(list,'FPC_CHECK_OBJECT_EXT',false);
           deallocallcpuregisters(list);
         end
        else
         if (cs_check_range in current_settings.localswitches) then
          begin
            a_load_reg_cgpara(list,OS_ADDR,reg,cgpara1);
            paramanager.freecgpara(list,cgpara1);
            allocallcpuregisters(list);
            a_call_name(list,'FPC_CHECK_OBJECT',false);
            deallocallcpuregisters(list);
          end;
        cgpara1.done;
        cgpara2.done;
      end;


{*****************************************************************************
                            Entry/Exit Code Functions
*****************************************************************************}

    procedure tcg.g_copyvaluepara_openarray(list : TAsmList;const ref:treference;const lenloc:tlocation;elesize:tcgint;destreg:tregister);
      var
        sizereg,sourcereg,lenreg : tregister;
        cgpara1,cgpara2,cgpara3 : TCGPara;
      begin
        { because some abis don't support dynamic stack allocation properly
          open array value parameters are copied onto the heap
        }

        { calculate necessary memory }

        { read/write operations on one register make the life of the register allocator hard }
        if not(lenloc.loc in [LOC_REGISTER,LOC_CREGISTER]) then
          begin
            lenreg:=getintregister(list,OS_INT);
            a_load_loc_reg(list,OS_INT,lenloc,lenreg);
          end
        else
          lenreg:=lenloc.register;

        sizereg:=getintregister(list,OS_INT);
        a_op_const_reg_reg(list,OP_ADD,OS_INT,1,lenreg,sizereg);
        a_op_const_reg(list,OP_IMUL,OS_INT,elesize,sizereg);
        { load source }
        sourcereg:=getaddressregister(list);
        a_loadaddr_ref_reg(list,ref,sourcereg);

        { do getmem call }
        cgpara1.init;
        paramanager.getintparaloc(pocall_default,1,cgpara1);
        a_load_reg_cgpara(list,OS_INT,sizereg,cgpara1);
        paramanager.freecgpara(list,cgpara1);
        allocallcpuregisters(list);
        a_call_name(list,'FPC_GETMEM',false);
        deallocallcpuregisters(list);
        cgpara1.done;
        { return the new address }
        a_load_reg_reg(list,OS_ADDR,OS_ADDR,NR_FUNCTION_RESULT_REG,destreg);

        { do move call }
        cgpara1.init;
        cgpara2.init;
        cgpara3.init;
        paramanager.getintparaloc(pocall_default,1,cgpara1);
        paramanager.getintparaloc(pocall_default,2,cgpara2);
        paramanager.getintparaloc(pocall_default,3,cgpara3);
        { load size }
        a_load_reg_cgpara(list,OS_INT,sizereg,cgpara3);
        { load destination }
        a_load_reg_cgpara(list,OS_ADDR,destreg,cgpara2);
        { load source }
        a_load_reg_cgpara(list,OS_ADDR,sourcereg,cgpara1);
        paramanager.freecgpara(list,cgpara3);
        paramanager.freecgpara(list,cgpara2);
        paramanager.freecgpara(list,cgpara1);
        allocallcpuregisters(list);
        a_call_name(list,'FPC_MOVE',false);
        deallocallcpuregisters(list);
        cgpara3.done;
        cgpara2.done;
        cgpara1.done;
      end;


    procedure tcg.g_releasevaluepara_openarray(list : TAsmList;const l:tlocation);
      var
        cgpara1 : TCGPara;
      begin
        { do move call }
        cgpara1.init;
        paramanager.getintparaloc(pocall_default,1,cgpara1);
        { load source }
        a_load_loc_cgpara(list,l,cgpara1);
        paramanager.freecgpara(list,cgpara1);
        allocallcpuregisters(list);
        a_call_name(list,'FPC_FREEMEM',false);
        deallocallcpuregisters(list);
        cgpara1.done;
      end;


    procedure tcg.g_save_registers(list:TAsmList);
      var
        href : treference;
        size : longint;
        r : integer;
      begin
        { calculate temp. size }
        size:=0;
        for r:=low(saved_standard_registers) to high(saved_standard_registers) do
          if saved_standard_registers[r] in rg[R_INTREGISTER].used_in_proc then
            inc(size,sizeof(aint));

        { mm registers }
        if uses_registers(R_MMREGISTER) then
          begin
            { Make sure we reserve enough space to do the alignment based on the offset
              later on. We can't use the size for this, because the alignment of the start
              of the temp is smaller than needed for an OS_VECTOR }
            inc(size,tcgsize2size[OS_VECTOR]);

            for r:=low(saved_mm_registers) to high(saved_mm_registers) do
              if saved_mm_registers[r] in rg[R_MMREGISTER].used_in_proc then
                inc(size,tcgsize2size[OS_VECTOR]);
          end;

        if size>0 then
          begin
            tg.GetTemp(list,size,sizeof(aint),tt_noreuse,current_procinfo.save_regs_ref);
            include(current_procinfo.flags,pi_has_saved_regs);

            { Copy registers to temp }
            href:=current_procinfo.save_regs_ref;
            for r:=low(saved_standard_registers) to high(saved_standard_registers) do
              begin
                if saved_standard_registers[r] in rg[R_INTREGISTER].used_in_proc then
                  begin
                    a_load_reg_ref(list,OS_ADDR,OS_ADDR,newreg(R_INTREGISTER,saved_standard_registers[r],R_SUBWHOLE),href);
                    inc(href.offset,sizeof(aint));
                  end;
                include(rg[R_INTREGISTER].preserved_by_proc,saved_standard_registers[r]);
              end;

            if uses_registers(R_MMREGISTER) then
              begin
                if (href.offset mod tcgsize2size[OS_VECTOR])<>0 then
                  inc(href.offset,tcgsize2size[OS_VECTOR]-(href.offset mod tcgsize2size[OS_VECTOR]));

                for r:=low(saved_mm_registers) to high(saved_mm_registers) do
                  begin
                    if saved_mm_registers[r] in rg[R_MMREGISTER].used_in_proc then
                      begin
                        a_loadmm_reg_ref(list,OS_VECTOR,OS_VECTOR,newreg(R_MMREGISTER,saved_mm_registers[r],R_SUBNONE),href,nil);
                        inc(href.offset,tcgsize2size[OS_VECTOR]);
                      end;
                    include(rg[R_MMREGISTER].preserved_by_proc,saved_mm_registers[r]);
                  end;
              end;
          end;
      end;


    procedure tcg.g_restore_registers(list:TAsmList);
      var
        href     : treference;
        r        : integer;
        hreg     : tregister;
      begin
        if not(pi_has_saved_regs in current_procinfo.flags) then
          exit;
        { Copy registers from temp }
        href:=current_procinfo.save_regs_ref;
        for r:=low(saved_standard_registers) to high(saved_standard_registers) do
          if saved_standard_registers[r] in rg[R_INTREGISTER].used_in_proc then
            begin
              hreg:=newreg(R_INTREGISTER,saved_standard_registers[r],R_SUBWHOLE);
              { Allocate register so the optimizer does not remove the load }
              a_reg_alloc(list,hreg);
              a_load_ref_reg(list,OS_ADDR,OS_ADDR,href,hreg);
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
                    hreg:=newreg(R_MMREGISTER,saved_mm_registers[r],R_SUBNONE);
                    { Allocate register so the optimizer does not remove the load }
                    a_reg_alloc(list,hreg);
                    a_loadmm_ref_reg(list,OS_VECTOR,OS_VECTOR,href,hreg,nil);
                    inc(href.offset,tcgsize2size[OS_VECTOR]);
                  end;
              end;
          end;
        tg.UnGetTemp(list,current_procinfo.save_regs_ref);
      end;


    procedure tcg.g_profilecode(list : TAsmList);
      begin
      end;


    procedure tcg.g_exception_reason_save(list : TAsmList; const href : treference);
      begin
        a_load_reg_ref(list, OS_INT, OS_INT, NR_FUNCTION_RESULT_REG, href);
      end;


    procedure tcg.g_exception_reason_save_const(list : TAsmList; const href : treference; a: tcgint);
      begin
        a_load_const_ref(list, OS_INT, a, href);
      end;


    procedure tcg.g_exception_reason_load(list : TAsmList; const href : treference);
      begin
        cg.a_reg_alloc(list,NR_FUNCTION_RESULT_REG);
        a_load_ref_reg(list, OS_INT, OS_INT, href, NR_FUNCTION_RESULT_REG);
      end;


    procedure tcg.g_adjust_self_value(list:TAsmList;procdef: tprocdef;ioffset: tcgint);
      var
        hsym : tsym;
        href : treference;
        paraloc : Pcgparalocation;
      begin
        { calculate the parameter info for the procdef }
        procdef.init_paraloc_info(callerside);
        hsym:=tsym(procdef.parast.Find('self'));
        if not(assigned(hsym) and
               (hsym.typ=paravarsym)) then
          internalerror(200305251);
        paraloc:=tparavarsym(hsym).paraloc[callerside].location;
        while paraloc<>nil do
          with paraloc^ do
            begin
              case loc of
                LOC_REGISTER:
                  a_op_const_reg(list,OP_SUB,size,ioffset,register);
                LOC_REFERENCE:
                  begin
                    { offset in the wrapper needs to be adjusted for the stored
                      return address }
                    reference_reset_base(href,reference.index,reference.offset+sizeof(pint),sizeof(pint));
                    a_op_const_ref(list,OP_SUB,size,ioffset,href);
                  end
                else
                  internalerror(200309189);
              end;
              paraloc:=next;
            end;
      end;


    procedure tcg.g_external_wrapper(list : TAsmList; procdef: tprocdef; const externalname: string);
      begin
        a_jmp_name(list,externalname);
      end;


    procedure tcg.a_call_name_static(list : TAsmList;const s : string);
      begin
        a_call_name(list,s,false);
      end;


    procedure tcg.a_call_ref(list : TAsmList;ref: treference);
      var
        tempreg : TRegister;
      begin
        tempreg := getintregister(list, OS_ADDR);
        a_load_ref_reg(list,OS_ADDR,OS_ADDR,ref,tempreg);
        a_call_reg(list,tempreg);
      end;


   function tcg.g_indirect_sym_load(list:TAsmList;const symname: string; const flags: tindsymflags): tregister;
      var
        l: tasmsymbol;
        ref: treference;
        nlsymname: string;
      begin
        result := NR_NO;
        case target_info.system of
          system_powerpc_darwin,
          system_i386_darwin,
          system_i386_iphonesim,
          system_powerpc64_darwin,
          system_arm_darwin:
            begin
              nlsymname:='L'+symname+'$non_lazy_ptr';
              l:=current_asmdata.getasmsymbol(nlsymname);
              if not(assigned(l)) then
                begin
                  new_section(current_asmdata.asmlists[al_picdata],sec_data_nonlazy,'',sizeof(pint));
                  l:=current_asmdata.DefineAsmSymbol(nlsymname,AB_LOCAL,AT_DATA);
                  current_asmdata.asmlists[al_picdata].concat(tai_symbol.create(l,0));
                  if not(is_weak in flags) then
                    current_asmdata.asmlists[al_picdata].concat(tai_directive.Create(asd_indirect_symbol,current_asmdata.RefAsmSymbol(symname).Name))
                  else
                    current_asmdata.asmlists[al_picdata].concat(tai_directive.Create(asd_indirect_symbol,current_asmdata.WeakRefAsmSymbol(symname).Name));
{$ifdef cpu64bitaddr}
                  current_asmdata.asmlists[al_picdata].concat(tai_const.create_64bit(0));
{$else cpu64bitaddr}
                  current_asmdata.asmlists[al_picdata].concat(tai_const.create_32bit(0));
{$endif cpu64bitaddr}
                end;
              result := getaddressregister(list);
              reference_reset_symbol(ref,l,0,sizeof(pint));
              { a_load_ref_reg will turn this into a pic-load if needed }
              a_load_ref_reg(list,OS_ADDR,OS_ADDR,ref,result);
            end;
        end;
      end;


    procedure tcg.g_maybe_got_init(list: TAsmList);
      begin
      end;

    procedure tcg.g_call(list: TAsmList;const s: string);
      begin
        allocallcpuregisters(list);
        a_call_name(list,s,false);
        deallocallcpuregisters(list);
      end;

    procedure tcg.g_local_unwind(list: TAsmList; l: TAsmLabel);
      begin
        a_jmp_always(list,l);
      end;

    procedure tcg.a_loadmm_reg_reg(list: TAsmList; fromsize, tosize: tcgsize; reg1, reg2: tregister; shuffle: pmmshuffle);
      begin
        internalerror(200807231);
      end;


    procedure tcg.a_loadmm_ref_reg(list: TAsmList; fromsize, tosize: tcgsize; const ref: treference; reg: tregister; shuffle: pmmshuffle);
      begin
        internalerror(200807232);
      end;


    procedure tcg.a_loadmm_reg_ref(list: TAsmList; fromsize, tosize: tcgsize; reg: tregister; const ref: treference; shuffle: pmmshuffle);
      begin
        internalerror(200807233);
      end;


    procedure tcg.a_opmm_reg_reg(list: TAsmList; Op: TOpCG; size: tcgsize; src, dst: tregister; shuffle: pmmshuffle);
      begin
        internalerror(200807234);
      end;


    function tcg.getflagregister(list: TAsmList; size: Tcgsize): Tregister;
      begin
        Result:=TRegister(0);
        internalerror(200807238);
      end;

{*****************************************************************************
                                    TCG64
*****************************************************************************}

{$ifndef cpu64bitalu}
    procedure tcg64.a_op64_const_reg_reg(list: TAsmList;op:TOpCG;size : tcgsize;value : int64; regsrc,regdst : tregister64);
      begin
        a_load64_reg_reg(list,regsrc,regdst);
        a_op64_const_reg(list,op,size,value,regdst);
      end;


    procedure tcg64.a_op64_reg_reg_reg(list: TAsmList;op:TOpCG;size : tcgsize;regsrc1,regsrc2,regdst : tregister64);
      var
        tmpreg64 : tregister64;
      begin
        { when src1=dst then we need to first create a temp to prevent
          overwriting src1 with src2 }
        if (regsrc1.reghi=regdst.reghi) or
           (regsrc1.reglo=regdst.reghi) or
           (regsrc1.reghi=regdst.reglo) or
           (regsrc1.reglo=regdst.reglo) then
          begin
            tmpreg64.reglo:=cg.getintregister(list,OS_32);
            tmpreg64.reghi:=cg.getintregister(list,OS_32);
            a_load64_reg_reg(list,regsrc2,tmpreg64);
            a_op64_reg_reg(list,op,size,regsrc1,tmpreg64);
            a_load64_reg_reg(list,tmpreg64,regdst);
          end
        else
          begin
            a_load64_reg_reg(list,regsrc2,regdst);
            a_op64_reg_reg(list,op,size,regsrc1,regdst);
          end;
      end;


    procedure tcg64.a_op64_const_subsetref(list : TAsmList; Op : TOpCG; size : TCGSize; a : int64; const sref: tsubsetreference);
      var
        tmpreg64 : tregister64;
      begin
        tmpreg64.reglo:=cg.getintregister(list,OS_32);
        tmpreg64.reghi:=cg.getintregister(list,OS_32);
        a_load64_subsetref_reg(list,sref,tmpreg64);
        a_op64_const_reg(list,op,size,a,tmpreg64);
        a_load64_reg_subsetref(list,tmpreg64,sref);
      end;


    procedure tcg64.a_op64_reg_subsetref(list : TAsmList; Op : TOpCG; size : TCGSize; reg: tregister64; const sref: tsubsetreference);
      var
        tmpreg64 : tregister64;
      begin
        tmpreg64.reglo:=cg.getintregister(list,OS_32);
        tmpreg64.reghi:=cg.getintregister(list,OS_32);
        a_load64_subsetref_reg(list,sref,tmpreg64);
        a_op64_reg_reg(list,op,size,reg,tmpreg64);
        a_load64_reg_subsetref(list,tmpreg64,sref);
      end;


    procedure tcg64.a_op64_ref_subsetref(list : TAsmList; Op : TOpCG; size : TCGSize; const ref: treference; const sref: tsubsetreference);
      var
        tmpreg64 : tregister64;
      begin
        tmpreg64.reglo:=cg.getintregister(list,OS_32);
        tmpreg64.reghi:=cg.getintregister(list,OS_32);
        a_load64_subsetref_reg(list,sref,tmpreg64);
        a_op64_ref_reg(list,op,size,ref,tmpreg64);
        a_load64_reg_subsetref(list,tmpreg64,sref);
      end;


    procedure tcg64.a_op64_subsetref_subsetref(list : TAsmList; Op : TOpCG; size : TCGSize; const ssref,dsref: tsubsetreference);
      var
        tmpreg64 : tregister64;
      begin
        tmpreg64.reglo:=cg.getintregister(list,OS_32);
        tmpreg64.reghi:=cg.getintregister(list,OS_32);
        a_load64_subsetref_reg(list,ssref,tmpreg64);
        a_op64_reg_subsetref(list,op,size,tmpreg64,dsref);
      end;


    procedure tcg64.a_op64_const_reg_reg_checkoverflow(list: TAsmList;op:TOpCG;size : tcgsize;value : int64;regsrc,regdst : tregister64;setflags : boolean;var ovloc : tlocation);
      begin
        a_op64_const_reg_reg(list,op,size,value,regsrc,regdst);
        ovloc.loc:=LOC_VOID;
      end;


    procedure tcg64.a_op64_reg_reg_reg_checkoverflow(list: TAsmList;op:TOpCG;size : tcgsize;regsrc1,regsrc2,regdst : tregister64;setflags : boolean;var ovloc : tlocation);
      begin
        a_op64_reg_reg_reg(list,op,size,regsrc1,regsrc2,regdst);
        ovloc.loc:=LOC_VOID;
      end;


    procedure tcg64.a_load64_loc_subsetref(list : TAsmList;const l: tlocation; const sref : tsubsetreference);
      begin
        case l.loc of
          LOC_REFERENCE, LOC_CREFERENCE:
            a_load64_ref_subsetref(list,l.reference,sref);
          LOC_REGISTER,LOC_CREGISTER:
            a_load64_reg_subsetref(list,l.register64,sref);
          LOC_CONSTANT :
            a_load64_const_subsetref(list,l.value64,sref);
          LOC_SUBSETREF,LOC_CSUBSETREF:
            a_load64_subsetref_subsetref(list,l.sref,sref);
          else
            internalerror(2006082210);
        end;
      end;


    procedure tcg64.a_load64_subsetref_loc(list: TAsmlist; const sref: tsubsetreference; const l: tlocation);
      begin
        case l.loc of
          LOC_REFERENCE, LOC_CREFERENCE:
            a_load64_subsetref_ref(list,sref,l.reference);
          LOC_REGISTER,LOC_CREGISTER:
            a_load64_subsetref_reg(list,sref,l.register64);
          LOC_SUBSETREF,LOC_CSUBSETREF:
            a_load64_subsetref_subsetref(list,sref,l.sref);
          else
            internalerror(2006082211);
        end;
      end;
{$endif cpu64bitalu}

    function asmsym2indsymflags(sym: TAsmSymbol): tindsymflags;
      begin
        result:=[];
        if sym.typ<>AT_FUNCTION then
          include(result,is_data);
        if sym.bind=AB_WEAK_EXTERNAL then
          include(result,is_weak);
      end;

    procedure destroy_codegen;
      begin
        cg.free;
        cg:=nil;
{$ifndef cpu64bitalu}
        cg64.free;
        cg64:=nil;
{$endif cpu64bitalu}
      end;

end.
