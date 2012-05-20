{
    Copyright (c) 1998-2002 by Florian Klaempfl

    Generates ARM inline nodes

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
unit narminl;

{$i fpcdefs.inc}

interface

    uses
      node,ninl,ncginl;

    type
      tarminlinenode = class(tcgInlineNode)
        function first_abs_real: tnode; override;
        function first_sqr_real: tnode; override;
        function first_sqrt_real: tnode; override;
        { atn,sin,cos,lgn isn't supported by the linux fpe
        function first_arctan_real: tnode; override;
        function first_ln_real: tnode; override;
        function first_cos_real: tnode; override;
        function first_sin_real: tnode; override;
        }
        procedure second_abs_real; override;
        procedure second_sqr_real; override;
        procedure second_sqrt_real; override;
        { atn,sin,cos,lgn isn't supported by the linux fpe
        procedure second_arctan_real; override;
        procedure second_ln_real; override;
        procedure second_cos_real; override;
        procedure second_sin_real; override;
        }
        procedure second_prefetch; override;
      private
        procedure load_fpu_location(out singleprec: boolean);
      end;


implementation

    uses
      globtype,systems,
      cutils,verbose,globals,fmodule,
      cpuinfo,
      symconst,symdef,
      aasmbase,aasmtai,aasmdata,aasmcpu,
      cgbase,cgutils,
      pass_1,pass_2,
      cpubase,paramgr,
      nbas,ncon,ncal,ncnv,nld,
      tgobj,ncgutil,cgobj,cg64f32,rgobj,rgcpu,cgcpu;

{*****************************************************************************
                              tarminlinenode
*****************************************************************************}

    procedure tarminlinenode.load_fpu_location(out singleprec: boolean);
      begin
        secondpass(left);
        case current_settings.fputype of
          fpu_fpa,
          fpu_fpa10,
          fpu_fpa11:
            begin
              location_force_fpureg(current_asmdata.CurrAsmList,left.location,true);
              location_copy(location,left.location);
              if left.location.loc=LOC_CFPUREGISTER then
                begin
                 location.register:=cg.getfpuregister(current_asmdata.CurrAsmList,location.size);
                 location.loc := LOC_FPUREGISTER;
               end;
            end;
          fpu_vfpv2,
          fpu_vfpv3,
          fpu_vfpv3_d16:
            begin
              location_force_mmregscalar(current_asmdata.CurrAsmList,left.location,true);
              location_copy(location,left.location);
              if left.location.loc=LOC_CMMREGISTER then
                begin
                 location.register:=cg.getmmregister(current_asmdata.CurrAsmList,location.size);
                 location.loc := LOC_MMREGISTER;
               end;
            end;
          else
            internalerror(2009111801);
        end;
        singleprec:=tfloatdef(left.resultdef).floattype=s32real;
      end;


    function tarminlinenode.first_abs_real : tnode;
      begin
        if (cs_fp_emulation in current_settings.moduleswitches) then
          result:=inherited first_abs_real
        else
          begin
            case current_settings.fputype of
              fpu_fpa,
              fpu_fpa10,
              fpu_fpa11:
                expectloc:=LOC_FPUREGISTER;
              fpu_vfpv2,
              fpu_vfpv3,
              fpu_vfpv3_d16:
                expectloc:=LOC_MMREGISTER;
              else
                internalerror(2009112401);
            end;
            first_abs_real:=nil;
          end;
      end;


    function tarminlinenode.first_sqr_real : tnode;
      begin
        if (cs_fp_emulation in current_settings.moduleswitches) then
          result:=inherited first_sqr_real
        else
          begin
            case current_settings.fputype of
              fpu_fpa,
              fpu_fpa10,
              fpu_fpa11:
                expectloc:=LOC_FPUREGISTER;
              fpu_vfpv2,
              fpu_vfpv3,
              fpu_vfpv3_d16:
                expectloc:=LOC_MMREGISTER;
              else
                internalerror(2009112402);
            end;
            first_sqr_real:=nil;
          end;
      end;


    function tarminlinenode.first_sqrt_real : tnode;
      begin
        if cs_fp_emulation in current_settings.moduleswitches then
          result:=inherited first_sqrt_real
        else
          begin
            case current_settings.fputype of
              fpu_fpa,
              fpu_fpa10,
              fpu_fpa11:
                expectloc:=LOC_FPUREGISTER;
              fpu_vfpv2,
              fpu_vfpv3,
              fpu_vfpv3_d16:
                expectloc:=LOC_MMREGISTER;
              else
                internalerror(2009112403);
            end;
            first_sqrt_real := nil;
          end;
      end;


    { atn,sin,cos,lgn isn't supported by the linux fpe
    function tarminlinenode.first_arctan_real: tnode;
      begin
        expectloc:=LOC_FPUREGISTER;
        result:=nil;
      end;


    function tarminlinenode.first_ln_real: tnode;
      begin
        expectloc:=LOC_FPUREGISTER;
        result:=nil;
      end;

    function tarminlinenode.first_cos_real: tnode;
      begin
        expectloc:=LOC_FPUREGISTER;
        result:=nil;
      end;


    function tarminlinenode.first_sin_real: tnode;
      begin
        expectloc:=LOC_FPUREGISTER;
        result:=nil;
      end;
    }


    procedure tarminlinenode.second_abs_real;
      var
        singleprec: boolean;
        op: TAsmOp;
      begin
        load_fpu_location(singleprec);
        case current_settings.fputype of
          fpu_fpa,
          fpu_fpa10,
          fpu_fpa11:
            current_asmdata.CurrAsmList.concat(setoppostfix(taicpu.op_reg_reg(A_ABS,location.register,left.location.register),get_fpu_postfix(resultdef)));
          fpu_vfpv2,
          fpu_vfpv3,
          fpu_vfpv3_d16:
            begin
              if singleprec then
                op:=A_FABSS
              else
                op:=A_FABSD;
              current_asmdata.CurrAsmList.concat(taicpu.op_reg_reg(op,location.register,left.location.register));
            end;
        else
          internalerror(2009111402);
        end;
      end;


    procedure tarminlinenode.second_sqr_real;
      var
        singleprec: boolean;
        op: TAsmOp;
      begin
        load_fpu_location(singleprec);
        case current_settings.fputype of
          fpu_fpa,
          fpu_fpa10,
          fpu_fpa11:
            current_asmdata.CurrAsmList.concat(setoppostfix(taicpu.op_reg_reg_reg(A_MUF,location.register,left.location.register,left.location.register),get_fpu_postfix(resultdef)));
          fpu_vfpv2,
          fpu_vfpv3,
          fpu_vfpv3_d16:
            begin
              if singleprec then
                op:=A_FMULS
              else
                op:=A_FMULD;
              current_asmdata.CurrAsmList.concat(taicpu.op_reg_reg_reg(op,location.register,left.location.register,left.location.register));
            end;
        else
          internalerror(2009111403);
        end;
      end;


    procedure tarminlinenode.second_sqrt_real;
      var
        singleprec: boolean;
        op: TAsmOp;
      begin
        load_fpu_location(singleprec);
        case current_settings.fputype of
          fpu_fpa,
          fpu_fpa10,
          fpu_fpa11:
            current_asmdata.CurrAsmList.concat(setoppostfix(taicpu.op_reg_reg(A_SQT,location.register,left.location.register),get_fpu_postfix(resultdef)));
          fpu_vfpv2,
          fpu_vfpv3,
          fpu_vfpv3_d16:
            begin
              if singleprec then
                op:=A_FSQRTS
              else
                op:=A_FSQRTD;
              current_asmdata.CurrAsmList.concat(taicpu.op_reg_reg(op,location.register,left.location.register));
            end;
        else
          internalerror(2009111402);
        end;
      end;


    { atn, sin, cos, lgn isn't supported by the linux fpe
    procedure tarminlinenode.second_arctan_real;
      begin
        load_fpu_location;
        current_asmdata.CurrAsmList.concat(setoppostfix(taicpu.op_reg_reg(A_ATN,location.register,left.location.register),get_fpu_postfix(resultdef)));
      end;


    procedure tarminlinenode.second_ln_real;
      begin
        load_fpu_location;
        current_asmdata.CurrAsmList.concat(setoppostfix(taicpu.op_reg_reg(A_LGN,location.register,left.location.register),get_fpu_postfix(resultdef)));
      end;

    procedure tarminlinenode.second_cos_real;
      begin
        load_fpu_location;
        current_asmdata.CurrAsmList.concat(setoppostfix(taicpu.op_reg_reg(A_COS,location.register,left.location.register),get_fpu_postfix(resultdef)));
      end;


    procedure tarminlinenode.second_sin_real;
      begin
        load_fpu_location;
        current_asmdata.CurrAsmList.concat(setoppostfix(taicpu.op_reg_reg(A_SIN,location.register,left.location.register),get_fpu_postfix(resultdef)));
      end;
    }

    procedure tarminlinenode.second_prefetch;
      var
        ref : treference;
        r : tregister;
      begin
        if current_settings.cputype>=cpu_armv5 then
          begin
            secondpass(left);
            case left.location.loc of
              LOC_CREFERENCE,
              LOC_REFERENCE:
                begin
                  r:=cg.getintregister(current_asmdata.CurrAsmList,OS_ADDR);
                  cg.a_loadaddr_ref_reg(current_asmdata.CurrAsmList,left.location.reference,r);
                  reference_reset_base(ref,r,0,left.location.reference.alignment);
                  { since the address might be nil we can't use ldr for older cpus }
                  current_asmdata.CurrAsmList.concat(taicpu.op_ref(A_PLD,ref));
                end;
              else
                internalerror(200402021);
            end;
          end;
      end;


begin
  cinlinenode:=tarminlinenode;
end.
