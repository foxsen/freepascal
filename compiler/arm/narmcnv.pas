{
    Copyright (c) 1998-2002 by Florian Klaempfl

    Generate ARM assembler for type converting nodes

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
unit narmcnv;

{$i fpcdefs.inc}

interface

    uses
      node,ncnv,ncgcnv,defcmp;

    type
       tarmtypeconvnode = class(tcgtypeconvnode)
         protected
           function first_int_to_real: tnode;override;
         { procedure second_int_to_int;override; }
         { procedure second_string_to_string;override; }
         { procedure second_cstring_to_pchar;override; }
         { procedure second_string_to_chararray;override; }
         { procedure second_array_to_pointer;override; }
         // function first_int_to_real: tnode; override;
         { procedure second_pointer_to_array;override; }
         { procedure second_chararray_to_string;override; }
         { procedure second_char_to_string;override; }
           procedure second_int_to_real;override;
         // procedure second_real_to_real;override;
         { procedure second_cord_to_pointer;override; }
         { procedure second_proc_to_procvar;override; }
         { procedure second_bool_to_int;override; }
           procedure second_int_to_bool;override;
         { procedure second_load_smallset;override;  }
         { procedure second_ansistring_to_pchar;override; }
         { procedure second_pchar_to_string;override; }
         { procedure second_class_to_intf;override; }
         { procedure second_char_to_char;override; }
       end;

implementation

   uses
      verbose,globtype,globals,systems,
      symconst,symdef,aasmbase,aasmtai,aasmdata,
      defutil,
      cgbase,cgutils,
      pass_1,pass_2,procinfo,
      ncon,ncal,
      ncgutil,
      cpubase,cpuinfo,aasmcpu,
      rgobj,tgobj,cgobj,hlcgobj,cgcpu;


{*****************************************************************************
                             FirstTypeConv
*****************************************************************************}

    function tarmtypeconvnode.first_int_to_real: tnode;
      var
        fname: string[19];
      begin
        if cs_fp_emulation in current_settings.moduleswitches then
          result:=inherited first_int_to_real
        else
          begin
            { converting a 64bit integer to a float requires a helper }
            if is_64bitint(left.resultdef) or
              is_currency(left.resultdef) then
              begin
                { hack to avoid double division by 10000, as it's
                  already done by typecheckpass.resultdef_int_to_real }
                if is_currency(left.resultdef) then
                  left.resultdef := s64inttype;
                if is_signed(left.resultdef) then
                  fname := 'fpc_int64_to_double'
                else
                  fname := 'fpc_qword_to_double';
                result := ccallnode.createintern(fname,ccallparanode.create(
                  left,nil));
                left:=nil;
                if (tfloatdef(resultdef).floattype=s32real) then
                  inserttypeconv(result,s32floattype);
                firstpass(result);
                exit;
              end
            else
              { other integers are supposed to be 32 bit }
              begin
                if is_signed(left.resultdef) then
                  inserttypeconv(left,s32inttype)
                else
                  inserttypeconv(left,u32inttype);
                firstpass(left);
              end;
            result := nil;
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
                internalerror(2009112702);
            end;
          end;
      end;


    procedure tarmtypeconvnode.second_int_to_real;
      const
        signedprec2vfpop: array[boolean,OS_F32..OS_F64] of tasmop =
          ((A_FUITOS,A_FUITOD),
           (A_FSITOS,A_FSITOD));
      var
        instr : taicpu;
        href : treference;
        l1,l2 : tasmlabel;
        hregister : tregister;
        signed : boolean;
      begin
        case current_settings.fputype of
          fpu_fpa,
          fpu_fpa10,
          fpu_fpa11:
            begin
              { convert first to double to avoid precision loss }
              location_reset(location,LOC_FPUREGISTER,def_cgsize(resultdef));
              hlcg.location_force_reg(current_asmdata.CurrAsmList,left.location,left.resultdef,u32inttype,true);
              location.register:=cg.getfpuregister(current_asmdata.CurrAsmList,location.size);
              instr:=taicpu.op_reg_reg(A_FLT,location.register,left.location.register);
              if is_signed(left.resultdef) then
                begin
                  instr.oppostfix:=cgsize2fpuoppostfix[def_cgsize(resultdef)];
                  current_asmdata.CurrAsmList.concat(instr);
                end
              else
                begin
                  { flt does a signed load, fix this }
                  case tfloatdef(resultdef).floattype of
                    s32real,
                    s64real:
                      begin
                        { converting dword to s64real first and cut off at the end avoids precision loss }
                        instr.oppostfix:=PF_D;
                        current_asmdata.CurrAsmList.concat(instr);

                        current_asmdata.getdatalabel(l1);
                        current_asmdata.getjumplabel(l2);
                        reference_reset_symbol(href,l1,0,const_align(8));

                        current_asmdata.CurrAsmList.concat(Taicpu.op_reg_const(A_CMP,left.location.register,0));
                        cg.a_jmp_flags(current_asmdata.CurrAsmList,F_GE,l2);

                        hregister:=cg.getfpuregister(current_asmdata.CurrAsmList,OS_F64);
                        new_section(current_asmdata.asmlists[al_typedconsts],sec_rodata_norel,l1.name,const_align(8));
                        current_asmdata.asmlists[al_typedconsts].concat(Tai_label.Create(l1));
                        { I got this constant from a test program (FK) }
                        current_asmdata.asmlists[al_typedconsts].concat(Tai_const.Create_32bit($41f00000));
                        current_asmdata.asmlists[al_typedconsts].concat(Tai_const.Create_32bit(0));

                        cg.a_loadfpu_ref_reg(current_asmdata.CurrAsmList,OS_F64,OS_F64,href,hregister);
                        current_asmdata.CurrAsmList.concat(setoppostfix(taicpu.op_reg_reg_reg(A_ADF,location.register,hregister,location.register),PF_D));
                        cg.a_label(current_asmdata.CurrAsmList,l2);

                        { cut off if we should convert to single }
                        if tfloatdef(resultdef).floattype=s32real then
                          begin
                            hregister:=location.register;
                            location.register:=cg.getfpuregister(current_asmdata.CurrAsmList,location.size);
                            current_asmdata.CurrAsmList.concat(setoppostfix(taicpu.op_reg_reg(A_MVF,location.register,hregister),PF_S));
                          end;
                      end;
                    else
                      internalerror(200410031);
                  end;
              end;
            end;
          fpu_vfpv2,
          fpu_vfpv3,
          fpu_vfpv3_d16:
            begin
              location_reset(location,LOC_MMREGISTER,def_cgsize(resultdef));
              signed:=left.location.size=OS_S32;
              location_force_mmregscalar(current_asmdata.CurrAsmList,left.location,false);
              if (left.location.size<>OS_F32) then
                internalerror(2009112703);
              if left.location.size<>location.size then
                location.register:=cg.getmmregister(current_asmdata.CurrAsmList,location.size)
              else
                location.register:=left.location.register;
              current_asmdata.CurrAsmList.concat(taicpu.op_reg_reg(
                signedprec2vfpop[signed,location.size],location.register,left.location.register));
            end;
        end;
      end;


    procedure tarmtypeconvnode.second_int_to_bool;
      var
        hreg1,
        hregister : tregister;
        href      : treference;
        resflags  : tresflags;
        hlabel,oldTrueLabel,oldFalseLabel : tasmlabel;
        newsize   : tcgsize;
      begin
         oldTrueLabel:=current_procinfo.CurrTrueLabel;
         oldFalseLabel:=current_procinfo.CurrFalseLabel;
         current_asmdata.getjumplabel(current_procinfo.CurrTrueLabel);
         current_asmdata.getjumplabel(current_procinfo.CurrFalseLabel);
         secondpass(left);
         if codegenerror then
          exit;

         { Explicit typecasts from any ordinal type to a boolean type }
         { must not change the ordinal value                          }
         if (nf_explicit in flags) and
            not(left.location.loc in [LOC_FLAGS,LOC_JUMP]) then
           begin
              location_copy(location,left.location);
              newsize:=def_cgsize(resultdef);
              { change of size? change sign only if location is LOC_(C)REGISTER? Then we have to sign/zero-extend }
              if (tcgsize2size[newsize]<>tcgsize2size[left.location.size]) or
                 ((newsize<>left.location.size) and (location.loc in [LOC_REGISTER,LOC_CREGISTER])) then
                hlcg.location_force_reg(current_asmdata.CurrAsmList,location,left.resultdef,resultdef,true)
              else
                location.size:=newsize;
              current_procinfo.CurrTrueLabel:=oldTrueLabel;
              current_procinfo.CurrFalseLabel:=oldFalseLabel;
              exit;
           end;

         { Load left node into flag F_NE/F_E }
         resflags:=F_NE;
         case left.location.loc of
            LOC_CREFERENCE,
            LOC_REFERENCE :
              begin
                if left.location.size in [OS_64,OS_S64] then
                 begin
                   hregister:=cg.getintregister(current_asmdata.CurrAsmList,OS_INT);
                   cg.a_load_ref_reg(current_asmdata.CurrAsmList,OS_32,OS_32,left.location.reference,hregister);
                   href:=left.location.reference;
                   inc(href.offset,4);
                   tcgarm(cg).cgsetflags:=true;
                   cg.a_op_ref_reg(current_asmdata.CurrAsmList,OP_OR,OS_32,href,hregister);
                   tcgarm(cg).cgsetflags:=false;
                 end
                else
                 begin
                   hlcg.location_force_reg(current_asmdata.CurrAsmList,left.location,left.resultdef,left.resultdef,true);
                   tcgarm(cg).cgsetflags:=true;
                   cg.a_op_reg_reg(current_asmdata.CurrAsmList,OP_OR,left.location.size,left.location.register,left.location.register);
                   tcgarm(cg).cgsetflags:=false;
                 end;
              end;
            LOC_FLAGS :
              begin
                resflags:=left.location.resflags;
              end;
            LOC_REGISTER,LOC_CREGISTER :
              begin
                if left.location.size in [OS_64,OS_S64] then
                 begin
                   hregister:=cg.getintregister(current_asmdata.CurrAsmList,OS_32);
                   cg.a_load_reg_reg(current_asmdata.CurrAsmList,OS_32,OS_32,left.location.register64.reglo,hregister);
                   tcgarm(cg).cgsetflags:=true;
                   cg.a_op_reg_reg(current_asmdata.CurrAsmList,OP_OR,OS_32,left.location.register64.reghi,hregister);
                   tcgarm(cg).cgsetflags:=false;
                 end
                else
                 begin
                   tcgarm(cg).cgsetflags:=true;
                   cg.a_op_reg_reg(current_asmdata.CurrAsmList,OP_OR,left.location.size,left.location.register,left.location.register);
                   tcgarm(cg).cgsetflags:=false;
                 end;
              end;
            LOC_JUMP :
              begin
                hregister:=cg.getintregister(current_asmdata.CurrAsmList,OS_INT);
                current_asmdata.getjumplabel(hlabel);
                cg.a_label(current_asmdata.CurrAsmList,current_procinfo.CurrTrueLabel);
                cg.a_load_const_reg(current_asmdata.CurrAsmList,OS_INT,1,hregister);
                cg.a_jmp_always(current_asmdata.CurrAsmList,hlabel);
                cg.a_label(current_asmdata.CurrAsmList,current_procinfo.CurrFalseLabel);
                cg.a_load_const_reg(current_asmdata.CurrAsmList,OS_INT,0,hregister);
                cg.a_label(current_asmdata.CurrAsmList,hlabel);
                tcgarm(cg).cgsetflags:=true;
                cg.a_op_reg_reg(current_asmdata.CurrAsmList,OP_OR,OS_INT,hregister,hregister);
                tcgarm(cg).cgsetflags:=false;
              end;
            else
              internalerror(200311301);
         end;
         { load flags to register }
         location_reset(location,LOC_REGISTER,def_cgsize(resultdef));
         hreg1:=cg.getintregister(current_asmdata.CurrAsmList,location.size);
         cg.g_flags2reg(current_asmdata.CurrAsmList,location.size,resflags,hreg1);
         if (is_cbool(resultdef)) then
           cg.a_op_reg_reg(current_asmdata.CurrAsmList,OP_NEG,location.size,hreg1,hreg1);

{$ifndef cpu64bitalu}
         if (location.size in [OS_64,OS_S64]) then
           begin
             location.register64.reglo:=hreg1;
             location.register64.reghi:=cg.getintregister(current_asmdata.CurrAsmList,OS_32);
             if (is_cbool(resultdef)) then
               { reglo is either 0 or -1 -> reghi has to become the same }
               cg.a_load_reg_reg(current_asmdata.CurrAsmList,OS_32,OS_32,location.register64.reglo,location.register64.reghi)
             else
               { unsigned }
               cg.a_load_const_reg(current_asmdata.CurrAsmList,OS_32,0,location.register64.reghi);
           end
         else
{$endif cpu64bitalu}
           location.register:=hreg1;

         current_procinfo.CurrTrueLabel:=oldTrueLabel;
         current_procinfo.CurrFalseLabel:=oldFalseLabel;
      end;


begin
  ctypeconvnode:=tarmtypeconvnode;
end.
