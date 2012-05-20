{
    Copyright (c) 1998-2002 by Florian Klaempfl

    Generate generic mathematical nodes

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
unit ncgmat;

{$i fpcdefs.inc}

interface

    uses
      node,nmat,cpubase,cgbase;

    type
      tcgunaryminusnode = class(tunaryminusnode)
      protected
         { This routine is called to change the sign of the
           floating point value in the floating point
           register r.

           This routine should be overridden, since
           the generic version is not optimal at all. The
           generic version assumes that floating
           point values are stored in the register
           in IEEE-754 format.
         }
         procedure emit_float_sign_change(r: tregister; _size : tcgsize);virtual;
{$ifdef SUPPORT_MMX}
         procedure second_mmx;virtual;abstract;
{$endif SUPPORT_MMX}
{$ifndef cpu64bitalu}
         procedure second_64bit;virtual;
{$endif not cpu64bitalu}
         procedure second_integer;virtual;
         procedure second_float;virtual;
      public
         procedure pass_generate_code;override;
      end;

      tcgmoddivnode = class(tmoddivnode)
         procedure pass_generate_code;override;
      protected
         { This routine must do an actual 32-bit division, be it
           signed or unsigned. The result must set into the the
           @var(num) register.

           @param(signed Indicates if the division must be signed)
           @param(denum  Register containing the denominator
           @param(num    Register containing the numerator, will also receive result)

           The actual optimizations regarding shifts have already
           been done and emitted, so this should really a do a divide.
         }
         procedure emit_div_reg_reg(signed: boolean;denum,num : tregister);virtual;abstract;
         { This routine must do an actual 32-bit modulo, be it
           signed or unsigned. The result must set into the the
           @var(num) register.

           @param(signed Indicates if the modulo must be signed)
           @param(denum  Register containing the denominator
           @param(num    Register containing the numerator, will also receive result)

           The actual optimizations regarding shifts have already
           been done and emitted, so this should really a do a modulo.
         }
         procedure emit_mod_reg_reg(signed: boolean;denum,num : tregister);virtual;abstract;
{$ifndef cpu64bitalu}
         { This routine must do an actual 64-bit division, be it
           signed or unsigned. The result must set into the the
           @var(num) register.

           @param(signed Indicates if the division must be signed)
           @param(denum  Register containing the denominator
           @param(num    Register containing the numerator, will also receive result)

           The actual optimizations regarding shifts have already
           been done and emitted, so this should really a do a divide.
           Currently, this routine should only be implemented on
           64-bit systems, otherwise a helper is called in 1st pass.
         }
         procedure emit64_div_reg_reg(signed: boolean;denum,num : tregister64);virtual;
{$endif not cpu64bitalu}
      end;

      tcgshlshrnode = class(tshlshrnode)
{$ifndef cpu64bitalu}
         procedure second_64bit;virtual;
{$endif not cpu64bitalu}
         procedure second_integer;virtual;
         procedure pass_generate_code;override;
      end;

      tcgnotnode = class(tnotnode)
      protected
         procedure second_boolean;virtual;abstract;
{$ifdef SUPPORT_MMX}
         procedure second_mmx;virtual;abstract;
{$endif SUPPORT_MMX}
{$ifndef cpu64bitalu}
         procedure second_64bit;virtual;
{$endif not cpu64bitalu}
         procedure second_integer;virtual;
      public
         procedure pass_generate_code;override;
      end;


implementation

    uses
      globtype,systems,
      cutils,verbose,globals,
      symconst,symtype,symdef,aasmbase,aasmtai,aasmdata,aasmcpu,defutil,
      parabase,
      pass_2,
      ncon,
      tgobj,ncgutil,cgobj,cgutils,paramgr,hlcgobj
{$ifndef cpu64bitalu}
      ,cg64f32
{$endif not cpu64bitalu}
      ;

{*****************************************************************************
                          TCGUNARYMINUSNODE
*****************************************************************************}

    procedure tcgunaryminusnode.emit_float_sign_change(r: tregister; _size : tcgsize);
      var
        href,
        href2 : treference;
      begin
        { get a temporary memory reference to store the floating
          point value
        }
        tg.gettemp(current_asmdata.CurrAsmList,tcgsize2size[_size],tcgsize2size[_size],tt_normal,href);
        { store the floating point value in the temporary memory area }
        cg.a_loadfpu_reg_ref(current_asmdata.CurrAsmList,_size,_size,r,href);
        { only single and double ieee are supported, for little endian
          the signed bit is in the second dword }
        href2:=href;
        case _size of
          OS_F64 :
            if target_info.endian = endian_little then
              inc(href2.offset,4);
          OS_F32 :
            ;
          else
            internalerror(200406021);
        end;
        { flip sign-bit (bit 31/63) of single/double }
        cg.a_op_const_ref(current_asmdata.CurrAsmList,OP_XOR,OS_32,aint($80000000),href2);
        cg.a_loadfpu_ref_reg(current_asmdata.CurrAsmList,_size,_size,href,r);
        tg.ungetiftemp(current_asmdata.CurrAsmList,href);
      end;


{$ifndef cpu64bitalu}
    procedure tcgunaryminusnode.second_64bit;
      var
        tr: tregister;
        hl: tasmlabel;
      begin
        secondpass(left);
        location_reset(location,LOC_REGISTER,left.location.size);
        location.register64.reglo:=cg.getintregister(current_asmdata.CurrAsmList,OS_INT);
        location.register64.reghi:=cg.getintregister(current_asmdata.CurrAsmList,OS_INT);
        cg64.a_op64_loc_reg(current_asmdata.CurrAsmList,OP_NEG,OS_S64,
          left.location,joinreg64(location.register64.reglo,location.register64.reghi));
        { there's only overflow in case left was low(int64) -> -left = left }
        if (cs_check_overflow in current_settings.localswitches) then
          begin
            tr:=cg.getintregister(current_asmdata.CurrAsmList,OS_INT);
            cg.a_op_const_reg_reg(current_asmdata.CurrAsmList,OP_XOR,OS_INT,
              aint($80000000),location.register64.reghi,tr);
            cg.a_op_reg_reg(current_asmdata.CurrAsmList,OP_OR,OS_INT,
              location.register64.reglo,tr);
            current_asmdata.getjumplabel(hl);
            cg.a_cmp_const_reg_label(current_asmdata.CurrAsmList,OS_INT,OC_NE,0,tr,hl);
            cg.a_call_name(current_asmdata.CurrAsmList,'FPC_OVERFLOW',false);
            cg.a_label(current_asmdata.CurrAsmList,hl);
          end;
      end;
{$endif not cpu64bitalu}

    procedure tcgunaryminusnode.second_float;
      begin
        secondpass(left);
        location_reset(location,LOC_FPUREGISTER,def_cgsize(resultdef));
        case left.location.loc of
          LOC_REFERENCE,
          LOC_CREFERENCE :
            begin
              location.register:=cg.getfpuregister(current_asmdata.CurrAsmList,location.size);
              cg.a_loadfpu_ref_reg(current_asmdata.CurrAsmList,
                 left.location.size,location.size,
                 left.location.reference,location.register);
              emit_float_sign_change(location.register,def_cgsize(left.resultdef));
            end;
          LOC_FPUREGISTER:
            begin
               location.register:=left.location.register;
               emit_float_sign_change(location.register,def_cgsize(left.resultdef));
            end;
          LOC_CFPUREGISTER:
            begin
               location.register:=cg.getfpuregister(current_asmdata.CurrAsmList,location.size);
               cg.a_loadfpu_reg_reg(current_asmdata.CurrAsmList,left.location.size,location.size,left.location.register,location.register);
               emit_float_sign_change(location.register,def_cgsize(left.resultdef));
            end;
          else
            internalerror(200306021);
        end;
      end;


    procedure tcgunaryminusnode.second_integer;
      var
        hl: tasmlabel;
        opsize: tdef;
      begin
        secondpass(left);
        { load left operator in a register }
        location_copy(location,left.location);
        { in case of a 32 bit system that can natively execute 64 bit operations }
        if (left.resultdef.size<=sinttype.size) then
          opsize:=sinttype
        else
          opsize:=s64inttype;
        hlcg.location_force_reg(current_asmdata.CurrAsmList,location,left.resultdef,opsize,false);
        hlcg.a_op_reg_reg(current_asmdata.CurrAsmList,OP_NEG,opsize,location.register,location.register);

        if (cs_check_overflow in current_settings.localswitches) then
          begin
            current_asmdata.getjumplabel(hl);
            hlcg.a_cmp_const_reg_label(current_asmdata.CurrAsmList,opsize,OC_NE,low(aint),location.register,hl);
            cg.a_call_name(current_asmdata.CurrAsmList,'FPC_OVERFLOW',false);
            hlcg.a_label(current_asmdata.CurrAsmList,hl);
          end;
      end;


    procedure tcgunaryminusnode.pass_generate_code;
      begin
{$ifndef cpu64bitalu}
         if is_64bit(left.resultdef) then
           second_64bit
         else
{$endif not cpu64bitalu}
{$ifdef SUPPORT_MMX}
           if (cs_mmx in current_settings.localswitches) and is_mmx_able_array(left.resultdef) then
             second_mmx
         else
{$endif SUPPORT_MMX}
           if (left.resultdef.typ=floatdef) then
             second_float
         else
           second_integer;
      end;


{*****************************************************************************
                             TCGMODDIVNODE
*****************************************************************************}

{$ifndef cpu64bitalu}
    procedure tcgmoddivnode.emit64_div_reg_reg(signed: boolean; denum,num:tregister64);
      begin
        { handled in pass_1 already, unless pass_1 is
          overridden
        }
        { should be handled in pass_1 (JM) }
        internalerror(200109052);
      end;
{$endif not cpu64bitalu}


    procedure tcgmoddivnode.pass_generate_code;
      var
         hreg1 : tregister;
         hdenom : tregister;
         power : longint;
         hl : tasmlabel;
         paraloc1 : tcgpara;
         opsize : tcgsize;
         opdef : tdef;
      begin
         secondpass(left);
         if codegenerror then
          exit;
         secondpass(right);
         if codegenerror then
          exit;
         location_copy(location,left.location);

{$ifndef cpu64bitalu}
         if is_64bit(resultdef) then
           begin
             if is_signed(left.resultdef) then
               opdef:=s64inttype
             else
               opdef:=u64inttype;

             { this code valid for 64-bit cpu's only ,
               otherwise helpers are called in pass_1
             }
             hlcg.location_force_reg(current_asmdata.CurrAsmList,location,left.resultdef,opdef,false);
             location_copy(location,left.location);
             hlcg.location_force_reg(current_asmdata.CurrAsmList,right.location,right.resultdef,opdef,false);
             emit64_div_reg_reg(is_signed(left.resultdef),
               joinreg64(right.location.register64.reglo,right.location.register64.reghi),
               joinreg64(location.register64.reglo,location.register64.reghi));
           end
         else
{$endif not cpu64bitalu}
           begin
              if is_signed(left.resultdef) then
                begin
                  opsize:=OS_SINT;
                  opdef:=ossinttype;
                end
              else
                begin
                  opsize:=OS_INT;
                  opdef:=osuinttype;
                end;

              { put numerator in register }
              hlcg.location_force_reg(current_asmdata.CurrAsmList,left.location,left.resultdef,opdef,false);
              hreg1:=left.location.register;

              if (nodetype=divn) and
                 (right.nodetype=ordconstn) and
                 ispowerof2(tordconstnode(right).value.svalue,power) then
                Begin
                  { for signed numbers, the numerator must be adjusted before the
                    shift instruction, but not wih unsigned numbers! Otherwise,
                    "Cardinal($ffffffff) div 16" overflows! (JM) }
                  If is_signed(left.resultdef) Then
                    Begin
                      current_asmdata.getjumplabel(hl);
                      cg.a_cmp_const_reg_label(current_asmdata.CurrAsmList,OS_INT,OC_GT,0,hreg1,hl);
                      if power=1 then
                        cg.a_op_const_reg(current_asmdata.CurrAsmList,OP_ADD,OS_INT,1,hreg1)
                      else
                        cg.a_op_const_reg(current_asmdata.CurrAsmList,OP_ADD,OS_INT,Tordconstnode(right).value.svalue-1,hreg1);
                      cg.a_label(current_asmdata.CurrAsmList,hl);
                      cg.a_op_const_reg(current_asmdata.CurrAsmList,OP_SAR,OS_INT,power,hreg1);
                    End
                  Else { not signed }
                    cg.a_op_const_reg(current_asmdata.CurrAsmList,OP_SHR,OS_INT,power,hreg1);
                End
              else
                begin
                  { bring denominator to hdenom }
                  { hdenom is always free, it's }
                  { only used for temporary }
                  { purposes                }
                  hdenom := cg.getintregister(current_asmdata.CurrAsmList,OS_INT);
                  hlcg.a_load_loc_reg(current_asmdata.CurrAsmList,right.resultdef,osuinttype,right.location,hdenom);
                  { verify if the divisor is zero, if so return an error
                    immediately
                  }
                  current_asmdata.getjumplabel(hl);
                  cg.a_cmp_const_reg_label(current_asmdata.CurrAsmList,OS_INT,OC_NE,0,hdenom,hl);
                  paraloc1.init;
                  paramanager.getintparaloc(pocall_default,1,paraloc1);
                  cg.a_load_const_cgpara(current_asmdata.CurrAsmList,OS_S32,aint(200),paraloc1);
                  paramanager.freecgpara(current_asmdata.CurrAsmList,paraloc1);
                  cg.a_call_name(current_asmdata.CurrAsmList,'FPC_HANDLEERROR',false);
                  paraloc1.done;
                  cg.a_label(current_asmdata.CurrAsmList,hl);
                  if nodetype = modn then
                    emit_mod_reg_reg(is_signed(left.resultdef),hdenom,hreg1)
                  else
                    emit_div_reg_reg(is_signed(left.resultdef),hdenom,hreg1);
                end;
              location_reset(location,LOC_REGISTER,opsize);
              location.register:=hreg1;
           end;
        cg.g_overflowcheck(current_asmdata.CurrAsmList,location,resultdef);
      end;


{*****************************************************************************
                             TCGSHLRSHRNODE
*****************************************************************************}


{$ifndef cpu64bitalu}
    procedure tcgshlshrnode.second_64bit;
      begin
         { already hanled in 1st pass }
         internalerror(2002081501);
      end;
{$endif not cpu64bitalu}


    procedure tcgshlshrnode.second_integer;
      var
         op : topcg;
         opdef : tdef;
         hcountreg : tregister;
         opsize : tcgsize;
      begin
         { determine operator }
         case nodetype of
           shln: op:=OP_SHL;
           shrn: op:=OP_SHR;
         end;
{$ifdef cpunodefaultint}
        opsize:=left.location.size;
        opdef:=left.resultdef;
{$else cpunodefaultint}
         { load left operators in a register }
         if is_signed(left.resultdef) then
           begin
             opsize:=OS_SINT;
             opdef:=ossinttype
           end
         else
           begin
             opsize:=OS_INT;
             opdef:=osuinttype;
           end;
{$endif cpunodefaultint}

         hlcg.location_force_reg(current_asmdata.CurrAsmList,left.location,left.resultdef,opdef,true);
         location_reset(location,LOC_REGISTER,opsize);
         location.register:=cg.getintregister(current_asmdata.CurrAsmList,opsize);

         { shifting by a constant directly coded: }
         if (right.nodetype=ordconstn) then
           begin
              { l shl 32 should 0 imho, but neither TP nor Delphi do it in this way (FK)
              if right.value<=31 then
              }
              cg.a_op_const_reg_reg(current_asmdata.CurrAsmList,op,location.size,
                tordconstnode(right).value.uvalue and 31,left.location.register,location.register);
              {
              else
                emit_reg_reg(A_XOR,S_L,hregister1,
                  hregister1);
              }
           end
         else
           begin
              { load right operators in a register - this
                is done since most target cpu which will use this
                node do not support a shift count in a mem. location (cec)
              }
              if right.location.loc<>LOC_REGISTER then
                begin
                  hcountreg:=cg.getintregister(current_asmdata.CurrAsmList,opsize);
                  hlcg.a_load_loc_reg(current_asmdata.CurrAsmList,right.resultdef,opdef,right.location,hcountreg);
                end
              else
                hcountreg:=right.location.register;
              cg.a_op_reg_reg_reg(current_asmdata.CurrAsmList,op,opsize,hcountreg,left.location.register,location.register);
           end;
      end;


    procedure tcgshlshrnode.pass_generate_code;
      begin
         secondpass(left);
         secondpass(right);
{$ifndef cpu64bitalu}
         if is_64bit(left.resultdef) then
           second_64bit
         else
{$endif not cpu64bitalu}
           second_integer;
      end;


{*****************************************************************************
                               TCGNOTNODE
*****************************************************************************}

{$ifndef cpu64bitalu}
    procedure tcgnotnode.second_64bit;
      begin
        secondpass(left);
        hlcg.location_force_reg(current_asmdata.CurrAsmList,left.location,left.resultdef,left.resultdef,false);
        location_copy(location,left.location);
        { perform the NOT operation }
        cg64.a_op64_reg_reg(current_asmdata.CurrAsmList,OP_NOT,location.size,left.location.register64,location.register64);
      end;
{$endif not cpu64bitalu}


    procedure tcgnotnode.second_integer;
      begin
        secondpass(left);
        hlcg.location_force_reg(current_asmdata.CurrAsmList,left.location,left.resultdef,left.resultdef,false);
        location_copy(location,left.location);
        { perform the NOT operation }
        hlcg.a_op_reg_reg(current_asmdata.CurrAsmList,OP_NOT,left.resultdef,location.register,location.register);
      end;


    procedure tcgnotnode.pass_generate_code;
      begin
        if is_boolean(resultdef) then
          second_boolean
{$ifdef SUPPORT_MMX}
        else if (cs_mmx in current_settings.localswitches) and is_mmx_able_array(left.resultdef) then
          second_mmx
{$endif SUPPORT_MMX}
{$ifndef cpu64bitalu}
        else if is_64bit(left.resultdef) then
          second_64bit
{$endif not cpu64bitalu}
        else
          second_integer;
      end;

begin
   cmoddivnode:=tcgmoddivnode;
   cunaryminusnode:=tcgunaryminusnode;
   cshlshrnode:=tcgshlshrnode;
   cnotnode:=tcgnotnode;
end.
