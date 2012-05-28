{
    Copyright (c) 1998-2002 by Florian Klaempfl

    This unit implements an asmoutput class for i386 AT&T syntax

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
{ This unit implements an asmoutput class for i386 AT&T syntax
}
unit agx86att;

{$i fpcdefs.inc}

interface

    uses
      cclasses,cpubase,
      globals,cgutils,
      aasmbase,aasmtai,aasmdata,assemble,aggas;

    type
      Tx86ATTAssembler=class(TGNUassembler)
        constructor create(smart: boolean); override;
      end;

      Tx86AppleGNUAssembler=class(TAppleGNUassembler)
        constructor create(smart: boolean); override;
      end;

      Tx86AoutGNUAssembler=class(TAoutGNUassembler)
        constructor create(smart: boolean); override;
      end;


     Tx86InstrWriter=class(TCPUInstrWriter)
       private
        procedure WriteReference(var ref : treference);
        procedure WriteOper(const o:toper);
        procedure WriteOper_jmp(const o:toper);
       protected
        fskipPopcountSuffix: boolean;
       public
        procedure WriteInstruction(hp: tai);override;
     end;



  implementation

    uses
      globtype,
      cutils,systems,
      verbose,
      itcpugas,
      cgbase,
      aasmcpu;


{****************************************************************************
                            Tx86ATTAssembler
 ****************************************************************************}

    constructor Tx86ATTAssembler.create(smart: boolean);
      begin
        inherited create(smart);
        InstrWriter := Tx86InstrWriter.create(self);
      end;

{****************************************************************************
                          Tx86AppleGNUAssembler
 ****************************************************************************}

    constructor Tx86AppleGNUAssembler.create(smart: boolean);
      begin
        inherited create(smart);
        InstrWriter := Tx86InstrWriter.create(self);
        { Apple's assembler does not support a size suffix for popcount }
        Tx86InstrWriter(InstrWriter).fskipPopcountSuffix := true;
      end;

{****************************************************************************
                          Tx86AoutGNUAssembler
 ****************************************************************************}

    constructor Tx86AoutGNUAssembler.create(smart: boolean);
      begin
        inherited create(smart);
        InstrWriter := Tx86InstrWriter.create(self);
      end;

{****************************************************************************
                            Tx86InstrWriter
 ****************************************************************************}

    procedure Tx86InstrWriter.WriteReference(var ref : treference);
      begin
        with ref do
         begin
           { do we have a segment prefix ? }
           { These are probably not correctly handled under GAS }
           { should be replaced by coding the segment override  }
           { directly! - DJGPP FAQ                              }
           if segment<>NR_NO then
             owner.AsmWrite(gas_regname(segment)+':');
           if assigned(symbol) then
             owner.AsmWrite(symbol.name);
           if assigned(relsymbol) then
             owner.AsmWrite('-'+relsymbol.name);
           if ref.refaddr=addr_pic then
{$ifdef x86_64}
             begin
               { local symbols don't have to (and in case of Mac OS X: cannot)
                 be accessed via the GOT
               }
               if not assigned(ref.symbol) or
                  (ref.symbol.bind<>AB_LOCAL) then
                 owner.AsmWrite('@GOTPCREL');
             end;
{$else x86_64}
             owner.AsmWrite('@GOT');
{$endif x86_64}
           if offset<0 then
             owner.AsmWrite(tostr(offset))
           else
            if (offset>0) then
             begin
               if assigned(symbol) then
                owner.AsmWrite('+'+tostr(offset))
               else
                owner.AsmWrite(tostr(offset));
             end
           else if (index=NR_NO) and (base=NR_NO) and (not assigned(symbol)) then
             owner.AsmWrite('0');
           if (index<>NR_NO) and (base=NR_NO) then
            begin
              owner.AsmWrite('(,'+gas_regname(index));
              if scalefactor<>0 then
               owner.AsmWrite(','+tostr(scalefactor)+')')
              else
               owner.AsmWrite(')');
            end
           else
            if (index=NR_NO) and (base<>NR_NO) then
              owner.AsmWrite('('+gas_regname(base)+')')
            else
             if (index<>NR_NO) and (base<>NR_NO) then
              begin
                owner.AsmWrite('('+gas_regname(base)+','+gas_regname(index));
                if scalefactor<>0 then
                 owner.AsmWrite(','+tostr(scalefactor));
                owner.AsmWrite(')');
              end;
         end;
      end;


    procedure Tx86InstrWriter.WriteOper(const o:toper);
      begin
        case o.typ of
          top_reg :
            owner.AsmWrite(gas_regname(o.reg));
          top_ref :
            if o.ref^.refaddr in [addr_no,addr_pic,addr_pic_no_got] then
              WriteReference(o.ref^)
            else
              begin
                owner.AsmWrite('$');
                if assigned(o.ref^.symbol) then
                 owner.AsmWrite(o.ref^.symbol.name);
                if o.ref^.offset>0 then
                 owner.AsmWrite('+'+tostr(o.ref^.offset))
                else
                 if o.ref^.offset<0 then
                  owner.AsmWrite(tostr(o.ref^.offset))
                else
                 if not(assigned(o.ref^.symbol)) then
                   owner.AsmWrite('0');
              end;
          top_const :
              owner.AsmWrite('$'+tostr(o.val));
          else
            internalerror(10001);
        end;
      end;


    procedure Tx86InstrWriter.WriteOper_jmp(const o:toper);
      begin
        case o.typ of
          top_reg :
            owner.AsmWrite('*'+gas_regname(o.reg));
          top_ref :
            begin
              if o.ref^.refaddr in [addr_no,addr_pic_no_got] then
                begin
                  owner.AsmWrite('*');
                  WriteReference(o.ref^);
                end
              else
                begin
                  owner.AsmWrite(o.ref^.symbol.name);
                  if o.ref^.refaddr=addr_pic then
                    owner.AsmWrite('@PLT');
                  if o.ref^.offset>0 then
                   owner.AsmWrite('+'+tostr(o.ref^.offset))
                  else
                   if o.ref^.offset<0 then
                    owner.AsmWrite(tostr(o.ref^.offset));
                end;
            end;
          top_const :
            owner.AsmWrite(tostr(o.val));
          else
            internalerror(10001);
        end;
      end;


    procedure Tx86InstrWriter.WriteInstruction(hp: tai);
      var
       op       : tasmop;
{$ifdef x86_64}
       val      : aint;
{$endif}
       calljmp  : boolean;
       need_second_mov : boolean;
       i        : integer;
      begin
        if hp.typ <> ait_instruction then
          exit;
        taicpu(hp).SetOperandOrder(op_att);
        op:=taicpu(hp).opcode;
        calljmp:=is_calljmp(op);
        { constant values in the 32 bit range are sign-extended to
          64 bits, but this is not what we want.  PM 2010-09-02
          the fix consists of simply setting only the 4-byte register
          as the upper 4-bytes will be zeroed at the same time. }
        need_second_mov:=false;
{$ifdef x86_64}
        if (op=A_MOV) and (taicpu(hp).opsize=S_Q) and
           (taicpu(hp).oper[0]^.typ = top_const) then
           begin
             val := taicpu(hp).oper[0]^.val;
             if (val > int64($7fffffff)) and (val < int64($100000000)) then
               begin
                 owner.AsmWrite(target_asm.comment);
                 owner.AsmWritePChar('Fix for Win64-GAS bug');
                 owner.AsmLn;
                 taicpu(hp).opsize:=S_L;
                 if taicpu(hp).oper[1]^.typ = top_reg then
                   setsubreg(taicpu(hp).oper[1]^.reg,R_SUBD)
                 else if taicpu(hp).oper[1]^.typ = top_ref then
                   need_second_mov:=true
                 else
                   internalerror(20100902);
               end;
           end;
{$endif x86_64}
        owner.AsmWrite(#9);
        { movsd should not be translated to movsl when there
          are (xmm) arguments }
        if (op=A_MOVSD) and (taicpu(hp).ops>0) then
          owner.AsmWrite('movsd')
        else
          owner.AsmWrite(gas_op2str[op]);
        owner.AsmWrite(cond2str[taicpu(hp).condition]);
        { suffix needed ?  fnstsw,fldcw don't support suffixes
          with binutils 2.9.5 under linux }
{        if (Taicpu(hp).oper[0]^.typ=top_reg) and
            (Taicpu(hp).oper[0]^.reg.enum>lastreg) then
          internalerror(200301081);}

        if (not calljmp) and
           (gas_needsuffix[op]<>AttSufNONE) and
           (op<>A_FNSTSW) and
           (op<>A_FSTSW) and
           (op<>A_FNSTCW) and
           (op<>A_FSTCW) and
           (op<>A_FLDCW) and
           (not fskipPopcountSuffix or
            (op<>A_POPCNT)) and
           not(
               (taicpu(hp).ops<>0) and
               (taicpu(hp).oper[0]^.typ=top_reg) and
               (getregtype(taicpu(hp).oper[0]^.reg)=R_FPUREGISTER)
              ) then
          owner.AsmWrite(gas_opsize2str[taicpu(hp).opsize]);
        { process operands }
        if taicpu(hp).ops<>0 then
          begin
            if calljmp then
             begin
               owner.AsmWrite(#9);
               WriteOper_jmp(taicpu(hp).oper[0]^);
             end
            else
             begin
               for i:=0 to taicpu(hp).ops-1 do
                 begin
                   if i=0 then
                     owner.AsmWrite(#9)
                   else
                     owner.AsmWrite(',');
                   WriteOper(taicpu(hp).oper[i]^);
                 end;
             end;
          end;
        owner.AsmLn;
        if need_second_mov then
          begin
            taicpu(hp).oper[0]^.val:=0;
            inc(taicpu(hp).oper[1]^.ref^.offset,4);
            WriteInstruction(hp);
          end;
      end;

{*****************************************************************************
                                  Initialize
*****************************************************************************}

    const
{$ifdef x86_64}
       as_x86_64_as_info : tasminfo =
          (
            id     : as_gas;
            idtxt  : 'AS';
            asmbin : 'as';
            asmcmd : '--64 -o $OBJ $ASM';
            supported_targets : [system_x86_64_linux,system_x86_64_freebsd,
                                 system_x86_64_win64,system_x86_64_embedded,
                                 system_x86_64_openbsd,system_x86_64_netbsd];
            flags : [af_allowdirect,af_needar,af_smartlink_sections,af_supports_dwarf];
            labelprefix : '.L';
            comment : '# ';
            dollarsign: '$';
          );

       as_x86_64_gas_info : tasminfo =
          (
            id     : as_ggas;
            idtxt  : 'GAS';
            asmbin : 'gas';
            asmcmd : '--64 -o $OBJ $ASM';
            supported_targets : [system_x86_64_solaris];
            flags : [af_allowdirect,af_needar,af_smartlink_sections,af_supports_dwarf];
            labelprefix : '.L';
            comment : '# ';
            dollarsign: '$';
          );



       as_x86_64_gas_darwin_info : tasminfo =
          (
            id     : as_darwin;
            idtxt  : 'AS-Darwin';
            asmbin : 'as';
            asmcmd : '-o $OBJ $ASM -arch x86_64';
            supported_targets : [system_x86_64_darwin];
            flags : [af_allowdirect,af_needar,af_smartlink_sections,af_supports_dwarf];
            labelprefix : 'L';
            comment : '# ';
            dollarsign: '$';
          );

{$else x86_64}
       as_i386_as_info : tasminfo =
          (
            id     : as_gas;
            idtxt  : 'AS';
            asmbin : 'as';
            asmcmd : '--32 -o $OBJ $ASM';
            supported_targets : [system_i386_GO32V2,system_i386_linux,system_i386_Win32,system_i386_freebsd,system_i386_solaris,system_i386_beos,
                                system_i386_netbsd,system_i386_Netware,system_i386_qnx,system_i386_wdosx,system_i386_openbsd,
                                system_i386_netwlibc,system_i386_wince,system_i386_embedded,system_i386_symbian,system_i386_haiku,system_x86_6432_linux,
                                system_i386_nativent];
            flags : [af_allowdirect,af_needar,af_smartlink_sections,af_supports_dwarf];
            labelprefix : '.L';
            comment : '# ';
            dollarsign: '$';
          );


       as_i386_as_aout_info : tasminfo =
          (
            id           : as_i386_as_aout;
            idtxt  : 'AS_AOUT';
            asmbin : 'as';
            asmcmd : '-o $OBJ $ASM';
            supported_targets : [system_i386_linux,system_i386_OS2,system_i386_freebsd,system_i386_netbsd,system_i386_openbsd,system_i386_EMX,system_i386_embedded];
            flags : [af_allowdirect,af_needar,af_stabs_use_function_absolute_addresses];
            labelprefix : 'L';
            comment : '# ';
            dollarsign: '$';
          );


       as_i386_gas_darwin_info : tasminfo =
          (
            id     : as_darwin;
            idtxt  : 'AS-Darwin';
            asmbin : 'as';
            asmcmd : '-o $OBJ $ASM -arch i386';
            supported_targets : [system_i386_darwin,system_i386_iphonesim];
            flags : [af_allowdirect,af_needar,af_smartlink_sections,af_supports_dwarf,af_stabs_use_function_absolute_addresses];
            labelprefix : 'L';
            comment : '# ';
            dollarsign: '$';
          );

       as_i386_gas_info : tasminfo =
          (
            id     : as_ggas;
            idtxt  : 'GAS';
            asmbin : 'gas';
            asmcmd : '--32 -o $OBJ $ASM';
            supported_targets : [system_i386_GO32V2,system_i386_linux,system_i386_Win32,system_i386_freebsd,system_i386_solaris,system_i386_beos,
                                system_i386_netbsd,system_i386_Netware,system_i386_qnx,system_i386_wdosx,system_i386_openbsd,
                                system_i386_netwlibc,system_i386_wince,system_i386_embedded,system_i386_symbian,system_i386_haiku,system_x86_6432_linux];
            flags : [af_allowdirect,af_needar,af_smartlink_sections,af_supports_dwarf];
            labelprefix : '.L';
            comment : '# ';
            dollarsign: '$';
          );
{$endif x86_64}

initialization
{$ifdef x86_64}
  RegisterAssembler(as_x86_64_as_info,Tx86ATTAssembler);
  RegisterAssembler(as_x86_64_gas_info,Tx86ATTAssembler);
  RegisterAssembler(as_x86_64_gas_darwin_info,Tx86AppleGNUAssembler);
{$else x86_64}
  RegisterAssembler(as_i386_as_info,Tx86ATTAssembler);
  RegisterAssembler(as_i386_gas_info,Tx86ATTAssembler);
  RegisterAssembler(as_i386_gas_darwin_info,Tx86AppleGNUAssembler);
  RegisterAssembler(as_i386_as_aout_info,Tx86AoutGNUAssembler);
{$endif x86_64}
end.
