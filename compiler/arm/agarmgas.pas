{
    Copyright (c) 2003 by Florian Klaempfl

    This unit implements an asm for the ARM

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
{ This unit implements the GNU Assembler writer for the ARM
}

unit agarmgas;

{$i fpcdefs.inc}

  interface

    uses
       globtype,
       aasmtai,aasmdata,
       aggas,
       cpubase;

    type
      TARMGNUAssembler=class(TGNUassembler)
        constructor create(smart: boolean); override;
        function MakeCmdLine: TCmdStr; override;
        procedure WriteExtraHeader; override;
      end;

      TArmInstrWriter=class(TCPUInstrWriter)
        procedure WriteInstruction(hp : tai);override;
      end;

      TArmAppleGNUAssembler=class(TAppleGNUassembler)
        constructor create(smart: boolean); override;
      end;


    const
      gas_shiftmode2str : array[tshiftmode] of string[3] = (
        '','lsl','lsr','asr','ror','rrx');

  implementation

    uses
       cutils,globals,verbose,
       systems,
       assemble,
       cpuinfo,aasmcpu,
       itcpugas,
       cgbase,cgutils;

{****************************************************************************}
{                         GNU Arm Assembler writer                           }
{****************************************************************************}

    constructor TArmGNUAssembler.create(smart: boolean);
      begin
        inherited create(smart);
        InstrWriter := TArmInstrWriter.create(self);
      end;


    function TArmGNUAssembler.MakeCmdLine: TCmdStr;
      begin
        result:=inherited MakeCmdLine;
        if (current_settings.fputype = fpu_soft) then
          result:='-mfpu=softvfp '+result;
        if (current_settings.fputype = fpu_vfpv2) then
          result:='-mfpu=vfpv2 '+result;
        if (current_settings.fputype = fpu_vfpv3) then
          result:='-mfpu=vfpv3 '+result;
        if (current_settings.fputype = fpu_vfpv3_d16) then
          result:='-mfpu=vfpv3-d16 '+result;
        if current_settings.cputype = cpu_armv7m then
          result:='-march=armv7m -mthumb -mthumb-interwork '+result;
        if target_info.abi = abi_eabihf then
          { options based on what gcc uses on debian armhf }
          result:='-mfloat-abi=hard -meabi=5 '+result;
      end;

    procedure TArmGNUAssembler.WriteExtraHeader;
      begin
        inherited WriteExtraHeader;
        if current_settings.cputype in cpu_thumb2 then
          AsmWriteLn(#9'.syntax unified');
      end;

{****************************************************************************}
{                      GNU/Apple ARM Assembler writer                        }
{****************************************************************************}

    constructor TArmAppleGNUAssembler.create(smart: boolean);
      begin
        inherited create(smart);
        InstrWriter := TArmInstrWriter.create(self);
      end;


{****************************************************************************}
{                  Helper routines for Instruction Writer                    }
{****************************************************************************}

    function getreferencestring(var ref : treference) : string;
      var
        s : string;
      begin
         with ref do
          begin
{$ifdef extdebug}
            // if base=NR_NO then
            //   internalerror(200308292);

            // if ((index<>NR_NO) or (shiftmode<>SM_None)) and ((offset<>0) or (symbol<>nil)) then
            //   internalerror(200308293);
{$endif extdebug}

            if assigned(symbol) then
              begin
                if (base<>NR_NO) and not(is_pc(base)) then
                  internalerror(200309011);
                s:=symbol.name;
                if offset<0 then
                  s:=s+tostr(offset)
                else if offset>0 then
                  s:=s+'+'+tostr(offset);
              end
            else
              begin
                s:='['+gas_regname(base);
                if addressmode=AM_POSTINDEXED then
                  s:=s+']';
                if index<>NR_NO then
                  begin
                     if signindex<0 then
                       s:=s+', -'
                     else
                       s:=s+', ';

                     s:=s+gas_regname(index);

                     if shiftmode<>SM_None then
                       s:=s+', '+gas_shiftmode2str[shiftmode]+' #'+tostr(shiftimm);
                  end
                else if offset<>0 then
                  s:=s+', #'+tostr(offset);

                case addressmode of
                  AM_OFFSET:
                    s:=s+']';
                  AM_PREINDEXED:
                    s:=s+']!';
                end;
              end;

          end;
        getreferencestring:=s;
      end;


    const
      shiftmode2str: array[tshiftmode] of string[3] = ('','lsl','lsr','asr','ror','rrx');

    function getopstr(const o:toper) : string;
      var
        hs : string;
        first : boolean;
        r : tsuperregister;
      begin
        case o.typ of
          top_reg:
            getopstr:=gas_regname(o.reg);
          top_shifterop:
            begin
              if (o.shifterop^.rs<>NR_NO) and (o.shifterop^.shiftimm=0) then
                getopstr:=shiftmode2str[o.shifterop^.shiftmode]+' '+gas_regname(o.shifterop^.rs)
              else if (o.shifterop^.rs=NR_NO) then
                getopstr:=shiftmode2str[o.shifterop^.shiftmode]+' #'+tostr(o.shifterop^.shiftimm)
              else internalerror(200308282);
            end;
          top_const:
            getopstr:='#'+tostr(longint(o.val));
          top_regset:
            begin
              getopstr:='{';
              first:=true;
              for r:=RS_R0 to RS_R15 do
                if r in o.regset^ then
                  begin
                    if not(first) then
                      getopstr:=getopstr+',';
                    getopstr:=getopstr+gas_regname(newreg(o.regtyp,r,o.subreg));
                    first:=false;
                  end;
              getopstr:=getopstr+'}';
            end;
          top_conditioncode:
            getopstr:=cond2str[o.cc];
          top_modeflags:
            begin
              getopstr:='';
              if mfA in o.modeflags then getopstr:=getopstr+'a';
              if mfI in o.modeflags then getopstr:=getopstr+'i';
              if mfF in o.modeflags then getopstr:=getopstr+'f';
            end;
          top_ref:
            if o.ref^.refaddr=addr_full then
              begin
                hs:=o.ref^.symbol.name;
                if o.ref^.offset>0 then
                 hs:=hs+'+'+tostr(o.ref^.offset)
                else
                 if o.ref^.offset<0 then
                  hs:=hs+tostr(o.ref^.offset);
                getopstr:=hs;
              end
            else
              getopstr:=getreferencestring(o.ref^);
          else
            internalerror(2002070604);
        end;
      end;


    Procedure TArmInstrWriter.WriteInstruction(hp : tai);
    var op: TAsmOp;
        postfix,s: string;
        i: byte;
        sep: string[3];
    begin
      op:=taicpu(hp).opcode;
      if current_settings.cputype in cpu_thumb2 then
        begin
          postfix:='';
          if taicpu(hp).wideformat then
            postfix:='.w';

          if taicpu(hp).ops = 0 then
            s:=#9+gas_op2str[op]+' '+cond2str[taicpu(hp).condition]+oppostfix2str[taicpu(hp).oppostfix]
          else
            s:=#9+gas_op2str[op]+oppostfix2str[taicpu(hp).oppostfix]+postfix+cond2str[taicpu(hp).condition]; // Conditional infixes are deprecated in unified syntax
        end
      else
        s:=#9+gas_op2str[op]+cond2str[taicpu(hp).condition]+oppostfix2str[taicpu(hp).oppostfix];
      if taicpu(hp).ops<>0 then
        begin
          sep:=#9;
          for i:=0 to taicpu(hp).ops-1 do
            begin
               // debug code
               // writeln(s);
               // writeln(taicpu(hp).fileinfo.line);

               { LDM and STM use references as first operand but they are written like a register }
               if (i=0) and (op in [A_LDM,A_STM,A_FSTM,A_FLDM]) then
                 begin
                   case taicpu(hp).oper[0]^.typ of
                     top_ref:
                       begin
                         s:=s+sep+gas_regname(taicpu(hp).oper[0]^.ref^.index);
                         if taicpu(hp).oper[0]^.ref^.addressmode=AM_PREINDEXED then
                           s:=s+'!';
                       end;
                     top_reg:
                       s:=s+sep+gas_regname(taicpu(hp).oper[0]^.reg);
                     else
                       internalerror(200311292);
                   end;
                 end
               { register count of SFM and LFM is written without # }
               else if (i=1) and (op in [A_SFM,A_LFM]) then
                 begin
                   case taicpu(hp).oper[1]^.typ of
                     top_const:
                       s:=s+sep+tostr(taicpu(hp).oper[1]^.val);
                     else
                       internalerror(200311292);
                   end;
                 end
               else
                 s:=s+sep+getopstr(taicpu(hp).oper[i]^);

               sep:=',';
            end;
        end;
      owner.AsmWriteLn(s);
    end;


    const
       as_arm_gas_info : tasminfo =
          (
            id     : as_gas;

            idtxt  : 'AS';
            asmbin : 'as';
            asmcmd : '-o $OBJ $ASM';
            supported_targets : [system_arm_linux,system_arm_wince,system_arm_gba,system_arm_palmos,system_arm_nds,system_arm_embedded,system_arm_symbian];
            flags : [af_allowdirect,af_needar,af_smartlink_sections];
            labelprefix : '.L';
            comment : '# ';
            dollarsign: '$';
          );

       as_arm_gas_darwin_info : tasminfo =
          (
            id     : as_darwin;
            idtxt  : 'AS-Darwin';
            asmbin : 'as';
            asmcmd : '-o $OBJ $ASM -arch $ARCH';
            supported_targets : [system_arm_darwin];
            flags : [af_allowdirect,af_needar,af_smartlink_sections,af_supports_dwarf,af_stabs_use_function_absolute_addresses];
            labelprefix : 'L';
            comment : '# ';
            dollarsign: '$';
          );


begin
  RegisterAssembler(as_arm_gas_info,TARMGNUAssembler);
  RegisterAssembler(as_arm_gas_darwin_info,TArmAppleGNUAssembler);
end.
