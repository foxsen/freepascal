{
    Copyright (c) 1999-2008 by Mazen Neifer and Florian Klaempfl

    Contains the assembler object for the AVR

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
unit aasmcpu;

{$i fpcdefs.inc}

interface

uses
  cclasses,
  globtype,globals,verbose,
  aasmbase,aasmtai,aasmdata,aasmsym,
  cgbase,cgutils,cpubase,cpuinfo,
  ogbase;

    const
      { "mov reg,reg" source operand number }
      O_MOV_SOURCE = 1;
      { "mov reg,reg" source operand number }
      O_MOV_DEST = 0;

      maxinfolen = 5;

    type
      tinsentry = record
        opcode  : tasmop;
        ops     : byte;
        optypes : array[0..3] of longint;
        code    : array[0..maxinfolen] of char;
        flags   : longint;
      end;

      pinsentry=^tinsentry;

      taicpu = class(tai_cpu_abstract_sym)
         constructor op_none(op : tasmop);

         constructor op_reg(op : tasmop;_op1 : tregister);
         constructor op_const(op : tasmop;_op1 : LongInt);
         constructor op_ref(op : tasmop;const _op1 : treference);

         constructor op_reg_reg(op : tasmop;_op1,_op2 : tregister);
         constructor op_reg_ref(op : tasmop;_op1 : tregister;const _op2 : treference);
         constructor op_reg_const(op:tasmop; _op1: tregister; _op2: LongInt);
         constructor op_const_reg(op:tasmop; _op1: LongInt; _op2: tregister);
         constructor op_ref_reg(op : tasmop;const _op1 : treference;_op2 : tregister);

         { this is for Jmp instructions }
         constructor op_cond_sym(op : tasmop;cond:TAsmCond;_op1 : tasmsymbol);
         constructor op_sym(op : tasmop;_op1 : tasmsymbol);
         constructor op_sym_ofs(op : tasmop;_op1 : tasmsymbol;_op1ofs:longint);
         procedure loadbool(opidx:longint;_b:boolean);
         { register allocation }
         function is_same_reg_move(regtype: Tregistertype):boolean; override;

         { register spilling code }
         function spilling_get_operation_type(opnr: longint): topertype;override;

         { assembler }
      public
         { the next will reset all instructions that can change in pass 2 }
         procedure ResetPass1;override;
         procedure ResetPass2;override;
{         function  CheckIfValid:boolean;
         function GetString:string; }
         function  Pass1(objdata:TObjData):longint;override;
//         procedure Pass2(objdata:TObjData);override;
         function calcsize(p:PInsEntry):shortint;
      private
         { next fields are filled in pass1, so pass2 is faster }
         inssize   : shortint;
         insoffset : longint;
         insentry  : PInsEntry;
         LastInsOffset : longint; { need to be public to be reset }
         function  FindInsentry(objdata:TObjData):boolean;
      end;

      tai_align = class(tai_align_abstract)
        { nothing to add }
      end;

    procedure InitAsm;
    procedure DoneAsm;

    function spilling_create_load(const ref:treference;r:tregister):Taicpu;
    function spilling_create_store(r:tregister; const ref:treference):Taicpu;

    function setcondition(i : taicpu;c : tasmcond) : taicpu;

    { replaces cond. branches by rjmp/jmp and the inverse cond. branch if needed
      and transforms special instructions to valid instruction encodings }
    procedure finalizeavrcode(list : TAsmList);

implementation

{*****************************************************************************
                                 taicpu Constructors
*****************************************************************************}

    procedure taicpu.loadbool(opidx:longint;_b:boolean);
      begin
        if opidx>=ops then
         ops:=opidx+1;
        with oper[opidx]^ do
         begin
           if typ=top_ref then
            dispose(ref);
           b:=_b;
           typ:=top_bool;
         end;
      end;


    constructor taicpu.op_none(op : tasmop);
      begin
         inherited create(op);
      end;


    constructor taicpu.op_reg(op : tasmop;_op1 : tregister);
      begin
         inherited create(op);
         ops:=1;
         loadreg(0,_op1);
      end;


    constructor taicpu.op_ref(op : tasmop;const _op1 : treference);
      begin
         inherited create(op);
         ops:=1;
         loadref(0,_op1);
      end;


    constructor taicpu.op_const(op : tasmop;_op1 : LongInt);
      begin
         inherited create(op);
         ops:=1;
         loadconst(0,_op1);
      end;


    constructor taicpu.op_reg_reg(op : tasmop;_op1,_op2 : tregister);
      begin
         inherited create(op);
         ops:=2;
         loadreg(0,_op1);
         loadreg(1,_op2);
      end;

    constructor taicpu.op_reg_const(op:tasmop; _op1: tregister; _op2: LongInt);
      begin
         inherited create(op);
         ops:=2;
         loadreg(0,_op1);
         loadconst(1,aint(_op2));
      end;

     constructor taicpu.op_const_reg(op:tasmop; _op1: LongInt; _op2: tregister);
      begin
         inherited create(op);
         ops:=2;
         loadconst(0,_op1);
         loadreg(1,_op2);
      end;


    constructor taicpu.op_reg_ref(op : tasmop;_op1 : tregister;const _op2 : treference);
      begin
         inherited create(op);
         ops:=2;
         loadreg(0,_op1);
         loadref(1,_op2);
      end;


    constructor taicpu.op_ref_reg(op : tasmop;const _op1 : treference;_op2 : tregister);
      begin
         inherited create(op);
         ops:=2;
         loadref(0,_op1);
         loadreg(1,_op2);
      end;


    constructor taicpu.op_cond_sym(op : tasmop;cond:TAsmCond;_op1 : tasmsymbol);
      begin
         inherited create(op);
         is_jmp:=op in jmp_instructions;
         condition:=cond;
         ops:=1;
         loadsymbol(0,_op1,0);
      end;


    constructor taicpu.op_sym(op : tasmop;_op1 : tasmsymbol);
      begin
         inherited create(op);
         is_jmp:=op in jmp_instructions;
         ops:=1;
         loadsymbol(0,_op1,0);
      end;


    constructor taicpu.op_sym_ofs(op : tasmop;_op1 : tasmsymbol;_op1ofs:longint);
      begin
         inherited create(op);
         ops:=1;
         loadsymbol(0,_op1,_op1ofs);
      end;


    function taicpu.is_same_reg_move(regtype: Tregistertype):boolean;
      begin
        result:=(
                 ((opcode in [A_MOV,A_MOVW]) and (regtype = R_INTREGISTER))
                ) and
                (ops=2) and
                (oper[0]^.typ=top_reg) and
                (oper[1]^.typ=top_reg) and
                (oper[0]^.reg=oper[1]^.reg);
      end;


    function taicpu.spilling_get_operation_type(opnr: longint): topertype;
      begin
        result:=operand_read;
        case opcode of
          A_CP,A_CPC,A_CPI,A_PUSH :
            ;
          else
            begin
              if opnr=0 then
                result:=operand_write;
            end;
        end;
      end;


    function  taicpu.calcsize(p:PInsEntry):shortint;
      begin
        case opcode of
          A_CALL,
          A_JMP:
            result:=4;
          A_LDS:
            if (getsupreg(oper[0]^.reg)>=RS_R16) and (getsupreg(oper[0]^.reg)<=RS_R31) and
              (oper[1]^.val>=0) and (oper[1]^.val<=127) then
              result:=2
            else
              result:=4;
          A_STS:
            if (getsupreg(oper[1]^.reg)>=RS_R16) and (getsupreg(oper[1]^.reg)<=RS_R31) and
              (oper[0]^.val>=0) and (oper[0]^.val<=127) then
              result:=2
            else
              result:=4;
        else
          result:=2;
        end;
      end;


    procedure taicpu.ResetPass1;
      begin
        { we need to reset everything here, because the choosen insentry
          can be invalid for a new situation where the previously optimized
          insentry is not correct }
        InsEntry:=nil;
        InsSize:=0;
        LastInsOffset:=-1;
      end;


    procedure taicpu.ResetPass2;
      begin
        { we are here in a second pass, check if the instruction can be optimized }
{
        if assigned(InsEntry) and
           ((InsEntry^.flags and IF_PASS2)<>0) then
         begin
           InsEntry:=nil;
           InsSize:=0;
         end;
}
        LastInsOffset:=-1;
      end;


    function taicpu.FindInsentry(objdata:TObjData):boolean;
      begin
        result:=false;
      end;


    function taicpu.Pass1(objdata:TObjData):longint;
      begin
        Pass1:=0;
        { Save the old offset and set the new offset }
        InsOffset:=ObjData.CurrObjSec.Size;
        InsSize:=calcsize(InsEntry);
        { Error? }
        if (Insentry=nil) and (InsSize=-1) then
          exit;
        { set the file postion }
        current_filepos:=fileinfo;

        { Get InsEntry }
        if FindInsEntry(objdata) then
         begin
           LastInsOffset:=InsOffset;
           Pass1:=InsSize;
           exit;
         end;
        LastInsOffset:=-1;
      end;


    function spilling_create_load(const ref:treference;r:tregister):Taicpu;
      begin
        case getregtype(r) of
          R_INTREGISTER :
            if ref.offset<>0 then
              result:=taicpu.op_reg_ref(A_LDD,r,ref)
            else
              result:=taicpu.op_reg_ref(A_LD,r,ref);
          R_ADDRESSREGISTER :
            if ref.offset<>0 then
              result:=taicpu.op_reg_ref(A_LDD,r,ref)
            else
              result:=taicpu.op_reg_ref(A_LD,r,ref);
          else
            internalerror(200401041);
        end;
      end;


    function spilling_create_store(r:tregister; const ref:treference):Taicpu;
      begin
        case getregtype(r) of
          R_INTREGISTER :
            if ref.offset<>0 then
              result:=taicpu.op_ref_reg(A_STD,ref,r)
            else
              result:=taicpu.op_ref_reg(A_ST,ref,r);
          R_ADDRESSREGISTER :
            if ref.offset<>0 then
              result:=taicpu.op_ref_reg(A_STD,ref,r)
            else
              result:=taicpu.op_ref_reg(A_ST,ref,r);
          else
            internalerror(200401041);
        end;
      end;


    procedure InitAsm;
      begin
      end;


    procedure DoneAsm;
      begin
      end;


    function setcondition(i : taicpu;c : tasmcond) : taicpu;
      begin
        i.condition:=c;
        result:=i;
      end;


    procedure finalizeavrcode(list : TAsmList);
      var
        CurrOffset : longint;
        curtai : tai;
        again : boolean;
        l : tasmlabel;
      begin
        again:=true;
        while again do
          begin
            again:=false;
            CurrOffset:=0;
            curtai:=tai(list.first);
            while assigned(curtai) do
              begin
                { instruction? }
                if not(curtai.typ in SkipInstr) then
                  case curtai.typ of
                    ait_instruction:
                      begin
                        taicpu(curtai).InsOffset:=CurrOffset;
                        inc(CurrOffset,taicpu(curtai).calcsize(nil));
                      end;
                    ait_align:
                      inc(CurrOffset,tai_align(curtai).aligntype);
                    ait_marker:
                      ;
                    ait_label:
                      begin
                        tai_label(curtai).labsym.offset:=CurrOffset;
                      end;
                    else
                      internalerror(2011082401);
                  end;
                curtai:=tai(curtai.next);
              end;

            curtai:=tai(list.first);
            while assigned(curtai) do
              begin
                if (curtai.typ=ait_instruction) and
                  (taicpu(curtai).opcode in [A_BRxx]) and
                  ((taicpu(curtai).InsOffset-taicpu(curtai).oper[0]^.ref^.symbol.offset>64) or
                   (taicpu(curtai).InsOffset-taicpu(curtai).oper[0]^.ref^.symbol.offset<-63)
                  ) then
                  begin
                    current_asmdata.getjumplabel(l);
                    list.insertafter(tai_label.create(l),curtai);
                    list.insertafter(taicpu.op_sym(A_JMP,taicpu(curtai).oper[0]^.ref^.symbol),curtai);
                    taicpu(curtai).oper[0]^.ref^.symbol:=l;
                    taicpu(curtai).condition:=inverse_cond(taicpu(curtai).condition);
                    again:=true;
                  end;
                curtai:=tai(curtai.next);
              end;
          end;
      end;


begin
  cai_cpu:=taicpu;
  cai_align:=tai_align;
end.
