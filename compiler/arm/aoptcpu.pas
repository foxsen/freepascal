{
    Copyright (c) 1998-2002 by Jonas Maebe, member of the Free Pascal
    Development Team

    This unit implements the ARM optimizer object

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


Unit aoptcpu;

{$i fpcdefs.inc}

Interface

uses cgbase, cpubase, aasmtai, aopt, aoptcpub, aoptobj;

Type

  { TCpuAsmOptimizer }

  TCpuAsmOptimizer = class(TAsmOptimizer)
    { uses the same constructor as TAopObj }
    function PeepHoleOptPass1Cpu(var p: tai): boolean; override;
    procedure PeepHoleOptPass2;override;
    Function RegInInstruction(Reg: TRegister; p1: tai): Boolean;override;
    procedure RemoveSuperfluousMove(const p: tai; movp: tai; const optimizer: string);
    function RegUsedAfterInstruction(reg: Tregister; p: tai;
                                     var AllUsedRegs: TAllUsedRegs): Boolean;
  End;

  TCpuPreRegallocScheduler = class(TAsmOptimizer)
    function PeepHoleOptPass1Cpu(var p: tai): boolean;override;
  end;

  TCpuThumb2AsmOptimizer = class(TCpuAsmOptimizer)
    { uses the same constructor as TAopObj }
    procedure PeepHoleOptPass2;override;
  End;

Implementation

  uses
    cutils,
    verbose,
    cgutils,
    aasmbase,aasmdata,aasmcpu;

  function CanBeCond(p : tai) : boolean;
    begin
      result:=
        (p.typ=ait_instruction) and
        (taicpu(p).condition=C_None) and
        ((taicpu(p).opcode<>A_BLX) or
         (taicpu(p).oper[0]^.typ=top_reg));
    end;


  function RefsEqual(const r1, r2: treference): boolean;
    begin
      refsequal :=
        (r1.offset = r2.offset) and
        (r1.base = r2.base) and
        (r1.index = r2.index) and (r1.scalefactor = r2.scalefactor) and
        (r1.symbol=r2.symbol) and (r1.refaddr = r2.refaddr) and
        (r1.relsymbol = r2.relsymbol) and
        (r1.signindex = r2.signindex) and
        (r1.shiftimm = r2.shiftimm) and
        (r1.addressmode = r2.addressmode) and
        (r1.shiftmode = r2.shiftmode);
    end;

  function MatchInstruction(const instr: tai; const op: TAsmOp; const cond: TAsmConds; const postfix: TOpPostfixes): boolean;
  begin
    result :=
      (instr.typ = ait_instruction) and
      (taicpu(instr).opcode = op) and
      ((cond = []) or (taicpu(instr).condition in cond)) and
      ((postfix = []) or (taicpu(instr).oppostfix in postfix));
  end;

  function MatchOperand(const oper1: TOper; const oper2: TOper): boolean; inline;
    begin
      result := (oper1.typ = oper2.typ) and
                (
                  ((oper1.typ = top_const) and (oper1.val = oper2.val)) or
                  ((oper1.typ = top_reg) and (oper1.reg = oper2.reg)) or
                  ((oper1.typ = top_conditioncode) and (oper1.cc = oper2.cc))
                );
    end;

  function MatchOperand(const oper: TOper; const reg: TRegister): boolean; inline;
    begin
      result := (oper.typ = top_reg) and (oper.reg = reg);
    end;

  procedure RemoveRedundantMove(const cmpp: tai; movp: tai; asml: TAsmList);
    begin
      if (taicpu(movp).condition = C_EQ) and
         (taicpu(cmpp).oper[0]^.reg = taicpu(movp).oper[0]^.reg) and
         (taicpu(cmpp).oper[1]^.val = taicpu(movp).oper[1]^.val) then
      begin
        asml.insertafter(tai_comment.Create(strpnew('Peephole CmpMovMov - Removed redundant moveq')), movp);
        asml.remove(movp);
        movp.free;
      end;
    end;

  function regLoadedWithNewValue(reg: tregister; hp: tai): boolean;
  var
    p: taicpu;
  begin
    p := taicpu(hp);
    regLoadedWithNewValue := false;
    if not ((assigned(hp)) and (hp.typ = ait_instruction)) then
      exit;

    {These are not writing to their first oper}
    if p.opcode in [A_STR, A_STRB, A_STRH, A_CMP, A_CMN, A_TST, A_TEQ,
                        A_B, A_BL, A_BX, A_BLX] then
      exit;

    { These four are writing into the first 2 register, UMLAL and SMLAL will also read from them }
    if (p.opcode in [A_UMLAL, A_UMULL, A_SMLAL, A_SMULL]) and
       (p.oper[1]^.typ = top_reg) and
       (p.oper[1]^.reg = reg) then
    begin
      regLoadedWithNewValue := true;
      exit
    end;

    {All other instructions use oper[0] as destination}
    regLoadedWithNewValue :=
      (p.oper[0]^.typ = top_reg) and
      (p.oper[0]^.reg = reg);
  end;

  function instructionLoadsFromReg(const reg: TRegister; const hp: tai): boolean;
  var
    p: taicpu;
    i: longint;
  begin
    instructionLoadsFromReg := false;
    if not (assigned(hp) and (hp.typ = ait_instruction)) then
      exit;
    p:=taicpu(hp);

    i:=1;
    {For these instructions we have to start on oper[0]}
    if (p.opcode in [A_STR, A_STRB, A_STRH, A_CMP, A_CMN, A_TST, A_TEQ,
                        A_B, A_BL, A_BX, A_BLX,
                        A_SMLAL, A_UMLAL]) then i:=0;

    while(i<p.ops) do
      begin
        case p.oper[I]^.typ of
          top_reg:
            instructionLoadsFromReg := p.oper[I]^.reg = reg;
          top_regset:
            instructionLoadsFromReg := (getsupreg(reg) in p.oper[I]^.regset^);
          top_shifterop:
            instructionLoadsFromReg := p.oper[I]^.shifterop^.rs = reg;
          top_ref:
            instructionLoadsFromReg :=
              (p.oper[I]^.ref^.base = reg) or
              (p.oper[I]^.ref^.index = reg);
        end;
        if instructionLoadsFromReg then exit; {Bailout if we found something}
        Inc(I);
      end;
  end;

  function TCpuAsmOptimizer.RegUsedAfterInstruction(reg: Tregister; p: tai;
    var AllUsedRegs: TAllUsedRegs): Boolean;
    begin
      AllUsedRegs[getregtype(reg)].Update(tai(p.Next));
      RegUsedAfterInstruction :=
        (AllUsedRegs[getregtype(reg)].IsUsed(reg)) and
           (not(getNextInstruction(p,p)) or
            instructionLoadsFromReg(reg,p) or
            not(regLoadedWithNewValue(reg,p)));
    end;

  procedure TCpuAsmOptimizer.RemoveSuperfluousMove(const p: tai; movp: tai; const optimizer: string);
    var
      TmpUsedRegs: TAllUsedRegs;
    begin
      if MatchInstruction(movp, A_MOV, [taicpu(p).condition], [PF_None]) and
         (taicpu(movp).ops=2) and {We can't optimize if there is a shiftop}
         MatchOperand(taicpu(movp).oper[1]^, taicpu(p).oper[0]^.reg) and
         {There is a special requirement for MUL and MLA, oper[0] and oper[1] are not allowed to be the same}
         not (
           (taicpu(p).opcode in [A_MLA, A_MUL]) and
           (taicpu(p).oper[1]^.reg = taicpu(movp).oper[0]^.reg)
         ) then
        begin
          CopyUsedRegs(TmpUsedRegs);
          UpdateUsedRegs(TmpUsedRegs, tai(p.next));
          if not(RegUsedAfterInstruction(taicpu(p).oper[0]^.reg,movp,TmpUsedRegs)) then
            begin
              asml.insertbefore(tai_comment.Create(strpnew('Peephole '+optimizer+' removed superfluous mov')), movp);
              taicpu(p).loadreg(0,taicpu(movp).oper[0]^.reg);
              asml.remove(movp);
              movp.free;
            end;
          ReleaseUsedRegs(TmpUsedRegs);
        end;
    end;

  function TCpuAsmOptimizer.PeepHoleOptPass1Cpu(var p: tai): boolean;
    var
      hp1,hp2: tai;
      i: longint;
      TmpUsedRegs: TAllUsedRegs;
    begin
      result := false;
      case p.typ of
        ait_instruction:
          begin
            (* optimization proved not to be safe, see tw4768.pp
            {
              change
              <op> reg,x,y
              cmp reg,#0
              into
              <op>s reg,x,y
            }
            { this optimization can applied only to the currently enabled operations because
              the other operations do not update all flags and FPC does not track flag usage }
            if (taicpu(p).opcode in [A_ADC,A_ADD,A_SUB {A_UDIV,A_SDIV,A_MUL,A_MVN,A_MOV,A_ORR,A_EOR,A_AND}]) and
              (taicpu(p).oppostfix = PF_None) and
              (taicpu(p).condition = C_None) and
              GetNextInstruction(p, hp1) and
              MatchInstruction(hp1, A_CMP, [C_None], [PF_None]) and
              (taicpu(hp1).oper[1]^.typ = top_const) and
              (taicpu(p).oper[0]^.reg = taicpu(hp1).oper[0]^.reg) and
              (taicpu(hp1).oper[1]^.val = 0) { and
              GetNextInstruction(hp1, hp2) and
              (tai(hp2).typ = ait_instruction) and
              // be careful here, following instructions could use other flags
              // however after a jump fpc never depends on the value of flags
              (taicpu(hp2).opcode = A_B) and
              (taicpu(hp2).condition in [C_EQ,C_NE,C_MI,C_PL])} then
             begin
               taicpu(p).oppostfix:=PF_S;
               asml.remove(hp1);
               hp1.free;
             end
           else
           *)
              case taicpu(p).opcode of
                A_STR {,
                A_STRH,
                A_STRB }:
                  begin
                    { change
                      str reg1,ref
                      ldr reg2,ref
                      into
                      str reg1,ref
                      mov reg2,reg1
                    }
                    if (taicpu(p).oper[1]^.ref^.addressmode=AM_OFFSET) and
                       (taicpu(p).oppostfix=PF_None) and
                       GetNextInstruction(p,hp1) and
                       (
                         ( (taicpu(p).opcode = A_STR) and
                            MatchInstruction(hp1, A_LDR, [taicpu(p).condition, C_None], [PF_None])
                         ) or
                         ( (taicpu(p).opcode = A_STRH) and
                            MatchInstruction(hp1, A_LDRH, [taicpu(p).condition, C_None], [PF_None])
                         ) or
                         ( (taicpu(p).opcode = A_STRB) and
                            MatchInstruction(hp1, A_LDRB, [taicpu(p).condition, C_None], [PF_None])
                         )
                       ) and
                       RefsEqual(taicpu(p).oper[1]^.ref^,taicpu(hp1).oper[1]^.ref^) and
                       (taicpu(hp1).oper[1]^.ref^.addressmode=AM_OFFSET) then
                      begin
                        if taicpu(hp1).oper[0]^.reg=taicpu(p).oper[0]^.reg then
                          begin
                            asml.remove(hp1);
                            hp1.free;
                          end
                        else
                          begin
                            asml.insertbefore(tai_comment.Create(strpnew('Peephole StrLdr2StrMov done')), hp1);
                            taicpu(hp1).opcode:=A_MOV;
                            taicpu(hp1).oppostfix:=PF_None;
                            taicpu(hp1).loadreg(1,taicpu(p).oper[0]^.reg);
                          end;
                        result := true;
                      end;
                  end;
                A_LDR,
                A_LDRH,
                A_LDRB,
                A_LDRSH,
                A_LDRSB:
                  begin
                    { change
                      ldr reg1,ref
                      ldr reg2,ref
                      into
                      ldr reg1,ref
                      mov reg2,reg1
                    }
                    if (taicpu(p).oper[1]^.ref^.addressmode=AM_OFFSET) and
                       GetNextInstruction(p,hp1) and
                       MatchInstruction(hp1, taicpu(p).opcode, [taicpu(p).condition, C_None], [PF_None]) and
                       RefsEqual(taicpu(p).oper[1]^.ref^,taicpu(hp1).oper[1]^.ref^) and
                       (taicpu(p).oper[0]^.reg<>taicpu(hp1).oper[1]^.ref^.index) and
                       (taicpu(p).oper[0]^.reg<>taicpu(hp1).oper[1]^.ref^.base) and
                       (taicpu(hp1).oper[1]^.ref^.addressmode=AM_OFFSET) then
                      begin
                        if taicpu(hp1).oper[0]^.reg=taicpu(p).oper[0]^.reg then
                          begin
                            asml.insertbefore(tai_comment.Create(strpnew('Peephole LdrLdr2Ldr done')), hp1);
                            asml.remove(hp1);
                            hp1.free;
                          end
                        else
                          begin
                            asml.insertbefore(tai_comment.Create(strpnew('Peephole LdrLdr2LdrMov done')), hp1);
                            taicpu(hp1).opcode:=A_MOV;
                            taicpu(hp1).oppostfix:=PF_None;
                            taicpu(hp1).loadreg(1,taicpu(p).oper[0]^.reg);
                          end;
                        result := true;
                      end;
                    { Remove superfluous mov after ldr
                      changes
                      ldr reg1, ref
                      mov reg2, reg1
                      to
                      ldr reg2, ref

                      conditions are:
                        * reg1 must be released after mov
                        * mov can not contain shifterops
                        * ldr+mov have the same conditions
                        * mov does not set flags
                    }
                    if GetNextInstruction(p, hp1) then
                      RemoveSuperfluousMove(p, hp1, 'LdrMov2Ldr');
                  end;
                A_MOV:
                  begin
                    { fold
                      mov reg1,reg0, shift imm1
                      mov reg1,reg1, shift imm2
                      to
                      mov reg1,reg0, shift imm1+imm2
                    }
                    if (taicpu(p).ops=3) and
                       (taicpu(p).oper[2]^.typ = top_shifterop) and
                       (taicpu(p).oper[2]^.shifterop^.rs = NR_NO) and
                       getnextinstruction(p,hp1) and
                       MatchInstruction(hp1, A_MOV, [taicpu(p).condition], [PF_None]) and
                       (taicpu(hp1).ops=3) and
                       MatchOperand(taicpu(hp1).oper[0]^, taicpu(p).oper[0]^.reg) and
                       MatchOperand(taicpu(hp1).oper[1]^, taicpu(p).oper[0]^.reg) and
                       (taicpu(hp1).oper[2]^.typ = top_shifterop) and
                       (taicpu(hp1).oper[2]^.shifterop^.rs = NR_NO) then
                      begin
                        { fold
                          mov reg1,reg0, lsl 16
                          mov reg1,reg1, lsr 16
                          strh reg1, ...
                          dealloc reg1
                          to
                          strh reg1, ...
                          dealloc reg1
                        }
                        if (taicpu(p).oper[2]^.shifterop^.shiftmode=SM_LSL) and
                          (taicpu(p).oper[2]^.shifterop^.shiftimm=16) and
                          (taicpu(hp1).oper[2]^.shifterop^.shiftmode=SM_LSR) and
                          (taicpu(hp1).oper[2]^.shifterop^.shiftimm=16) and
                          getnextinstruction(hp1,hp2) and
                          MatchInstruction(hp2, A_STR, [taicpu(p).condition], [PF_H]) and
                          MatchOperand(taicpu(hp2).oper[0]^, taicpu(p).oper[0]^.reg) then
                          begin
                            CopyUsedRegs(TmpUsedRegs);
                            UpdateUsedRegs(TmpUsedRegs, tai(p.next));
                            UpdateUsedRegs(TmpUsedRegs, tai(hp1.next));
                            if not(RegUsedAfterInstruction(taicpu(p).oper[0]^.reg,hp2,TmpUsedRegs)) then
                              begin
                                asml.insertbefore(tai_comment.Create(strpnew('Peephole optimizer removed superfluous 16 Bit zero extension')), hp1);
                                taicpu(hp2).loadreg(0,taicpu(p).oper[1]^.reg);
                                asml.remove(p);
                                asml.remove(hp1);
                                p.free;
                                hp1.free;
                                p:=hp2;
                              end;
                            ReleaseUsedRegs(TmpUsedRegs);
                          end
                        { fold
                          mov reg1,reg0, shift imm1
                          mov reg1,reg1, shift imm2
                          to
                          mov reg1,reg0, shift imm1+imm2
                        }
                        else if (taicpu(p).oper[2]^.shifterop^.shiftmode=taicpu(hp1).oper[2]^.shifterop^.shiftmode) then
                          begin
                            inc(taicpu(p).oper[2]^.shifterop^.shiftimm,taicpu(hp1).oper[2]^.shifterop^.shiftimm);
                            { avoid overflows }
                            if taicpu(p).oper[2]^.shifterop^.shiftimm>31 then
                              case taicpu(p).oper[2]^.shifterop^.shiftmode of
                                SM_ROR:
                                  taicpu(p).oper[2]^.shifterop^.shiftimm:=taicpu(p).oper[2]^.shifterop^.shiftimm and 31;
                                SM_ASR:
                                  taicpu(p).oper[2]^.shifterop^.shiftimm:=31;
                                SM_LSR,
                                SM_LSL:
                                  begin
                                    hp1:=taicpu.op_reg_const(A_MOV,taicpu(p).oper[0]^.reg,0);
                                    InsertLLItem(p.previous, p.next, hp1);
                                    p.free;
                                    p:=hp1;
                                  end;
                                else
                                  internalerror(2008072803);
                              end;
                            asml.insertbefore(tai_comment.Create(strpnew('Peephole ShiftShift2Shift done')), p);
                            asml.remove(hp1);
                            hp1.free;
                            result := true;
                          end;
                      end;
                    { 
                      This changes the very common 
                      mov r0, #0
                      str r0, [...]
                      mov r0, #0
                      str r0, [...]

                      and removes all superfluous mov instructions
                    }
                    if (taicpu(p).ops = 2) and
                       (taicpu(p).oper[1]^.typ = top_const) and
                       GetNextInstruction(p,hp1) then
                      begin
                        while (tai(p).typ = ait_instruction) and
                              (taicpu(p).opcode in [A_STR, A_STRH, A_STRB]) and
                              MatchOperand(taicpu(hp1).oper[0]^, taicpu(p).oper[0]^) and
                              GetNextInstruction(hp1, hp2) and
                              MatchInstruction(hp2, A_MOV, [taicpu(p).condition], [taicpu(p).oppostfix]) and
                              (taicpu(hp2).ops = 2) and
                              MatchOperand(taicpu(hp2).oper[0]^, taicpu(p).oper[0]^) and
                              MatchOperand(taicpu(hp2).oper[1]^, taicpu(p).oper[1]^) do
                          begin
                            asml.insertbefore(tai_comment.Create(strpnew('Peephole MovStrMov done')), hp2);
                            GetNextInstruction(hp2,hp1);
                            asml.remove(hp2);
                            hp2.free;
                            if not assigned(hp1) then break;
                          end;
                      end;
                    {
                      change
                      mov r1, r0
                      add r1, r1, #1
                      to
                      add r1, r0, #1

                      Todo: Make it work for mov+cmp too
                    }
                    if (taicpu(p).ops = 2) and
                       (taicpu(p).oper[1]^.typ = top_reg) and
                       (taicpu(p).oppostfix = PF_NONE) and
                       GetNextInstruction(p, hp1) and
                       (tai(hp1).typ = ait_instruction) and
                       (taicpu(hp1).opcode in [A_ADD, A_ADC, A_RSB, A_RSC, A_SUB, A_SBC,
                                               A_AND, A_BIC, A_EOR, A_ORR]) and
                       (taicpu(hp1).condition in [C_NONE, taicpu(hp1).condition]) and
                       MatchOperand(taicpu(p).oper[0]^, taicpu(hp1).oper[0]^.reg) and
                       (taicpu(hp1).oper[1]^.typ = top_reg) and
                       (taicpu(hp1).oper[2]^.typ in [top_reg, top_const]) then
                      begin
                      { When we get here we still don't know if the registers match}
                        for I:=1 to 2 do
                          {
                            If the first loop was successful p will be replaced with hp1.
                            The checks will still be ok, because all required information
                            will also be in hp1 then.
                          }
                          if MatchOperand(taicpu(p).oper[0]^, taicpu(hp1).oper[I]^.reg) then
                            begin
                              asml.insertbefore(tai_comment.Create(strpnew('Peephole RedundantMovProcess done ')), hp1);
                              taicpu(hp1).oper[I]^.reg := taicpu(p).oper[1]^.reg;
                              if p<>hp1 then
                              begin
                                asml.remove(p);
                                p.free;
                                p:=hp1;
                              end;
                            end;
                      end;
                    {
                      Often we see shifts and then a superfluous mov to another register
                      In the future this might be handled in RedundantMovProcess when it uses RegisterTracking
                    }
                    if GetNextInstruction(p, hp1) then
                      RemoveSuperfluousMove(p, hp1, 'MovMov2Mov');
                  end;
                A_ADD,
                A_ADC,
                A_RSB,
                A_RSC,
                A_SUB,
                A_SBC,
                A_AND,
                A_BIC,
                A_EOR,
                A_ORR,
                A_MLA,
                A_MUL:
                  begin
                    {
                      change
                      and reg2,reg1,const1
                      and reg2,reg2,const2
                      to
                      and reg2,reg1,(const1 and const2)
                    }
                    if (taicpu(p).opcode = A_AND) and
                       (taicpu(p).oper[1]^.typ = top_reg) and
                       (taicpu(p).oper[2]^.typ = top_const) and
                       GetNextInstruction(p, hp1) and
                       MatchInstruction(hp1, A_AND, [taicpu(p).condition], [PF_None]) and
                       MatchOperand(taicpu(hp1).oper[0]^, taicpu(p).oper[0]^.reg) and
                       MatchOperand(taicpu(hp1).oper[1]^, taicpu(p).oper[0]^.reg) and
                       (taicpu(hp1).oper[2]^.typ = top_const) then
                      begin
                        asml.insertbefore(tai_comment.Create(strpnew('Peephole AndAnd2And done')), p);
                        taicpu(p).loadConst(2,taicpu(p).oper[2]^.val and taicpu(hp1).oper[2]^.val);
                        taicpu(p).oppostfix:=taicpu(hp1).oppostfix;
                        asml.remove(hp1);
                        hp1.free;
                      end;
                    {
                      change
                      add reg1, ...
                      mov reg2, reg1
                      to
                      add reg2, ...
                    }
                    if GetNextInstruction(p, hp1) then
                      RemoveSuperfluousMove(p, hp1, 'DataMov2Data');
                  end;
                A_CMP:
                  begin
                    {
                      change
                      cmp   reg,const1
                      moveq reg,const1
                      movne reg,const2
                      to
                      cmp   reg,const1
                      movne reg,const2
                    }
                    if (taicpu(p).oper[1]^.typ = top_const) and
                       GetNextInstruction(p, hp1) and
                       MatchInstruction(hp1, A_MOV, [C_EQ, C_NE], [PF_NONE]) and
                       (taicpu(hp1).oper[1]^.typ = top_const) and
                       GetNextInstruction(hp1, hp2) and
                       MatchInstruction(hp2, A_MOV, [C_EQ, C_NE], [PF_NONE]) and
                       (taicpu(hp1).oper[1]^.typ = top_const) then
                      begin
                        RemoveRedundantMove(p, hp1, asml);
                        RemoveRedundantMove(p, hp2, asml);
                      end;
                  end;
              end;
          end;
      end;
    end;


  { instructions modifying the CPSR can be only the last instruction }
  function MustBeLast(p : tai) : boolean;
    begin
      Result:=(p.typ=ait_instruction) and
        ((taicpu(p).opcode in [A_BL,A_BLX,A_CMP,A_CMN,A_SWI,A_TEQ,A_TST,A_CMF,A_CMFE {,A_MSR}]) or
         ((taicpu(p).ops>=1) and (taicpu(p).oper[0]^.typ=top_reg) and (taicpu(p).oper[0]^.reg=NR_PC)) or
         (taicpu(p).oppostfix=PF_S));
    end;


  procedure TCpuAsmOptimizer.PeepHoleOptPass2;
    var
      p,hp1,hp2: tai;
      l : longint;
      condition : tasmcond;
      hp3: tai;
      WasLast: boolean;
      { UsedRegs, TmpUsedRegs: TRegSet; }

    begin
      p := BlockStart;
      { UsedRegs := []; }
      while (p <> BlockEnd) Do
        begin
          { UpdateUsedRegs(UsedRegs, tai(p.next)); }
          case p.Typ Of
            Ait_Instruction:
              begin
                case taicpu(p).opcode Of
                  A_B:
                    if taicpu(p).condition<>C_None then
                      begin
                         { check for
                                Bxx   xxx
                                <several instructions>
                             xxx:
                         }
                         l:=0;
                         WasLast:=False;
                         GetNextInstruction(p, hp1);
                         while assigned(hp1) and
                           (l<=4) and
                           CanBeCond(hp1) and
                           { stop on labels }
                           not(hp1.typ=ait_label) do
                           begin
                              inc(l);
                              if MustBeLast(hp1) then
                                begin
                                  WasLast:=True;
                                  GetNextInstruction(hp1,hp1);
                                  break;
                                end
                              else
                                GetNextInstruction(hp1,hp1);
                           end;
                         if assigned(hp1) then
                           begin
                              if FindLabel(tasmlabel(taicpu(p).oper[0]^.ref^.symbol),hp1) then
                                begin
                                  if (l<=4) and (l>0) then
                                    begin
                                      condition:=inverse_cond(taicpu(p).condition);
                                      hp2:=p;
                                      GetNextInstruction(p,hp1);
                                      p:=hp1;
                                      repeat
                                        if hp1.typ=ait_instruction then
                                          taicpu(hp1).condition:=condition;
                                        if MustBeLast(hp1) then
                                          begin
                                            GetNextInstruction(hp1,hp1);
                                            break;
                                          end
                                        else
                                          GetNextInstruction(hp1,hp1);
                                      until not(assigned(hp1)) or
                                        not(CanBeCond(hp1)) or
                                        (hp1.typ=ait_label);
                                      { wait with removing else GetNextInstruction could
                                        ignore the label if it was the only usage in the
                                        jump moved away }
                                      tasmlabel(taicpu(hp2).oper[0]^.ref^.symbol).decrefs;
                                      asml.remove(hp2);
                                      hp2.free;
                                      continue;
                                    end;
                                end
                              else
                                { do not perform further optimizations if there is inctructon
                                  in block #1 which can not be optimized.
                                 }
                                if not WasLast then
                                begin
                                   { check further for
                                          Bcc   xxx
                                          <several instructions 1>
                                          B   yyy
                                  xxx:
                                          <several instructions 2>
                                  yyy:
                                   }
                                  { hp2 points to jmp yyy }
                                  hp2:=hp1;
                                  { skip hp1 to xxx }
                                  GetNextInstruction(hp1, hp1);
                                  if assigned(hp2) and
                                    assigned(hp1) and
                                    (l<=3) and
                                    (hp2.typ=ait_instruction) and
                                    (taicpu(hp2).is_jmp) and
                                    (taicpu(hp2).condition=C_None) and
                                    { real label and jump, no further references to the
                                      label are allowed }
                                    (tasmlabel(taicpu(p).oper[0]^.ref^.symbol).getrefs=2) and
                                    FindLabel(tasmlabel(taicpu(p).oper[0]^.ref^.symbol),hp1) then
                                     begin
                                       l:=0;
                                       { skip hp1 to <several moves 2> }
                                       GetNextInstruction(hp1, hp1);
                                       while assigned(hp1) and
                                         CanBeCond(hp1) do
                                         begin
                                           inc(l);
                                           GetNextInstruction(hp1, hp1);
                                         end;
                                       { hp1 points to yyy: }
                                       if assigned(hp1) and
                                         FindLabel(tasmlabel(taicpu(hp2).oper[0]^.ref^.symbol),hp1) then
                                         begin
                                            condition:=inverse_cond(taicpu(p).condition);
                                            GetNextInstruction(p,hp1);
                                            hp3:=p;
                                            p:=hp1;
                                            repeat
                                              if hp1.typ=ait_instruction then
                                                taicpu(hp1).condition:=condition;
                                              GetNextInstruction(hp1,hp1);
                                            until not(assigned(hp1)) or
                                              not(CanBeCond(hp1));
                                            { hp2 is still at jmp yyy }
                                            GetNextInstruction(hp2,hp1);
                                            { hp2 is now at xxx: }
                                            condition:=inverse_cond(condition);
                                            GetNextInstruction(hp1,hp1);
                                            { hp1 is now at <several movs 2> }
                                            repeat
                                              taicpu(hp1).condition:=condition;
                                              GetNextInstruction(hp1,hp1);
                                            until not(assigned(hp1)) or
                                              not(CanBeCond(hp1)) or
                                              (hp1.typ=ait_label);
                                            {
                                            asml.remove(hp1.next)
                                            hp1.next.free;
                                            asml.remove(hp1);
                                            hp1.free;
                                            }
                                            { remove Bcc }
                                            tasmlabel(taicpu(hp3).oper[0]^.ref^.symbol).decrefs;
                                            asml.remove(hp3);
                                            hp3.free;
                                            { remove jmp }
                                            tasmlabel(taicpu(hp2).oper[0]^.ref^.symbol).decrefs;
                                            asml.remove(hp2);
                                            hp2.free;
                                            continue;
                                         end;
                                     end;
                                end;
                           end;
                      end;
                end;
              end;
          end;
          p := tai(p.next)
        end;
    end;

  function TCpuAsmOptimizer.RegInInstruction(Reg: TRegister; p1: tai): Boolean;
    begin
      If (p1.typ = ait_instruction) and (taicpu(p1).opcode=A_BL) then
        Result:=true
      else
        Result:=inherited RegInInstruction(Reg, p1);
    end;

  const
    { set of opcode which might or do write to memory }
    { TODO : extend armins.dat to contain r/w info }
    opcode_could_mem_write = [A_B,A_BL,A_BLX,A_BKPT,A_BX,A_STR,A_STRB,A_STRBT,
                              A_STRH,A_STRT,A_STF,A_SFM,A_STM,A_FSTS,A_FSTD];

  function TCpuPreRegallocScheduler.PeepHoleOptPass1Cpu(var p: tai): boolean;
  { TODO : schedule also forward }
  { TODO : schedule distance > 1 }
    var
      hp1,hp2,hp3,hp4,hp5 : tai;
      list : TAsmList;
    begin
      result:=true;
      list:=TAsmList.Create;
      p := BlockStart;
      { UsedRegs := []; }
      while (p <> BlockEnd) Do
        begin
          if (p.typ=ait_instruction) and
            GetNextInstruction(p,hp1) and
            (hp1.typ=ait_instruction) and
            { for now we don't reschedule if the previous instruction changes potentially a memory location }
            ( (not(taicpu(p).opcode in opcode_could_mem_write) and
               not(RegModifiedByInstruction(NR_PC,p)) and
               (taicpu(hp1).opcode in [A_LDR,A_LDRB,A_LDRH,A_LDRSB,A_LDRSH])
              ) or
              ((taicpu(p).opcode in [A_STM,A_STRB,A_STRH,A_STR]) and
               (taicpu(hp1).opcode in [A_LDR,A_LDRB,A_LDRH,A_LDRSB,A_LDRSH]) and
               ((taicpu(hp1).oper[1]^.ref^.base=NR_PC) or
                (assigned(taicpu(hp1).oper[1]^.ref^.symboldata) and
                (taicpu(hp1).oper[1]^.ref^.offset=0)
                )
               ) or
               { try to prove that the memory accesses don't overlapp }
               ((taicpu(p).opcode in [A_STRB,A_STRH,A_STR]) and
                (taicpu(hp1).opcode in [A_LDR,A_LDRB,A_LDRH,A_LDRSB,A_LDRSH]) and
                (taicpu(p).oper[1]^.ref^.base=taicpu(hp1).oper[1]^.ref^.base) and
                (taicpu(p).oppostfix=PF_None) and
                (taicpu(hp1).oppostfix=PF_None) and
                (taicpu(p).oper[1]^.ref^.index=NR_NO) and
                (taicpu(hp1).oper[1]^.ref^.index=NR_NO) and
                { get operand sizes and check if the offset distance is large enough to ensure no overlapp }
                (abs(taicpu(p).oper[1]^.ref^.offset-taicpu(hp1).oper[1]^.ref^.offset)>=max(tcgsize2size[reg_cgsize(taicpu(p).oper[0]^.reg)],tcgsize2size[reg_cgsize(taicpu(hp1).oper[0]^.reg)]))
              )
            )
            ) and
            GetNextInstruction(hp1,hp2) and
            (hp2.typ=ait_instruction) and
            { loaded register used by next instruction? }
            (RegInInstruction(taicpu(hp1).oper[0]^.reg,hp2)) and
            { loaded register not used by previous instruction? }
            not(RegInInstruction(taicpu(hp1).oper[0]^.reg,p)) and
            { same condition? }
            (taicpu(p).condition=taicpu(hp1).condition) and
            { first instruction might not change the register used as base }
            ((taicpu(hp1).oper[1]^.ref^.base=NR_NO) or
             not(RegModifiedByInstruction(taicpu(hp1).oper[1]^.ref^.base,p))
            ) and
            { first instruction might not change the register used as index }
            ((taicpu(hp1).oper[1]^.ref^.index=NR_NO) or
             not(RegModifiedByInstruction(taicpu(hp1).oper[1]^.ref^.index,p))
            ) then
            begin
              hp3:=tai(p.Previous);
              hp5:=tai(p.next);
              asml.Remove(p);
              { if there is a reg. dealloc instruction associated with p, move it together with p }

              { before the instruction? }
              while assigned(hp3) and (hp3.typ<>ait_instruction) do
                begin
                  if (hp3.typ=ait_regalloc) and (tai_regalloc(hp3).ratype in [ra_dealloc]) and
                    RegInInstruction(tai_regalloc(hp3).reg,p) then
                    begin
                      hp4:=hp3;
                      hp3:=tai(hp3.Previous);
                      asml.Remove(hp4);
                      list.Concat(hp4);
                    end
                  else
                  hp3:=tai(hp3.Previous);
                end;
              list.Concat(p);
              { after the instruction? }
              while assigned(hp5) and (hp5.typ<>ait_instruction) do
                begin
                  if (hp5.typ=ait_regalloc) and (tai_regalloc(hp5).ratype in [ra_dealloc]) and
                    RegInInstruction(tai_regalloc(hp5).reg,p) then
                    begin
                      hp4:=hp5;
                      hp5:=tai(hp5.next);
                      asml.Remove(hp4);
                      list.Concat(hp4);
                    end
                  else
                  hp5:=tai(hp5.Next);
                end;

              asml.Remove(hp1);
{$ifdef DEBUG_PREREGSCHEDULER}
              asml.InsertBefore(tai_comment.Create(strpnew('Rescheduled')),hp2);
{$endif DEBUG_PREREGSCHEDULER}
              asml.InsertBefore(hp1,hp2);
              asml.InsertListBefore(hp2,list);
            end;
          p := tai(p.next)
        end;
      list.Free;
    end;


  procedure TCpuThumb2AsmOptimizer.PeepHoleOptPass2;
    begin
      { TODO: Add optimizer code }
    end;

begin
  casmoptimizer:=TCpuAsmOptimizer;
  cpreregallocscheduler:=TCpuPreRegallocScheduler;
End.
