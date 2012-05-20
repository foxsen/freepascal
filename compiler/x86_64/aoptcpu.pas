{
    Copyright (c) 1998-2004 by Jonas Maebe

    This unit calls the optimization procedures to optimize the assembler
    code for sparc

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

unit aoptcpu;

{$i fpcdefs.inc}

interface

uses cpubase, aasmtai, aopt, aoptcpub;

type
  TCpuAsmOptimizer = class(TAsmOptimizer)
    function PeepHoleOptPass1Cpu(var p: tai): boolean; override;
  end;

implementation

uses
  globtype, globals,
  cutils,
  verbose,
  cgbase, cgutils,
  aoptobj,
  aasmbase, aasmdata, aasmcpu,
  itcpugas;

function isFoldableArithOp(hp1: taicpu; reg: tregister): boolean;
begin
  isFoldableArithOp := False;
  case hp1.opcode of
    A_ADD, A_SUB, A_OR, A_XOR, A_AND, A_SHL, A_SHR, A_SAR:
      isFoldableArithOp :=
        (taicpu(hp1).oper[1]^.typ = top_reg) and
        (taicpu(hp1).oper[1]^.reg = reg) and
        ((taicpu(hp1).oper[0]^.typ = top_const) or
        ((taicpu(hp1).oper[0]^.typ = top_reg) and
        (taicpu(hp1).oper[0]^.reg<>reg)));
    A_INC, A_DEC:
      isFoldableArithOp :=
        (taicpu(hp1).oper[0]^.typ = top_reg) and
        (taicpu(hp1).oper[0]^.reg = reg);
    end;
end;

function TCpuAsmOptimizer.PeepHoleOptPass1Cpu(var p: tai): boolean;
var
  next1: tai;
  hp1, hp2: tai;
  GetNextIntruction_p : boolean;
  TmpUsedRegs : TAllUsedRegs;
begin
  Result := False;
  case p.typ of
    ait_instruction:
      begin
      case taicpu(p).opcode of
        A_AND:
          begin
          if (taicpu(p).oper[0]^.typ = top_const) and
            (taicpu(p).oper[1]^.typ = top_reg) and
            GetNextInstruction(p, hp1) and
            (tai(hp1).typ = ait_instruction) and
            (taicpu(hp1).opcode = A_AND) and
            (taicpu(hp1).oper[0]^.typ = top_const) and
            (taicpu(hp1).oper[1]^.typ = top_reg) and
            (getsupreg(taicpu(p).oper[1]^.reg) = getsupreg(
            taicpu(hp1).oper[1]^.reg)) and
            (getsubreg(taicpu(p).oper[1]^.reg)<=getsubreg(
            taicpu(hp1).oper[1]^.reg)) and
            (abs(taicpu(p).oper[0]^.val and
             taicpu(hp1).oper[0]^.val)<$80000000) then
            {change "and const1, reg; and const2, reg" to "and (const1 and const2), reg"}
            begin
              taicpu(hp1).loadConst(0, taicpu(p).oper[0]^.val and
                taicpu(hp1).oper[0]^.val);
              if (cs_asm_source in current_settings.globalswitches) then
                asml.insertbefore(tai_comment.create(strpnew('PeepHole Optimization,var1')),p);
              asml.remove(p);
              p.Free;
              p:=hp1;
            end;
(*                      else
  {change "and x, reg; jxx" to "test x, reg", if reg is deallocated before the
  jump, but only if it's a conditional jump (PFV) }
                      if (taicpu(p).oper[1]^.typ = top_reg) and
                         GetNextInstruction(p, hp1) and
                         (hp1.typ = ait_instruction) and
                         (taicpu(hp1).is_jmp) and
                         (taicpu(hp1).opcode<>A_JMP) and
                         not(getsupreg(taicpu(p).oper[1]^.reg) in UsedRegs) then
                        taicpu(p).opcode := A_TEST;*)
          end;
        A_MOV:
        { removes superfluous And's after mov's }
          begin
            if not(cs_opt_level3 in current_settings.optimizerswitches) then
              exit;
            GetNextIntruction_p:=GetNextInstruction(p, hp1);
            if (taicpu(p).oper[1]^.typ = top_reg) and
               GetNextIntruction_p and
               (tai(hp1).typ = ait_instruction) and
               (taicpu(hp1).opcode = A_AND) and
               (taicpu(hp1).oper[0]^.typ = top_const) and
               (taicpu(hp1).oper[1]^.typ = top_reg) and
               (taicpu(hp1).oper[1]^.reg = taicpu(p).oper[1]^.reg) then
              case taicpu(p).opsize Of
                S_L:
                  if (taicpu(hp1).oper[0]^.val = $ffffffff) then
                    begin
                      if (cs_asm_source in current_settings.globalswitches) then
                        asml.insertbefore(tai_comment.create(strpnew('PeepHole Optimization,var2a')),p);
                      asml.remove(hp1);
                      hp1.free;
                    end;
              end
            else if (taicpu(p).oper[1]^.typ = top_reg) and
              GetNextIntruction_p and
              (hp1.typ = ait_instruction) and
              GetNextInstruction(hp1, hp2) and
              (hp2.typ = ait_instruction) and
              (taicpu(hp2).opcode = A_MOV) and
              (taicpu(hp2).oper[0]^.typ = top_reg) and
              OpsEqual(taicpu(hp2).oper[1]^, taicpu(p).oper[0]^) and
              (IsFoldableArithOp(taicpu(hp1), taicpu(p).oper[1]^.reg) or
               ((taicpu(p).opsize=S_L) and (taicpu(hp1).opsize=S_Q) and
                IsFoldableArithOp(taicpu(hp1), newreg(R_INTREGISTER,getsupreg(taicpu(p).oper[1]^.reg),R_SUBQ)))
              ) then
              { change   movsX/movzX    reg/ref, reg2             }
              {          add/sub/or/... reg3/$const, reg2         }
              {          mov            reg2 reg/ref              }
              { to       add/sub/or/... reg3/$const, reg/ref      }
              begin
                CopyUsedRegs(TmpUsedRegs);
                UpdateUsedRegs(TmpUsedRegs, tai(p.next));
                UpdateUsedRegs(TmpUsedRegs, tai(hp1.next));
                If not(RegUsedAfterInstruction(taicpu(p).oper[1]^.reg,hp2,TmpUsedRegs)) then
                  begin
                    { by example:
                        movswl  %si,%eax        movswl  %si,%eax      p
                        decl    %eax            addl    %edx,%eax     hp1
                        movw    %ax,%si         movw    %ax,%si       hp2
                      ->
                        movswl  %si,%eax        movswl  %si,%eax      p
                        decw    %eax            addw    %edx,%eax     hp1
                        movw    %ax,%si         movw    %ax,%si       hp2
                    }
                    if (cs_asm_source in current_settings.globalswitches) then
                      begin
                        asml.insertbefore(tai_comment.create(strpnew('PeepHole Optimization,var2')),p);
                        asml.insertbefore(tai_comment.create(strpnew('P='+std_op2str[taicpu(p).opcode]+gas_opsize2str[taicpu(p).opsize])),p);
                        asml.insertbefore(tai_comment.create(strpnew('HP1='+std_op2str[taicpu(hp1).opcode]+gas_opsize2str[taicpu(hp1).opsize])),p);
                        asml.insertbefore(tai_comment.create(strpnew('HP2='+std_op2str[taicpu(hp2).opcode]+gas_opsize2str[taicpu(hp2).opsize])),p);
                     end;
                    taicpu(hp1).changeopsize(taicpu(p).opsize);
                    {
                      ->
                        movswl  %si,%eax        movswl  %si,%eax      p
                        decw    %si             addw    %dx,%si       hp1
                        movw    %ax,%si         movw    %ax,%si       hp2
                    }
                    case taicpu(hp1).ops of
                      1:
                        begin
                          taicpu(hp1).loadoper(0, taicpu(hp2).oper[1]^);
                          if taicpu(hp1).oper[0]^.typ=top_reg then
                            setsubreg(taicpu(hp1).oper[0]^.reg,getsubreg(taicpu(p).oper[1]^.reg));
                        end;
                      2:
                        begin
                          taicpu(hp1).loadoper(1, taicpu(hp2).oper[1]^);
                          if (taicpu(hp1).oper[0]^.typ=top_reg) and
                            (taicpu(hp1).opcode<>A_SHL) and
                            (taicpu(hp1).opcode<>A_SHR) and
                            (taicpu(hp1).opcode<>A_SAR) then
                            setsubreg(taicpu(hp1).oper[0]^.reg,getsubreg(taicpu(p).oper[1]^.reg));
                        end;
                      else
                        internalerror(2008042701);
                    end;
                    {
                      ->
                        decw    %si             addw    %dx,%si       p
                    }
                    if (cs_asm_source in current_settings.globalswitches) then
                      asml.insertbefore(tai_comment.create(strpnew('PeepHole Optimization,var2')),p);
                    asml.remove(p);
                    asml.remove(hp2);
                    p.Free;
                    hp2.Free;
                    p := hp1;
                 end;
                ReleaseUsedRegs(TmpUsedRegs);
              end
          end;
        A_MOVSX,
        A_MOVZX:
          begin
          if (taicpu(p).oper[1]^.typ = top_reg) and
            GetNextInstruction(p, hp1) and
            (hp1.typ = ait_instruction) and
            IsFoldableArithOp(taicpu(hp1), taicpu(p).oper[1]^.reg) and
            GetNextInstruction(hp1, hp2) and
            (hp2.typ = ait_instruction) and
            (taicpu(hp2).opcode = A_MOV) and
            (taicpu(hp2).oper[0]^.typ = top_reg) and
            OpsEqual(taicpu(hp2).oper[1]^, taicpu(p).oper[0]^) then
            { change   movsX/movzX    reg/ref, reg2             }
            {          add/sub/or/... reg3/$const, reg2         }
            {          mov            reg2 reg/ref              }
            { to       add/sub/or/... reg3/$const, reg/ref      }
            begin
              { by example:
                  movswl  %si,%eax        movswl  %si,%eax      p
                  decl    %eax            addl    %edx,%eax     hp1
                  movw    %ax,%si         movw    %ax,%si       hp2
                ->
                  movswl  %si,%eax        movswl  %si,%eax      p
                  decw    %eax            addw    %edx,%eax     hp1
                  movw    %ax,%si         movw    %ax,%si       hp2
              }
              taicpu(hp1).changeopsize(taicpu(hp2).opsize);
              {
                ->
                  movswl  %si,%eax        movswl  %si,%eax      p
                  decw    %si             addw    %dx,%si       hp1
                  movw    %ax,%si         movw    %ax,%si       hp2
              }
              case taicpu(hp1).ops of
                1:
                  taicpu(hp1).loadoper(0, taicpu(hp2).oper[1]^);
                2:
                  begin
                    taicpu(hp1).loadoper(1, taicpu(hp2).oper[1]^);
                    if (taicpu(hp1).oper[0]^.typ = top_reg) then
                      setsubreg(taicpu(hp1).oper[0]^.reg,
                        getsubreg(taicpu(hp2).oper[0]^.reg));
                  end;
                else
                  internalerror(2008042701);
              end;
              {
                ->
                  decw    %si             addw    %dx,%si       p
              }
              if (cs_asm_source in current_settings.globalswitches) then
                asml.insertbefore(tai_comment.create(strpnew('PeepHole Optimization,var3')),p);
              asml.remove(p);
              asml.remove(hp2);
              p.Free;
              hp2.Free;
              p := hp1;
            end
          { removes superfluous And's after movzx's }
          else if taicpu(p).opcode = A_MOVZX then
            begin
            if (taicpu(p).oper[1]^.typ = top_reg) and
              GetNextInstruction(p, hp1) and
              (tai(hp1).typ = ait_instruction) and
              (taicpu(hp1).opcode = A_AND) and
              (taicpu(hp1).oper[0]^.typ = top_const) and
              (taicpu(hp1).oper[1]^.typ = top_reg) and
              (taicpu(hp1).oper[1]^.reg = taicpu(p).oper[1]^.reg) then
                begin
                  case taicpu(p).opsize of
                    S_BL, S_BW, S_BQ:
                      if (taicpu(hp1).oper[0]^.val = $ff) then
                        begin
                          if (cs_asm_source in current_settings.globalswitches) then
                            asml.insertbefore(tai_comment.create(strpnew('PeepHole Optimization,var4')),p);
                          asml.remove(hp1);
                          hp1.Free;
                        end;
                    S_WL, S_WQ:
                      if (taicpu(hp1).oper[0]^.val = $ffff) then
                        begin
                          if (cs_asm_source in current_settings.globalswitches) then
                            asml.insertbefore(tai_comment.create(strpnew('PeepHole Optimization,var5')),p);
                          asml.remove(hp1);
                          hp1.Free;
                        end;
                    S_LQ:
                      if (taicpu(hp1).oper[0]^.val = $ffffffff) then
                        begin
                          if (cs_asm_source in current_settings.globalswitches) then
                            asml.insertbefore(tai_comment.create(strpnew('PeepHole Optimization,var6')),p);
                          asml.remove(hp1);
                          hp1.Free;
                        end;
                    end;
               end;
            { changes some movzx constructs to faster synonims (all examples
              are given with eax/ax, but are also valid for other registers)}
            if (taicpu(p).oper[1]^.typ = top_reg) then
              if (taicpu(p).oper[0]^.typ = top_reg) then
                case taicpu(p).opsize of
                  S_BW:
                    begin
                    if (getsupreg(taicpu(p).oper[0]^.reg) =
                      getsupreg(taicpu(p).oper[1]^.reg)) and  not
                      (cs_opt_size in current_settings.optimizerswitches) then
                      {Change "movzbw %al, %ax" to "andw $0x0ffh, %ax"}
                      begin
                      taicpu(p).opcode := A_AND;
                      taicpu(p).changeopsize(S_W);
                      taicpu(p).loadConst(0, $ff);
                      if (cs_asm_source in current_settings.globalswitches) then
                        asml.insertbefore(tai_comment.create(strpnew('PeepHole Optimization,var7')),p);
                      end
                    else if GetNextInstruction(p, hp1) and
                      (tai(hp1).typ = ait_instruction) and
                      (taicpu(hp1).opcode = A_AND) and
                      (taicpu(hp1).oper[0]^.typ = top_const) and
                      (taicpu(hp1).oper[1]^.typ = top_reg) and
                      (taicpu(hp1).oper[1]^.reg =
                      taicpu(p).oper[1]^.reg) then
                      { Change "movzbw %reg1, %reg2; andw $const, %reg2"
                        to "movw %reg1, reg2; andw $(const1 and $ff), %reg2"}
                      begin
                        if (cs_asm_source in current_settings.globalswitches) then
                          asml.insertbefore(tai_comment.create(strpnew('PeepHole Optimization,var8')),p);
                        taicpu(p).opcode := A_MOV;
                        taicpu(p).changeopsize(S_W);
                        setsubreg(taicpu(p).oper[0]^.reg, R_SUBW);
                        taicpu(hp1).loadConst(
                          0, taicpu(hp1).oper[0]^.val and $ff);
                      end;
                    end;
                  S_BL:
                    begin
                    if (getsupreg(taicpu(p).oper[0]^.reg) =
                      getsupreg(taicpu(p).oper[1]^.reg)) and not
                      (cs_opt_size in current_settings.optimizerswitches) then
                      { Change "movzbl %al, %eax" to "andl $0x0ffh, %eax"}
                      begin
                        if (cs_asm_source in current_settings.globalswitches) then
                          asml.insertbefore(tai_comment.create(strpnew('PeepHole Optimization,var9')),p);
                        taicpu(p).opcode := A_AND;
                        taicpu(p).changeopsize(S_L);
                        taicpu(p).loadConst(0, $ff);
                      end
                    else if GetNextInstruction(p, hp1) and
                      (tai(hp1).typ = ait_instruction) and
                      (taicpu(hp1).opcode = A_AND) and
                      (taicpu(hp1).oper[0]^.typ = top_const) and
                      (taicpu(hp1).oper[1]^.typ = top_reg) and
                      (taicpu(hp1).oper[1]^.reg =
                      taicpu(p).oper[1]^.reg) then
                      { Change "movzbl %reg1, %reg2; andl $const, %reg2"
                        to "movl %reg1, reg2; andl $(const1 and $ff), %reg2"}
                      begin
                        if (cs_asm_source in current_settings.globalswitches) then
                          asml.insertbefore(tai_comment.create(strpnew('PeepHole Optimization,var10')),p);
                        taicpu(p).opcode := A_MOV;
                        taicpu(p).changeopsize(S_L);
                        { do not use R_SUBWHOLE
                          as movl %rdx,%eax
                          is invalid in assembler PM }
                        setsubreg(taicpu(p).oper[0]^.reg, R_SUBD);
                        taicpu(hp1).loadConst(
                          0, taicpu(hp1).oper[0]^.val and $ff);
                      end;
                    end;
                  S_WL:
                    begin
                    if (getsupreg(taicpu(p).oper[0]^.reg) =
                      getsupreg(taicpu(p).oper[1]^.reg)) and  not
                      (cs_opt_size in current_settings.optimizerswitches) then
                      { Change "movzwl %ax, %eax" to "andl $0x0ffffh, %eax" }
                      begin
                        if (cs_asm_source in current_settings.globalswitches) then
                          asml.insertbefore(tai_comment.create(strpnew('PeepHole Optimization,var11')),p);
                        taicpu(p).opcode := A_AND;
                        taicpu(p).changeopsize(S_L);
                        taicpu(p).loadConst(0, $ffff);
                      end
                    else if GetNextInstruction(p, hp1) and
                      (tai(hp1).typ = ait_instruction) and
                      (taicpu(hp1).opcode = A_AND) and
                      (taicpu(hp1).oper[0]^.typ = top_const) and
                      (taicpu(hp1).oper[1]^.typ = top_reg) and
                      (taicpu(hp1).oper[1]^.reg =
                      taicpu(p).oper[1]^.reg) then
                      { Change "movzwl %reg1, %reg2; andl $const, %reg2"
                        to "movl %reg1, reg2; andl $(const1 and $ffff), %reg2"}
                      begin
                        if (cs_asm_source in current_settings.globalswitches) then
                          asml.insertbefore(tai_comment.create(strpnew('PeepHole Optimization,var12')),p);
                        taicpu(p).opcode := A_MOV;
                        taicpu(p).changeopsize(S_L);
                        { do not use R_SUBWHOLE
                          as movl %rdx,%eax
                          is invalid in assembler PM }
                        setsubreg(taicpu(p).oper[0]^.reg, R_SUBD);
                        taicpu(hp1).loadConst(
                          0, taicpu(hp1).oper[0]^.val and $ffff);
                      end;
                    end;
                  end
              else if (taicpu(p).oper[0]^.typ = top_ref) then
                begin
                if GetNextInstruction(p, hp1) and
                  (tai(hp1).typ = ait_instruction) and
                  (taicpu(hp1).opcode = A_AND) and
                  (taicpu(hp1).oper[0]^.typ = Top_Const) and
                  (taicpu(hp1).oper[1]^.typ = Top_Reg) and
                  (taicpu(hp1).oper[1]^.reg =
                  taicpu(p).oper[1]^.reg) then
                  begin
                  taicpu(p).opcode := A_MOV;
                  case taicpu(p).opsize of
                    S_BL:
                      begin
                        if (cs_asm_source in current_settings.globalswitches) then
                          asml.insertbefore(tai_comment.create(strpnew('PeepHole Optimization,var13')),p);
                        taicpu(p).changeopsize(S_L);
                        taicpu(hp1).loadConst(
                          0, taicpu(hp1).oper[0]^.val and $ff);
                      end;
                    S_WL:
                      begin
                        if (cs_asm_source in current_settings.globalswitches) then
                          asml.insertbefore(tai_comment.create(strpnew('PeepHole Optimization,var14')),p);
                        taicpu(p).changeopsize(S_L);
                        taicpu(hp1).loadConst(
                          0, taicpu(hp1).oper[0]^.val and $ffff);
                      end;
                    S_BW:
                      begin
                        if (cs_asm_source in current_settings.globalswitches) then
                          asml.insertbefore(tai_comment.create(strpnew('PeepHole Optimization,var15')),p);
                        taicpu(p).changeopsize(S_W);
                        taicpu(hp1).loadConst(
                          0, taicpu(hp1).oper[0]^.val and $ff);
                      end;
                    S_BQ:
                      begin
                        if (cs_asm_source in current_settings.globalswitches) then
                          asml.insertbefore(tai_comment.create(strpnew('PeepHole Optimization,var16')),p);
                        taicpu(p).changeopsize(S_Q);
                        taicpu(hp1).loadConst(
                          0, taicpu(hp1).oper[0]^.val and $ff);
                      end;
                    S_WQ:
                      begin
                        if (cs_asm_source in current_settings.globalswitches) then
                          asml.insertbefore(tai_comment.create(strpnew('PeepHole Optimization,var17')),p);
                        taicpu(p).changeopsize(S_Q);
                        taicpu(hp1).loadConst(
                          0, taicpu(hp1).oper[0]^.val and $ffff);
                      end;
                    S_LQ:
                      begin
                        if (cs_asm_source in current_settings.globalswitches) then
                          asml.insertbefore(tai_comment.create(strpnew('PeepHole Optimization,var18')),p);
                        taicpu(p).changeopsize(S_Q);
                        taicpu(hp1).loadConst(
                          0, taicpu(hp1).oper[0]^.val and $ffffffff);
                      end;
                    end;
                  end;
                end;
            end;
          end;
        end;
      end;
    end;
end;

begin
  casmoptimizer := TCpuAsmOptimizer;
end.

