{
    Copyright (c) 1998-2002 by Carl Eric Codere and Peter Vreman

    Does the parsing process for the intel styled inline assembler.

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
Unit Rax86int;

{$i fpcdefs.inc}

  interface

    uses
      cclasses,
      cpubase,
      globtype,
      aasmbase,
      rasm,
      rax86;

  type
    tasmtoken = (
      AS_NONE,AS_LABEL,AS_LLABEL,AS_STRING,AS_INTNUM,
      AS_COMMA,AS_LBRACKET,AS_RBRACKET,AS_LPAREN,
      AS_RPAREN,AS_COLON,AS_DOT,AS_PLUS,AS_MINUS,AS_STAR,
      AS_SEPARATOR,AS_ID,AS_REGISTER,AS_OPCODE,AS_SLASH,
       {------------------ Assembler directives --------------------}
      AS_ALIGN,AS_DB,AS_DW,AS_DD,AS_DQ,AS_END,
       {------------------ Assembler Operators  --------------------}
      AS_BYTE,AS_WORD,AS_DWORD,AS_QWORD,AS_TBYTE,AS_DQWORD,AS_NEAR,AS_FAR,
      AS_HIGH,AS_LOW,AS_OFFSET,AS_SIZEOF,AS_VMTOFFSET,AS_SEG,AS_TYPE,AS_PTR,AS_MOD,AS_SHL,AS_SHR,AS_NOT,
      AS_AND,AS_OR,AS_XOR);

    type
       tx86intreader = class(tasmreader)
         actasmtoken : tasmtoken;
         prevasmtoken : tasmtoken;
         ActOpsize : topsize;
         constructor create;override;
         function is_asmopcode(const s: string):boolean;
         function is_asmoperator(const s: string):boolean;
         function is_asmdirective(const s: string):boolean;
         function is_register(const s:string):boolean;
         function is_locallabel(const s:string):boolean;
         function Assemble: tlinkedlist;override;
         procedure GetToken;
         function consume(t : tasmtoken):boolean;
         procedure RecoverConsume(allowcomma:boolean);
         procedure BuildRecordOffsetSize(const expr: string;var offset:aint;var size:aint; var mangledname: string; needvmtofs: boolean);
         procedure BuildConstSymbolExpression(needofs,isref,startingminus:boolean;var value:aint;var asmsym:string;var asmsymtyp:TAsmsymtype);
         function BuildConstExpression:aint;
         function BuildRefConstExpression:aint;
         procedure BuildReference(oper : tx86operand);
         procedure BuildOperand(oper: tx86operand;istypecast:boolean);
         procedure BuildConstantOperand(oper: tx86operand);
         procedure BuildOpCode(instr : tx86instruction);
         procedure BuildConstant(constsize: byte);
       end;


  implementation

    uses
       { common }
       cutils,
       { global }
       globals,verbose,
       systems,
       { aasm }
       aasmtai,aasmdata,aasmcpu,
       { symtable }
       symconst,symbase,symtype,symsym,symdef,symtable,
       { parser }
       scanner,
       { register allocator }
       rabase,rautils,itx86int,
       { codegen }
       cgbase,cgobj,procinfo
       ;

    type
      tasmkeyword = string[9];


    const
       { These tokens should be modified accordingly to the modifications }
       { in the different enumerations.                                   }
       firstdirective = AS_ALIGN;
       lastdirective  = AS_END;
       firstoperator  = AS_BYTE;
       lastoperator   = AS_XOR;

       _count_asmdirectives = longint(lastdirective)-longint(firstdirective);
       _count_asmoperators  = longint(lastoperator)-longint(firstoperator);

       _asmdirectives : array[0.._count_asmdirectives] of tasmkeyword =
       ('ALIGN','DB','DW','DD','DQ','END');

       { problems with shl,shr,not,and,or and xor, they are }
       { context sensitive.                                 }
       _asmoperators : array[0.._count_asmoperators] of tasmkeyword = (
        'BYTE','WORD','DWORD','QWORD','TBYTE','DQWORD','NEAR','FAR','HIGH',
        'LOW','OFFSET','SIZEOF','VMTOFFSET','SEG','TYPE','PTR','MOD','SHL','SHR','NOT','AND',
        'OR','XOR');

      token2str : array[tasmtoken] of string[10] = (
        '','Label','LLabel','String','Integer',
        ',','[',']','(',
        ')',':','.','+','-','*',
        ';','identifier','register','opcode','/',
        '','','','','','END',
        '','','','','','','','','',
        '','','sizeof','vmtoffset','','type','ptr','mod','shl','shr','not',
        'and','or','xor'
      );

    var
      inexpression   : boolean;

    constructor tx86intreader.create;
      var
        i : tasmop;
      Begin
        inherited create;
        iasmops:=TFPHashList.create;
        for i:=firstop to lastop do
          iasmops.Add(upper(std_op2str[i]),Pointer(PtrInt(i)));
      end;


{---------------------------------------------------------------------}
{                     Routines for the tokenizing                     }
{---------------------------------------------------------------------}


     function tx86intreader.is_asmopcode(const s: string):boolean;
       var
         cond : string[4];
         cnd : tasmcond;
         j: longint;
       Begin
         is_asmopcode:=FALSE;

         actopcode:=A_None;
         actcondition:=C_None;
         actopsize:=S_NO;

         { Search opcodes }
         actopcode:=tasmop(PtrUInt(iasmops.Find(s)));
         if actopcode<>A_NONE then
           begin
             actasmtoken:=AS_OPCODE;
             result:=TRUE;
             exit;
           end;

         { not found yet, check condition opcodes }
         j:=0;
         while (j<CondAsmOps) do
          begin
            if Copy(s,1,Length(CondAsmOpStr[j]))=CondAsmOpStr[j] then
             begin
               cond:=Copy(s,Length(CondAsmOpStr[j])+1,255);
               if cond<>'' then
                begin
                  for cnd:=low(TasmCond) to high(TasmCond) do
                   if Cond=Upper(cond2str[cnd]) then
                    begin
                      actopcode:=CondASmOp[j];
                      actcondition:=cnd;
                      is_asmopcode:=TRUE;
                      actasmtoken:=AS_OPCODE;
                      exit
                    end;
                end;
             end;
            inc(j);
          end;
       end;


    function tx86intreader.is_asmoperator(const s: string):boolean;
      var
        i : longint;
      Begin
        for i:=0 to _count_asmoperators do
         if s=_asmoperators[i] then
          begin
            actasmtoken:=tasmtoken(longint(firstoperator)+i);
            is_asmoperator:=true;
            exit;
          end;
        is_asmoperator:=false;
      end;


    Function tx86intreader.is_asmdirective(const s: string):boolean;
      var
        i : longint;
      Begin
        for i:=0 to _count_asmdirectives do
         if s=_asmdirectives[i] then
          begin
            actasmtoken:=tasmtoken(longint(firstdirective)+i);
            is_asmdirective:=true;
            exit;
          end;
        is_asmdirective:=false;
      end;


    function tx86intreader.is_register(const s:string):boolean;
      var
        entry: TSymEntry;
      begin
        is_register:=false;
        actasmregister:=masm_regnum_search(lower(s));
        if (actasmregister=NR_NO) and
           (current_procinfo.procdef.proccalloption=pocall_register) and
           (po_assembler in current_procinfo.procdef.procoptions) then
          begin
            entry:=current_procinfo.procdef.parast.Find(s);
            if assigned(entry) and
               (entry.typ=paravarsym) and
               assigned(tparavarsym(entry).paraloc[calleeside].Location) and
               (tparavarsym(entry).paraloc[calleeside].Location^.Loc=LOC_REGISTER) then
              actasmregister:=tparavarsym(entry).paraloc[calleeside].Location^.register;
          end;
        if actasmregister<>NR_NO then
          begin
            is_register:=true;
            actasmtoken:=AS_REGISTER;
          end;
      end;


    function tx86intreader.is_locallabel(const s:string):boolean;
      begin
        is_locallabel:=(length(s)>1) and (s[1]='@');
      end;


    Procedure tx86intreader.GetToken;
      var
        len : longint;
        forcelabel : boolean;
        srsym : tsym;
        srsymtable : TSymtable;
      begin
        { save old token and reset new token }
        prevasmtoken:=actasmtoken;
        actasmtoken:=AS_NONE;
        { reset }
        forcelabel:=FALSE;
        actasmpattern:='';
        { while space and tab , continue scan... }
        while (c in [' ',#9]) do
          c:=current_scanner.asmgetchar;
        { get token pos }
        if not (c in [#10,#13,'{',';']) then
          current_scanner.gettokenpos;
      { Local Label, Label, Directive, Prefix or Opcode }
        if firsttoken and not (c in [#10,#13,'{',';']) then
         begin
           firsttoken:=FALSE;
           len:=0;
           while c in ['A'..'Z','a'..'z','0'..'9','_','@'] do
            begin
              { if there is an at_sign, then this must absolutely be a label }
              if c = '@' then
               forcelabel:=TRUE;
              inc(len);
              actasmpattern[len]:=c;
              c:=current_scanner.asmgetchar;
            end;
           actasmpattern[0]:=chr(len);
           uppervar(actasmpattern);
           { allow spaces }
           while (c in [' ',#9]) do
             c:=current_scanner.asmgetchar;
           { label ? }
           if c = ':' then
            begin
              if actasmpattern[1]='@' then
                actasmtoken:=AS_LLABEL
              else
                actasmtoken:=AS_LABEL;
              { let us point to the next character }
              c:=current_scanner.asmgetchar;
              firsttoken:=true;
              exit;
            end;
           { Are we trying to create an identifier with }
           { an at-sign...?                             }
           if forcelabel then
            Message(asmr_e_none_label_contain_at);
           { opcode ? }
           If is_asmopcode(actasmpattern) then
            Begin
              { check if we are in an expression  }
              { then continue with asm directives }
              if not inexpression then
               exit;
            end;
           if is_asmdirective(actasmpattern) then
            exit;
           message1(asmr_e_unknown_opcode,actasmpattern);
           actasmtoken:=AS_NONE;
           exit;
         end
        else { else firsttoken }
         begin
           case c of
             '@' : { possiblities : - local label reference , such as in jmp @local1 }
                   {                - @Result, @Code or @Data special variables.     }
               begin
                 actasmpattern:=c;
                 c:=current_scanner.asmgetchar;
                 while c in  ['A'..'Z','a'..'z','0'..'9','_','@'] do
                  begin
                    actasmpattern:=actasmpattern + c;
                    c:=current_scanner.asmgetchar;
                  end;
                 uppervar(actasmpattern);
                 actasmtoken:=AS_ID;
                 exit;
               end;

             'A'..'Z','a'..'z','_': { identifier, register, opcode, prefix or directive }
               begin
                 actasmpattern:=c;
                 c:=current_scanner.asmgetchar;
                 while c in  ['A'..'Z','a'..'z','0'..'9','_'] do
                  begin
                    actasmpattern:=actasmpattern + c;
                    c:=current_scanner.asmgetchar;
                  end;
                 uppervar(actasmpattern);
                 { after prefix we allow also a new opcode }
                 If is_prefix(actopcode) and is_asmopcode(actasmpattern) then
                  Begin
                    { if we are not in a constant }
                    { expression than this is an  }
                    { opcode.                     }
                    if not inexpression then
                     exit;
                  end;
                 { support st(X) for fpu registers }
                 if (actasmpattern = 'ST') and (c='(') then
                  Begin
                    actasmpattern:=actasmpattern+c;
                    c:=current_scanner.asmgetchar;
                    { allow spaces }
                    while (c in [' ',#9]) do
                      c:=current_scanner.asmgetchar;
                    if c in ['0'..'7'] then
                     actasmpattern:=actasmpattern + c
                    else
                     Message(asmr_e_invalid_fpu_register);
                    c:=current_scanner.asmgetchar;
                    { allow spaces }
                    while (c in [' ',#9]) do
                      c:=current_scanner.asmgetchar;
                    if c <> ')' then
                     Message(asmr_e_invalid_fpu_register)
                    else
                     Begin
                       actasmpattern:=actasmpattern + c;
                       c:=current_scanner.asmgetchar;
                     end;
                  end;
                 if is_asmdirective(actasmpattern) then
                  exit;
                 if is_asmoperator(actasmpattern) then
                  exit;
                 if is_register(actasmpattern) then
                  exit;
                 { allow spaces }
                 while (c in [' ',#9]) do
                   c:=current_scanner.asmgetchar;
                 { if next is a '.' and this is a unitsym then we also need to
                   parse the identifier }
                 if (c='.') then
                  begin
                    asmsearchsym(actasmpattern,srsym,srsymtable);
                    if assigned(srsym) and
                       (srsym.typ=unitsym) and
                       (srsym.owner.symtabletype in [staticsymtable,globalsymtable]) and
                       srsym.owner.iscurrentunit then
                     begin
                       { Add . to create System.Identifier }
                       actasmpattern:=actasmpattern+c;
                       c:=current_scanner.asmgetchar;
                       { Delphi allows System.@Halt, just ignore the @ }
                       if c='@' then
                         c:=current_scanner.asmgetchar;
                       while c in  ['A'..'Z','a'..'z','0'..'9','_','$'] do
                        begin
                          actasmpattern:=actasmpattern + upcase(c);
                          c:=current_scanner.asmgetchar;
                        end;
                     end;
                  end;
                 actasmtoken:=AS_ID;
                 exit;
               end;

             '''' : { string or character }
               begin
                 actasmpattern:='';
                 current_scanner.in_asm_string:=true;
                 repeat
                   if c = '''' then
                    begin
                      c:=current_scanner.asmgetchar;
                      if c in [#10,#13] then
                       begin
                         Message(scan_f_string_exceeds_line);
                         break;
                       end;
                      repeat
                        if c='''' then
                         begin
                           c:=current_scanner.asmgetchar;
                           if c='''' then
                            begin
                              actasmpattern:=actasmpattern+'''';
                              c:=current_scanner.asmgetchar;
                              if c in [#10,#13] then
                               begin
                                 Message(scan_f_string_exceeds_line);
                                 break;
                               end;
                            end
                           else
                            break;
                         end
                        else
                         begin
                           actasmpattern:=actasmpattern+c;
                           c:=current_scanner.asmgetchar;
                           if c in [#10,#13] then
                            begin
                              Message(scan_f_string_exceeds_line);
                              break
                            end;
                         end;
                      until false; { end repeat }
                    end
                   else
                    break; { end if }
                 until false;
                 current_scanner.in_asm_string:=false;
                 actasmtoken:=AS_STRING;
                 exit;
               end;

             '"' : { string or character }
               begin
                 current_scanner.in_asm_string:=true;
                 actasmpattern:='';
                 repeat
                   if c = '"' then
                    begin
                      c:=current_scanner.asmgetchar;
                      if c in [#10,#13] then
                       begin
                         Message(scan_f_string_exceeds_line);
                         break;
                       end;
                      repeat
                        if c='"' then
                         begin
                           c:=current_scanner.asmgetchar;
                           if c='"' then
                            begin
                              actasmpattern:=actasmpattern+'"';
                              c:=current_scanner.asmgetchar;
                              if c in [#10,#13] then
                               begin
                                 Message(scan_f_string_exceeds_line);
                                 break;
                               end;
                            end
                           else
                            break;
                         end
                        else
                         begin
                           actasmpattern:=actasmpattern+c;
                           c:=current_scanner.asmgetchar;
                           if c in [#10,#13] then
                            begin
                              Message(scan_f_string_exceeds_line);
                              break
                            end;
                         end;
                      until false; { end repeat }
                    end
                   else
                    break; { end if }
                 until false;
                 current_scanner.in_asm_string:=false;
                 actasmtoken:=AS_STRING;
                 exit;
               end;

             '$' :
               begin
                 c:=current_scanner.asmgetchar;
                 while c in ['0'..'9','A'..'F','a'..'f'] do
                  begin
                    actasmpattern:=actasmpattern + c;
                    c:=current_scanner.asmgetchar;
                  end;
                 actasmpattern:=tostr(ParseVal(actasmpattern,16));
                 actasmtoken:=AS_INTNUM;
                 exit;
               end;

             '&' : { identifier }
               begin
                 actasmpattern:='';
                 c:=current_scanner.asmgetchar;
                 while c in  ['A'..'Z','a'..'z','0'..'9','_'] do
                  begin
                    actasmpattern:=actasmpattern + c;
                    c:=current_scanner.asmgetchar;
                  end;
                 uppervar(actasmpattern);
                 actasmtoken:=AS_ID;
                 exit;
               end;

             ',' :
               begin
                 actasmtoken:=AS_COMMA;
                 c:=current_scanner.asmgetchar;
                 exit;
               end;

             '[' :
               begin
                 actasmtoken:=AS_LBRACKET;
                 c:=current_scanner.asmgetchar;
                 exit;
               end;

             ']' :
               begin
                 actasmtoken:=AS_RBRACKET;
                 c:=current_scanner.asmgetchar;
                 exit;
               end;

             '(' :
               begin
                 actasmtoken:=AS_LPAREN;
                 c:=current_scanner.asmgetchar;
                 exit;
               end;

             ')' :
               begin
                 actasmtoken:=AS_RPAREN;
                 c:=current_scanner.asmgetchar;
                 exit;
               end;

             ':' :
               begin
                 actasmtoken:=AS_COLON;
                 c:=current_scanner.asmgetchar;
                 exit;
               end;

             '.' :
               begin
                 actasmtoken:=AS_DOT;
                 c:=current_scanner.asmgetchar;
                 exit;
               end;

             '+' :
               begin
                 actasmtoken:=AS_PLUS;
                 c:=current_scanner.asmgetchar;
                 exit;
               end;

             '-' :
               begin
                 actasmtoken:=AS_MINUS;
                 c:=current_scanner.asmgetchar;
                 exit;
               end;

             '*' :
               begin
                 actasmtoken:=AS_STAR;
                 c:=current_scanner.asmgetchar;
                 exit;
               end;

             '/' :
               begin
                 actasmtoken:=AS_SLASH;
                 c:=current_scanner.asmgetchar;
                 exit;
               end;

             '0'..'9':
               begin
                 actasmpattern:=c;
                 c:=current_scanner.asmgetchar;
                 { Get the possible characters }
                 while c in ['0'..'9','A'..'F','a'..'f'] do
                  begin
                    actasmpattern:=actasmpattern + c;
                    c:=current_scanner.asmgetchar;
                  end;
                 { Get ending character }
                 uppervar(actasmpattern);
                 c:=upcase(c);
                 { possibly a binary number. }
                 if (actasmpattern[length(actasmpattern)] = 'B') and (c <> 'H') then
                  Begin
                    { Delete the last binary specifier }
                    delete(actasmpattern,length(actasmpattern),1);
                    actasmpattern:=tostr(ParseVal(actasmpattern,2));
                    actasmtoken:=AS_INTNUM;
                    exit;
                  end
                 else
                  Begin
                    case c of
                      'O' :
                        Begin
                          actasmpattern:=tostr(ParseVal(actasmpattern,8));
                          actasmtoken:=AS_INTNUM;
                          c:=current_scanner.asmgetchar;
                          exit;
                        end;
                      'H' :
                        Begin
                          actasmpattern:=tostr(ParseVal(actasmpattern,16));
                          actasmtoken:=AS_INTNUM;
                          c:=current_scanner.asmgetchar;
                          exit;
                        end;
                      else { must be an integer number }
                        begin
                          actasmpattern:=tostr(ParseVal(actasmpattern,10));
                          actasmtoken:=AS_INTNUM;
                          exit;
                        end;
                    end;
                  end;
               end;
             ';','{',#13,#10 :
               begin
                 c:=current_scanner.asmgetchar;
                 firsttoken:=TRUE;
                 actasmtoken:=AS_SEPARATOR;
                 exit;
               end;

              else
                 current_scanner.illegal_char(c);
           end;
         end;
      end;


  function tx86intreader.consume(t : tasmtoken):boolean;
    begin
      Consume:=true;
      if t<>actasmtoken then
       begin
         Message2(scan_f_syn_expected,token2str[t],token2str[actasmtoken]);
         Consume:=false;
       end;
      repeat
        gettoken;
      until actasmtoken<>AS_NONE;
    end;


  procedure tx86intreader.RecoverConsume(allowcomma:boolean);
    begin
      While not (actasmtoken in [AS_SEPARATOR,AS_END]) do
       begin
         if allowcomma and (actasmtoken=AS_COMMA) then
          break;
         Consume(actasmtoken);
       end;
    end;


{*****************************************************************************
                                 Parsing Helpers
*****************************************************************************}

    { This routine builds up a record offset after a AS_DOT
      token is encountered.
      On entry actasmtoken should be equal to AS_DOT                     }
    Procedure tx86intreader.BuildRecordOffsetSize(const expr: string;var offset:aint;var size:aint; var mangledname: string; needvmtofs: boolean);
      var
        s: string;
      Begin
        offset:=0;
        size:=0;
        s:=expr;
        while (actasmtoken=AS_DOT) do
         begin
           Consume(AS_DOT);
           if actasmtoken in [AS_BYTE,AS_ID,AS_WORD,AS_DWORD,AS_QWORD,AS_REGISTER] then
             begin
               s:=s+'.'+actasmpattern;
               consume(actasmtoken);
             end
           else
            begin
              Consume(AS_ID);
              RecoverConsume(true);
              break;
            end;
         end;
        if not GetRecordOffsetSize(s,offset,size,mangledname,needvmtofs) then
          Message(asmr_e_building_record_offset);
      end;


    Procedure tx86intreader.BuildConstSymbolExpression(needofs,isref,startingminus:boolean;var value:aint;var asmsym:string;var asmsymtyp:TAsmsymtype);
      var
        tempstr,expr,hs,mangledname : string;
        parenlevel : longint;
        l,k : aint;
        hasparen,
        errorflag,
        needvmtofs : boolean;
        prevtok : tasmtoken;
        hl : tasmlabel;
        hssymtyp : Tasmsymtype;
        def : tdef;
        sym : tsym;
        srsymtable : TSymtable;
      Begin
        { reset }
        value:=0;
        asmsym:='';
        asmsymtyp:=AT_DATA;
        errorflag:=FALSE;
        tempstr:='';
        expr:='';
        if startingminus then
          expr:='-';
        inexpression:=TRUE;
        parenlevel:=0;
        sym:=nil;
        needvmtofs:=FALSE;
        Repeat
          { Support ugly delphi constructs like: [ECX].1+2[EDX] }
          if isref and (actasmtoken=AS_LBRACKET) then
            break;
          Case actasmtoken of
            AS_LPAREN:
              Begin
                Consume(AS_LPAREN);
                expr:=expr + '(';
                inc(parenlevel);
              end;
            AS_RPAREN:
              Begin
                { Keep the AS_PAREN in actasmtoken, it is maybe a typecast }
                if parenlevel=0 then
                  break;
                Consume(AS_RPAREN);
                expr:=expr + ')';
                dec(parenlevel);
              end;
            AS_SHL:
              Begin
                Consume(AS_SHL);
                expr:=expr + '<';
              end;
            AS_SHR:
              Begin
                Consume(AS_SHR);
                expr:=expr + '>';
              end;
            AS_SLASH:
              Begin
                Consume(AS_SLASH);
                expr:=expr + '/';
              end;
            AS_MOD:
              Begin
                Consume(AS_MOD);
                expr:=expr + '%';
              end;
            AS_STAR:
              Begin
                Consume(AS_STAR);
                if isref and (actasmtoken=AS_REGISTER) then
                 break;
                expr:=expr + '*';
              end;
            AS_PLUS:
              Begin
                Consume(AS_PLUS);
                if isref and (actasmtoken=AS_REGISTER) then
                 break;
                expr:=expr + '+';
              end;
            AS_MINUS:
              Begin
                Consume(AS_MINUS);
                expr:=expr + '-';
              end;
            AS_AND:
              Begin
                Consume(AS_AND);
                expr:=expr + '&';
              end;
            AS_NOT:
              Begin
                Consume(AS_NOT);
                expr:=expr + '~';
              end;
            AS_XOR:
              Begin
                Consume(AS_XOR);
                expr:=expr + '^';
              end;
            AS_OR:
              Begin
                Consume(AS_OR);
                expr:=expr + '|';
              end;
            AS_INTNUM:
              Begin
                expr:=expr + actasmpattern;
                Consume(AS_INTNUM);
              end;
            AS_VMTOFFSET,
            AS_OFFSET:
              begin
                if (actasmtoken = AS_OFFSET) then
                  needofs:=true
                else
                  needvmtofs:=true;
                Consume(actasmtoken);
                if actasmtoken<>AS_ID then
                 Message(asmr_e_offset_without_identifier);
              end;
            AS_SIZEOF,
            AS_TYPE:
              begin
                l:=0;
                hasparen:=false;
                Consume(actasmtoken);
                if actasmtoken=AS_LPAREN then
                  begin
                    hasparen:=true;
                    Consume(AS_LPAREN);
                  end;
                if actasmtoken<>AS_ID then
                 Message(asmr_e_type_without_identifier)
                else
                 begin
                   tempstr:=actasmpattern;
                   Consume(AS_ID);
                   if actasmtoken=AS_DOT then
                     begin
                       BuildRecordOffsetSize(tempstr,k,l,mangledname,false);
                       if mangledname<>'' then
                         { procsym }
                         Message(asmr_e_wrong_sym_type);
                     end
                   else
                    begin
                      asmsearchsym(tempstr,sym,srsymtable);
                      if assigned(sym) then
                       begin
                         case sym.typ of
                           staticvarsym,
                           localvarsym,
                           paravarsym :
                             l:=tabstractvarsym(sym).getsize;
                           typesym :
                             l:=ttypesym(sym).typedef.size;
                           else
                             Message(asmr_e_wrong_sym_type);
                         end;
                       end
                      else
                       Message1(sym_e_unknown_id,tempstr);
                    end;
                 end;
                str(l, tempstr);
                expr:=expr + tempstr;
                if hasparen then
                  Consume(AS_RPAREN);
              end;
            AS_PTR :
              begin
                { Support ugly delphi constructs like <constant> PTR [ref] }
                break;
              end;
            AS_STRING:
              begin
                l:=0;
                case Length(actasmpattern) of
                 1 :
                  l:=ord(actasmpattern[1]);
                 2 :
                  l:=ord(actasmpattern[2]) + ord(actasmpattern[1]) shl 8;
                 3 :
                  l:=ord(actasmpattern[3]) +
                     Ord(actasmpattern[2]) shl 8 + ord(actasmpattern[1]) shl 16;
                 4 :
                  l:=ord(actasmpattern[4]) + ord(actasmpattern[3]) shl 8 +
                     Ord(actasmpattern[2]) shl 16 + ord(actasmpattern[1]) shl 24;
                else
                  Message1(asmr_e_invalid_string_as_opcode_operand,actasmpattern);
                end;
                str(l, tempstr);
                expr:=expr + tempstr;
                Consume(AS_STRING);
              end;
            AS_ID:
              begin
                hs:='';
                hssymtyp:=AT_DATA;
                def:=nil;
                tempstr:=actasmpattern;
                prevtok:=prevasmtoken;
                { stop parsing a constant expression if we find an opcode after a
                  non-operator like "db $66 mov eax,ebx" }
                if (prevtok in [AS_ID,AS_INTNUM,AS_RPAREN]) and
                   is_asmopcode(actasmpattern) then
                  break;
                consume(AS_ID);
                if SearchIConstant(tempstr,l) then
                 begin
                   str(l, tempstr);
                   expr:=expr + tempstr;
                 end
                else
                 begin
                   if is_locallabel(tempstr) then
                    begin
                      CreateLocalLabel(tempstr,hl,false);
                      hs:=hl.name;
                      hssymtyp:=AT_FUNCTION;
                    end
                   else
                    if SearchLabel(tempstr,hl,false) then
                      begin
                        hs:=hl.name;
                        hssymtyp:=AT_FUNCTION;
                      end
                   else
                    begin
                      asmsearchsym(tempstr,sym,srsymtable);
                      if assigned(sym) then
                       begin
                         case sym.typ of
                           staticvarsym :
                             begin
                               hs:=tstaticvarsym(sym).mangledname;
                               def:=tstaticvarsym(sym).vardef;
                             end;
                           localvarsym,
                           paravarsym :
                             begin
                               Message(asmr_e_no_local_or_para_allowed);
                             end;
                           procsym :
                             begin
                               if Tprocsym(sym).ProcdefList.Count>1 then
                                Message(asmr_w_calling_overload_func);
                               hs:=tprocdef(tprocsym(sym).ProcdefList[0]).mangledname;
                               hssymtyp:=AT_FUNCTION;
                             end;
                           typesym :
                             begin
                               if not(ttypesym(sym).typedef.typ in [recorddef,objectdef]) then
                                Message(asmr_e_wrong_sym_type);
                             end;
                           fieldvarsym :
                             begin
                               tempstr:=upper(tdef(sym.owner.defowner).GetTypeName)+'.'+tempstr;
                             end;
                           else
                             Message(asmr_e_wrong_sym_type);
                         end;
                       end
                      else
                       Message1(sym_e_unknown_id,tempstr);
                    end;
                   { symbol found? }
                   if hs<>'' then
                    begin
                      if asmsym='' then
                        begin
                          asmsym:=hs;
                          asmsymtyp:=hssymtyp;
                        end
                      else
                       Message(asmr_e_cant_have_multiple_relocatable_symbols);
                      if (expr='') or (expr[length(expr)]='+') then
                       begin
                         { don't remove the + if there could be a record field }
                         if actasmtoken<>AS_DOT then
                          delete(expr,length(expr),1);
                       end
                      else
                       if needofs then
                         begin
                           if (prevtok<>AS_OFFSET) then
                             Message(asmr_e_need_offset);
                         end
                       else
                         Message(asmr_e_only_add_relocatable_symbol);
                    end;
                   if (actasmtoken=AS_DOT) or
                      (assigned(sym) and
                       (sym.typ = fieldvarsym)) then
                     begin
                      BuildRecordOffsetSize(tempstr,l,k,hs,needvmtofs);
                      if hs <> '' then
                        hssymtyp:=AT_FUNCTION
                      else
                        begin
                          str(l, tempstr);
                          expr:=expr + tempstr;
                        end
                    end
                   else
                    begin
                      if (expr='') or (expr[length(expr)] in ['+','-','/','*']) then
                       delete(expr,length(expr),1);
                    end;
                   if (actasmtoken=AS_LBRACKET) and
                      assigned(def) and
                      (def.typ=arraydef) then
                     begin
                       consume(AS_LBRACKET);
                       l:=BuildConstExpression;
                       if l<tarraydef(def).lowrange then
                         begin
                           Message(asmr_e_constant_out_of_bounds);
                           l:=0;
                         end
                       else
                         l:=(l-tarraydef(def).lowrange)*tarraydef(def).elesize;
                       str(l, tempstr);
                       expr:=expr + '+' + tempstr;
                       consume(AS_RBRACKET);
                     end;
                 end;
                { check if there are wrong operator used like / or mod etc. }
                if (hs<>'') and not(actasmtoken in [AS_MINUS,AS_PLUS,AS_COMMA,AS_SEPARATOR,AS_END,AS_RBRACKET]) then
                 Message(asmr_e_only_add_relocatable_symbol);
              end;
            AS_ALIGN,
            AS_DB,
            AS_DW,
            AS_DD,
            AS_DQ,
            AS_END,
            AS_RBRACKET,
            AS_SEPARATOR,
            AS_COMMA,
            AS_COLON:
              break;
          else
            begin
              { write error only once. }
              if not errorflag then
                Message(asmr_e_invalid_constant_expression);
              { consume tokens until we find COMMA or SEPARATOR }
              Consume(actasmtoken);
              errorflag:=TRUE;
            end;
          end;
        Until false;
        { calculate expression }
        if not ErrorFlag then
          value:=CalculateExpression(expr)
        else
          value:=0;
        { no longer in an expression }
        inexpression:=FALSE;
      end;


    Function tx86intreader.BuildConstExpression:aint;
      var
        l : aint;
        hs : string;
        hssymtyp : TAsmsymtype;
      begin
        BuildConstSymbolExpression(false,false,false,l,hs,hssymtyp);
        if hs<>'' then
         Message(asmr_e_relocatable_symbol_not_allowed);
        BuildConstExpression:=l;
      end;


    Function tx86intreader.BuildRefConstExpression:aint;
      var
        l : aint;
        hs : string;
        hssymtyp : TAsmsymtype;
      begin
        BuildConstSymbolExpression(false,true,false,l,hs,hssymtyp);
        if hs<>'' then
         Message(asmr_e_relocatable_symbol_not_allowed);
        BuildRefConstExpression:=l;
      end;


    procedure tx86intreader.BuildReference(oper : tx86operand);
      var
        scale : byte;
        k,l : aint;
        tempstr,hs : string;
        tempsymtyp : tasmsymtype;
        code : integer;
        hreg : tregister;
        GotStar,GotOffset,HadVar,
        GotPlus,Negative : boolean;
        hl : tasmlabel;
      Begin
        Consume(AS_LBRACKET);
        if not(oper.opr.typ in [OPR_LOCAL,OPR_REFERENCE]) then
          oper.InitRef;
        GotStar:=false;
        GotPlus:=true;
        GotOffset:=false;
        Negative:=false;
        Scale:=0;
        repeat
          if GotOffset and (actasmtoken<>AS_ID) then
            Message(asmr_e_invalid_reference_syntax);

          Case actasmtoken of
            AS_ID, { Constant reference expression OR variable reference expression }
            AS_VMTOFFSET:
              Begin
                if not GotPlus then
                  Message(asmr_e_invalid_reference_syntax);
                GotStar:=false;
                GotPlus:=false;
                if (actasmtoken = AS_VMTOFFSET) or
                   (SearchIConstant(actasmpattern,l) or
                    SearchRecordType(actasmpattern)) then
                 begin
                   l:=BuildRefConstExpression;
                   GotPlus:=(prevasmtoken=AS_PLUS);
                   GotStar:=(prevasmtoken=AS_STAR);
                   case oper.opr.typ of
                     OPR_LOCAL :
                       begin
                         if GotStar then
                           Message(asmr_e_invalid_reference_syntax);
                         if negative then
                           Dec(oper.opr.localsymofs,l)
                         else
                           Inc(oper.opr.localsymofs,l);
                       end;
                     OPR_REFERENCE :
                       begin
                         if GotStar then
                          oper.opr.ref.scalefactor:=l
                         else
                          begin
                            if negative then
                              Dec(oper.opr.ref.offset,l)
                            else
                              Inc(oper.opr.ref.offset,l);
                          end;
                        end;
                   end;
                 end
                else
                 Begin
                   if negative and not oper.hasvar then
                     Message(asmr_e_only_add_relocatable_symbol)
                   else if oper.hasvar and not GotOffset and
                           (not negative or assigned(oper.opr.ref.relsymbol)) then
                     Message(asmr_e_cant_have_multiple_relocatable_symbols);
                   HadVar:=oper.hasvar and GotOffset;
                   tempstr:=actasmpattern;
                   Consume(AS_ID);
                   { typecasting? }
                   if (actasmtoken=AS_LPAREN) and
                      SearchType(tempstr,l) then
                    begin
                      oper.hastype:=true;
                      oper.typesize:=l;
                      Consume(AS_LPAREN);
                      BuildOperand(oper,true);
                      Consume(AS_RPAREN);
                    end
                   else
                    if is_locallabel(tempstr) then
                      begin
                        CreateLocalLabel(tempstr,hl,false);
                        oper.InitRef;
                        if not negative then
                          begin
                            oper.opr.ref.symbol:=hl;
                            oper.hasvar:=true;
                          end
                        else
                          oper.opr.ref.relsymbol:=hl;
                      end
                   else
                    if oper.SetupVar(tempstr,GotOffset) then
                     begin
                       { force OPR_LOCAL to be a reference }
                       if oper.opr.typ=OPR_LOCAL then
                         oper.opr.localforceref:=true;
                     end
                   else
                     Message1(sym_e_unknown_id,tempstr);
                   { record.field ? }
                   if actasmtoken=AS_DOT then
                    begin
                      BuildRecordOffsetSize(tempstr,l,k,hs,false);
                      if (hs<>'') then
                        Message(asmr_e_invalid_symbol_ref);
                      case oper.opr.typ of
                        OPR_LOCAL :
                          inc(oper.opr.localsymofs,l);
                        OPR_REFERENCE :
                          inc(oper.opr.ref.offset,l);
                      end;
                    end;
                   if GotOffset then
                    begin
                      if oper.hasvar and (oper.opr.ref.base=current_procinfo.framepointer) then
                       begin
                         if (oper.opr.typ=OPR_REFERENCE) then
                           oper.opr.ref.base:=NR_NO;
                         oper.hasvar:=hadvar;
                       end
                      else
                       begin
                         if oper.hasvar and hadvar then
                          Message(asmr_e_cant_have_multiple_relocatable_symbols);
                         { should we allow ?? }
                       end;
                    end;
                 end;
                GotOffset:=false;
              end;

            AS_PLUS :
              Begin
                Consume(AS_PLUS);
                Negative:=false;
                GotPlus:=true;
                GotStar:=false;
                Scale:=0;
              end;

            AS_DOT :
              Begin
                { Handle like a + }
                Consume(AS_DOT);
                Negative:=false;
                GotPlus:=true;
                GotStar:=false;
                Scale:=0;
              end;

            AS_MINUS :
              begin
                Consume(AS_MINUS);
                Negative:=true;
                GotPlus:=true;
                GotStar:=false;
                Scale:=0;
              end;

            AS_STAR : { Scaling, with eax*4 order }
              begin
                Consume(AS_STAR);
                hs:='';
                l:=0;
                case actasmtoken of
                  AS_LPAREN :
                    l:=BuildConstExpression;
                  AS_INTNUM:
                    Begin
                      hs:=actasmpattern;
                      Consume(AS_INTNUM);
                    end;
                  AS_REGISTER :
                    begin
                      case oper.opr.typ of
                        OPR_REFERENCE :
                          begin
                            if oper.opr.ref.scalefactor=0 then
                              begin
                                if scale<>0 then
                                  begin
                                    oper.opr.ref.scalefactor:=scale;
                                    scale:=0;
                                  end
                                else
                                 Message(asmr_e_wrong_scale_factor);
                              end
                            else
                              Message(asmr_e_invalid_reference_syntax);
                          end;
                        OPR_LOCAL :
                          begin
                            if oper.opr.localscale=0 then
                              begin
                                if scale<>0 then
                                  begin
                                    oper.opr.localscale:=scale;
                                    scale:=0;
                                  end
                                else
                                 Message(asmr_e_wrong_scale_factor);
                              end
                            else
                              Message(asmr_e_invalid_reference_syntax);
                          end;
                      end;
                    end;
                  else
                    Message(asmr_e_invalid_reference_syntax);
                end;
                if actasmtoken<>AS_REGISTER then
                  begin
                    if hs<>'' then
                      val(hs,l,code);
                    case oper.opr.typ of
                      OPR_REFERENCE :
                        oper.opr.ref.scalefactor:=l;
                      OPR_LOCAL :
                        oper.opr.localscale:=l;
                    end;
                    if l>9 then
                      Message(asmr_e_wrong_scale_factor);
                  end;
                GotPlus:=false;
                GotStar:=false;
              end;

            AS_REGISTER :
              begin
                if not((GotPlus and (not Negative)) or
                       GotStar) then
                  Message(asmr_e_invalid_reference_syntax);
                hreg:=actasmregister;
                Consume(AS_REGISTER);
                { this register will be the index:
                   1. just read a *
                   2. next token is a *
                   3. base register is already used }
                case oper.opr.typ of
                  OPR_LOCAL :
                    begin
                      if (oper.opr.localindexreg<>NR_NO) then
                        Message(asmr_e_multiple_index);
                      oper.opr.localindexreg:=hreg;
                      if scale<>0 then
                        begin
                          oper.opr.localscale:=scale;
                          scale:=0;
                        end;
                    end;
                  OPR_REFERENCE :
                    begin
                      if (GotStar) or
                         (actasmtoken=AS_STAR) or
                         (oper.opr.ref.base<>NR_NO) then
                       begin
                         if (oper.opr.ref.index<>NR_NO) then
                          Message(asmr_e_multiple_index);
                         oper.opr.ref.index:=hreg;
                         if scale<>0 then
                           begin
                             oper.opr.ref.scalefactor:=scale;
                             scale:=0;
                           end;
                       end
                      else
                       oper.opr.ref.base:=hreg;
                    end;
                end;
                GotPlus:=false;
                GotStar:=false;
              end;

            AS_OFFSET :
              begin
                Consume(AS_OFFSET);
                GotOffset:=true;
              end;

            AS_TYPE,
            AS_NOT,
            AS_STRING,
            AS_INTNUM,
            AS_LPAREN : { Constant reference expression }
              begin
                if not GotPlus and not GotStar then
                  Message(asmr_e_invalid_reference_syntax);
                BuildConstSymbolExpression(true,true,GotPlus and negative,l,tempstr,tempsymtyp);
                { already handled by BuildConstSymbolExpression(); must be
                  handled there to avoid [reg-1+1] being interpreted as
                  [reg-(1+1)] }
                negative:=false;

                if tempstr<>'' then
                 begin
                   if GotStar then
                    Message(asmr_e_only_add_relocatable_symbol);
                   if not assigned(oper.opr.ref.symbol) then
                    oper.opr.ref.symbol:=current_asmdata.RefAsmSymbol(tempstr)
                   else
                    Message(asmr_e_cant_have_multiple_relocatable_symbols);
                 end;
                case oper.opr.typ of
                  OPR_REFERENCE :
                    begin
                      if GotStar then
                       oper.opr.ref.scalefactor:=l
                      else if (prevasmtoken = AS_STAR) then
                       begin
                         if scale<>0 then
                           scale:=l*scale
                         else
                           scale:=l;
                       end
                      else
                       Inc(oper.opr.ref.offset,l);
                    end;
                  OPR_LOCAL :
                    begin
                      if GotStar then
                       oper.opr.localscale:=l
                      else if (prevasmtoken = AS_STAR) then
                       begin
                         if scale<>0 then
                           scale:=l*scale
                         else
                           scale:=l;
                       end
                      else
                        Inc(oper.opr.localsymofs,l);
                    end;
                end;
                GotPlus:=(prevasmtoken=AS_PLUS) or
                         (prevasmtoken=AS_MINUS);
                if GotPlus then
                  negative := prevasmtoken = AS_MINUS;
                GotStar:=(prevasmtoken=AS_STAR);
              end;

            AS_RBRACKET :
              begin
                if GotPlus or GotStar then
                  Message(asmr_e_invalid_reference_syntax);
                Consume(AS_RBRACKET);
                break;
              end;

            else
              Begin
                Message(asmr_e_invalid_reference_syntax);
                RecoverConsume(true);
                break;
              end;
          end;
        until false;
      end;


    Procedure tx86intreader.BuildConstantOperand(oper: tx86operand);
      var
        l : aint;
        tempstr : string;
        tempsymtyp : tasmsymtype;
      begin
        if not (oper.opr.typ in [OPR_NONE,OPR_CONSTANT]) then
          Message(asmr_e_invalid_operand_type);
        BuildConstSymbolExpression(true,false,false,l,tempstr,tempsymtyp);
        if tempstr<>'' then
          begin
            oper.opr.typ:=OPR_SYMBOL;
            oper.opr.symofs:=l;
            oper.opr.symbol:=current_asmdata.RefAsmSymbol(tempstr);
          end
        else
          if oper.opr.typ=OPR_NONE then
            begin
              oper.opr.typ:=OPR_CONSTANT;
              oper.opr.val:=l;
            end
          else
            inc(oper.opr.val,l);
      end;


    Procedure tx86intreader.BuildOperand(oper: tx86operand;istypecast:boolean);

        procedure AddLabelOperand(hl:tasmlabel);
        begin
          if (oper.opr.typ=OPR_NONE) and
             is_calljmp(actopcode) then
           begin
             oper.opr.typ:=OPR_SYMBOL;
             oper.opr.symbol:=hl;
           end
          else
           begin
             oper.InitRef;
             oper.opr.ref.symbol:=hl;
           end;
        end;

      var
        expr,
        hs      : string;
        tempreg : tregister;
        l       : aint;
        hl      : tasmlabel;
        toffset,
        tsize   : aint;
      begin
        expr:='';
        repeat
          if actasmtoken=AS_DOT then
            begin
              if expr<>'' then
                begin
                  BuildRecordOffsetSize(expr,toffset,tsize,hs,false);
                  if (oper.opr.typ<>OPR_NONE) and
                     (hs<>'') then
                    Message(asmr_e_wrong_sym_type);
                  oper.SetSize(tsize,true);
                  { we have used the size of a field. Reset the typesize of the record }
                  oper.typesize:=0;
                  case oper.opr.typ of
                    OPR_LOCAL :
                      begin
                        { don't allow direct access to fields of parameters, because that
                          will generate buggy code. Allow it only for explicit typecasting
                          and when the parameter is in a register (delphi compatible) }
                        if (not oper.hastype) and
                           (oper.opr.localsym.owner.symtabletype=parasymtable) and
                           (current_procinfo.procdef.proccalloption<>pocall_register) then
                          Message(asmr_e_cannot_access_field_directly_for_parameters);
                        inc(oper.opr.localsymofs,toffset)
                      end;
                    OPR_CONSTANT :
                      inc(oper.opr.val,toffset);
                    OPR_REFERENCE :
                      inc(oper.opr.ref.offset,toffset);
                    OPR_NONE :
                      begin
                        if (hs <> '') then
                          begin
                            oper.opr.typ:=OPR_SYMBOL;
                            oper.opr.symbol:=current_asmdata.RefAsmSymbol(hs);
                          end
                        else
                          begin
                            oper.opr.typ:=OPR_CONSTANT;
                            oper.opr.val:=toffset;
                          end;
                      end;
                    OPR_REGISTER :
                      Message(asmr_e_invalid_reference_syntax);
                    OPR_SYMBOL:
                      Message(asmr_e_invalid_symbol_ref);
                    else
                      internalerror(200309222);
                  end;
                  expr:='';
                end
              else
                begin
                  { See it as a separator }
                  Consume(AS_DOT);
                end;
           end;

          case actasmtoken of
            AS_OFFSET,
            AS_SIZEOF,
            AS_VMTOFFSET,
            AS_TYPE,
            AS_NOT,
            AS_STRING,
            AS_PLUS,
            AS_MINUS,
            AS_LPAREN,
            AS_INTNUM :
              begin
                case oper.opr.typ of
                  OPR_REFERENCE :
                    if (actasmtoken=AS_OFFSET) and
                       (cs_create_pic in current_settings.moduleswitches) then
                      begin
                        Consume(AS_OFFSET);
                        oper.opr.ref.refaddr:=addr_pic;
                        BuildOperand(oper,false);
                      end
                    else
                      inc(oper.opr.ref.offset,BuildRefConstExpression);
                  OPR_LOCAL :
                    inc(oper.opr.localsymofs,BuildConstExpression);
                  OPR_NONE,
                  OPR_CONSTANT :
                    BuildConstantOperand(oper);
                  else
                    Message(asmr_e_invalid_operand_type);
                end;
              end;

            AS_PTR :
              begin
                if not oper.hastype then
                  begin
                    if (oper.opr.typ=OPR_CONSTANT) then
                      begin
                        oper.typesize:=oper.opr.val;
                        { reset constant value of operand }
                        oper.opr.typ:=OPR_NONE;
                        oper.opr.val:=0;
                      end
                    else
                      Message(asmr_e_syn_operand);
                  end;
                Consume(AS_PTR);
                oper.InitRef;
                { if the operand subscripts a record, the typesize will be
                  rest -> save it here and restore it afterwards }
                l:=oper.typesize;
                BuildOperand(oper,false);
                oper.setsize(l,true);
              end;

            AS_ID : { A constant expression, or a Variable ref. }
              Begin
                { Label or Special symbol reference? }
                if actasmpattern[1] = '@' then
                 Begin
                   if actasmpattern = '@RESULT' then
                    Begin
                      oper.SetupResult;
                      Consume(AS_ID);
                    end
                   else
                    if (actasmpattern = '@CODE') or (actasmpattern = '@DATA') then
                     begin
                       Message(asmr_w_CODE_and_DATA_not_supported);
                       Consume(AS_ID);
                     end
                   else
                    { Local Label }
                    begin
                      CreateLocalLabel(actasmpattern,hl,false);
                      Consume(AS_ID);
                      AddLabelOperand(hl);
                    end;
                 end
                else
                { support result for delphi modes }
                 if (m_objpas in current_settings.modeswitches) and (actasmpattern='RESULT') then
                  begin
                    oper.SetUpResult;
                    Consume(AS_ID);
                  end
                { probably a variable or normal expression }
                { or a procedure (such as in CALL ID)      }
                else
                 Begin
                   { is it a constant ? }
                   if SearchIConstant(actasmpattern,l) then
                    Begin
                      case oper.opr.typ of
                        OPR_REFERENCE :
                          inc(oper.opr.ref.offset,BuildRefConstExpression);
                        OPR_LOCAL :
                          inc(oper.opr.localsymofs,BuildRefConstExpression);
                        OPR_NONE,
                        OPR_CONSTANT :
                          BuildConstantOperand(oper);
                        else
                          Message(asmr_e_invalid_operand_type);
                      end;
                    end
                   else
                    { Check for pascal label }
                    if SearchLabel(actasmpattern,hl,false) then
                     begin
                       Consume(AS_ID);
                       AddLabelOperand(hl);
                     end
                    else
                    { is it a normal variable ? }
                     Begin
                       expr:=actasmpattern;
                       Consume(AS_ID);
                       { typecasting? }
                       if SearchType(expr,l) then
                        begin
                          oper.hastype:=true;
                          oper.typesize:=l;
                          case actasmtoken of
                            AS_LPAREN :
                              begin
                                { Support Type([Reference]) }
                                Consume(AS_LPAREN);
                                BuildOperand(oper,true);
                                { Delphi also supports Type(Register) and
                                  interprets it the same as Type([Register]).  }
                                if (oper.opr.typ = OPR_REGISTER) then
                                  { This also sets base to the register.  }
                                  oper.InitRef;
                                Consume(AS_RPAREN);
                              end;
                            AS_LBRACKET :
                              begin
                                { Support Var.Type[Index] }
                                { Convert @label.Byte[1] to reference }
                                if oper.opr.typ=OPR_SYMBOL then
                                  oper.initref;
                              end;
                          end;
                        end
                       else
                        begin
                          if not oper.SetupVar(expr,false) then
                            Begin
                              { not a variable, check special variables.. }
                              if expr = 'SELF' then
                                oper.SetupSelf
                              else
                                Message1(sym_e_unknown_id,expr);
                              expr:='';
                            end;
                          { indexed access to variable? }
                          if actasmtoken=AS_LBRACKET then
                            begin
                              { ... then the operand size is not known anymore }
                              oper.size:=OS_NO;
                              BuildReference(oper);
                            end;
                        end;
                     end;
                 end;
              end;

            AS_REGISTER : { Register, a variable reference or a constant reference }
              begin
                { save the type of register used. }
                tempreg:=actasmregister;
                Consume(AS_REGISTER);
                if actasmtoken = AS_COLON then
                 Begin
                   Consume(AS_COLON);
                   oper.InitRef;
                   oper.opr.ref.segment:=tempreg;
                   BuildReference(oper);
                 end
                else
                { Simple register }
                 begin
                   if (oper.opr.typ <> OPR_NONE) then
                     Message(asmr_e_syn_operand);
                   oper.opr.typ:=OPR_REGISTER;
                   oper.opr.reg:=tempreg;
                   oper.SetSize(tcgsize2size[reg_cgsize(oper.opr.reg)],true);
                 end;
              end;

            AS_LBRACKET: { a variable reference, register ref. or a constant reference }
              Begin
                BuildReference(oper);
              end;

            AS_SEG :
              Begin
                Message(asmr_e_seg_not_supported);
                Consume(actasmtoken);
              end;

            AS_DWORD,
            AS_BYTE,
            AS_WORD,
            AS_TBYTE,
            AS_DQWORD,
            AS_QWORD :
              begin
                { Type specifier }
                oper.hastype:=true;
                oper.typesize:=0;
                case actasmtoken of
                  AS_DWORD : oper.typesize:=4;
                  AS_WORD  : oper.typesize:=2;
                  AS_BYTE  : oper.typesize:=1;
                  AS_QWORD : oper.typesize:=8;
                  AS_DQWORD : oper.typesize:=16;
                  AS_TBYTE : oper.typesize:=10;
                  else
                    internalerror(2010061101);
                end;
                Consume(actasmtoken);
                if (actasmtoken=AS_LPAREN) then
                  begin
                    { Support "xxx ptr [Reference]" }
                    { in case the expression subscripts a record, the typesize
                      is reset, so save the explicit size we set above }
                    l:=oper.typesize;
                    Consume(AS_LPAREN);
                    BuildOperand(oper,true);
                    Consume(AS_RPAREN);
                    oper.setsize(l,true);
                  end;
              end;

            AS_SEPARATOR,
            AS_END,
            AS_COMMA,
            AS_COLON:
              begin
                break;
              end;

            AS_RPAREN:
              begin
                if not istypecast then
                  begin
                    Message(asmr_e_syn_operand);
                    Consume(AS_RPAREN);
                  end
                else
                  break;
              end;

            else
              begin
                Message(asmr_e_syn_operand);
                RecoverConsume(true);
                break;
              end;
          end;
        until false;
        { End of operand, update size if a typecast is forced }
        if (oper.typesize<>0) and
           (oper.opr.typ in [OPR_REFERENCE,OPR_LOCAL]) then
          oper.SetSize(oper.typesize,true);
      end;


    Procedure tx86intreader.BuildOpCode(instr : tx86instruction);
      var
        PrefixOp,OverrideOp: tasmop;
        operandnum : longint;
        is_far_const:boolean;
        i:byte;
      begin
        PrefixOp:=A_None;
        OverrideOp:=A_None;
        is_far_const:=false;
        { prefix seg opcode / prefix opcode }
        repeat
          if is_prefix(actopcode) then
            with instr do
              begin
                OpOrder:=op_intel;
                PrefixOp:=ActOpcode;
                opcode:=ActOpcode;
                condition:=ActCondition;
                opsize:=ActOpsize;
                ConcatInstruction(curlist);
                consume(AS_OPCODE);
              end
          else
           if is_override(actopcode) then
             with instr do
               begin
                 OpOrder:=op_intel;
                 OverrideOp:=ActOpcode;
                 opcode:=ActOpcode;
                 condition:=ActCondition;
                 opsize:=ActOpsize;
                 ConcatInstruction(curlist);
                 consume(AS_OPCODE);
               end
          else
            break;
          { allow for newline after prefix or override }
          while actasmtoken=AS_SEPARATOR do
            consume(AS_SEPARATOR);
        until (actasmtoken<>AS_OPCODE);
        { opcode }
        if (actasmtoken <> AS_OPCODE) then
         begin
           Message(asmr_e_invalid_or_missing_opcode);
           RecoverConsume(false);
           exit;
         end;
        { Fill the instr object with the current state }
        with instr do
          begin
            OpOrder:=op_intel;
            Opcode:=ActOpcode;
            condition:=ActCondition;
            opsize:=ActOpsize;

            { Valid combination of prefix/override and instruction ?  }
            if (prefixop<>A_NONE) and (NOT CheckPrefix(PrefixOp,actopcode)) then
              Message1(asmr_e_invalid_prefix_and_opcode,actasmpattern);
            if (overrideop<>A_NONE) and (NOT CheckOverride(OverrideOp,ActOpcode)) then
              Message1(asmr_e_invalid_override_and_opcode,actasmpattern);
          end;
        { pushf/popf/pusha/popa have to default to 16 bit in Intel mode
          (Intel manual and Delphi-compatbile) -- setting the opsize for
          these instructions doesn't change anything in the internal assember,
          so change the opcode }
        if (instr.opcode=A_POPF) then
          instr.opcode:=A_POPFW
        else if (instr.opcode=A_PUSHF) then
          instr.opcode:=A_PUSHFW
        else if (instr.opcode=A_PUSHA) then
          instr.opcode:=A_PUSHAW
        else if (instr.opcode=A_POPA) then
          instr.opcode:=A_POPAW;
        { We are reading operands, so opcode will be an AS_ID }
        operandnum:=1;
        is_far_const:=false;
        Consume(AS_OPCODE);
        { Zero operand opcode ?  }
        if actasmtoken in [AS_SEPARATOR,AS_END] then
         begin
           operandnum:=0;
           exit;
         end;
        { Read Operands }
        repeat
          case actasmtoken of
            { End of asm operands for this opcode }
            AS_END,
            AS_SEPARATOR :
              break;

            { Operand delimiter }
            AS_COMMA :
              begin
                if operandnum > Max_Operands then
                  Message(asmr_e_too_many_operands)
                else
                  Inc(operandnum);
                Consume(AS_COMMA);
              end;

            {Far constant, i.e. jmp $0000:$11111111.}
            AS_COLON:
              begin
                is_far_const:=true;
                if operandnum>1 then
                  message(asmr_e_too_many_operands)
                else
                  inc(operandnum);
                consume(AS_COLON);
              end;

            { Type specifier }
            AS_NEAR,
            AS_FAR :
              begin
                if actasmtoken = AS_NEAR then
                  begin
                    Message(asmr_w_near_ignored);
                    instr.opsize:=S_NEAR;
                  end
                else
                  begin
                    Message(asmr_w_far_ignored);
                    instr.opsize:=S_FAR;
                  end;
                Consume(actasmtoken);
                if actasmtoken=AS_PTR then
                 begin
                   Consume(AS_PTR);
                   instr.Operands[operandnum].InitRef;
                 end;
                BuildOperand(instr.Operands[operandnum] as tx86operand,false);
              end;
            else
              BuildOperand(instr.Operands[operandnum] as tx86operand,false);
          end; { end case }
        until false;
        instr.ops:=operandnum;
        { Check operands }
        for i:=1 to operandnum do
          begin
            if is_far_const and
               (instr.operands[i].opr.typ<>OPR_CONSTANT) then
              message(asmr_e_expr_illegal)
            else
              if instr.operands[i].opr.typ=OPR_NONE then
                Message(asmr_e_syntax_error);
          end;
        { e.g. for "push dword 1", "push word 6" }
        if (instr.ops=1) and
           (instr.operands[1].typesize<>0) then
          instr.operands[1].setsize(instr.operands[1].typesize,false);
      end;


    Procedure tx86intreader.BuildConstant(constsize: byte);
      var
        asmsymtyp : tasmsymtype;
        asmsym,
        expr: string;
        value : aint;
      Begin
        Repeat
          Case actasmtoken of
            AS_STRING:
              Begin
                { DD and DW cases }
                if constsize <> 1 then
                 Begin
                   if Not PadZero(actasmpattern,constsize) then
                    Message(scan_f_string_exceeds_line);
                 end;
                expr:=actasmpattern;
                Consume(AS_STRING);
                Case actasmtoken of
                  AS_COMMA:
                    Consume(AS_COMMA);
                  AS_END,
                  AS_SEPARATOR: ;
                  else
                    Message(asmr_e_invalid_string_expression);
                end;
                ConcatString(curlist,expr);
              end;
            AS_PLUS,
            AS_MINUS,
            AS_LPAREN,
            AS_NOT,
            AS_INTNUM,
            AS_ID :
              Begin
                BuildConstSymbolExpression(false,false,false,value,asmsym,asmsymtyp);
                if asmsym<>'' then
                 begin
                   if constsize<>sizeof(pint) then
                     Message1(asmr_w_const32bit_for_address,asmsym);
                   ConcatConstSymbol(curlist,asmsym,asmsymtyp,value)
                 end
                else
                 ConcatConstant(curlist,value,constsize);
              end;
            AS_COMMA:
              begin
                Consume(AS_COMMA);
              end;
            AS_ALIGN,
            AS_DB,
            AS_DW,
            AS_DD,
            AS_DQ,
            AS_OPCODE,
            AS_END,
            AS_SEPARATOR:
              break;
            else
              begin
                Message(asmr_e_syn_constant);
                RecoverConsume(false);
              end
          end;
        Until false;
      end;


  function tx86intreader.Assemble: tlinkedlist;
    Var
      hl : tasmlabel;
      instr : Tx86Instruction;
    Begin
      Message1(asmr_d_start_reading,'intel');
      inexpression:=FALSE;
      firsttoken:=TRUE;
     { sets up all opcode and register tables in uppercase
       done in the construtor now
      if not _asmsorted then
       Begin
         SetupTables;
         _asmsorted:=TRUE;
       end;
      }
      curlist:=TAsmList.Create;
      { setup label linked list }
      LocalLabelList:=TLocalLabelList.Create;
      { we might need to know which parameters are passed in registers }
      current_procinfo.generate_parameter_info;
      { start tokenizer }
      c:=current_scanner.asmgetcharstart;
      gettoken;
      { main loop }
      repeat
        case actasmtoken of
          AS_LLABEL:
            Begin
              if CreateLocalLabel(actasmpattern,hl,true) then
                ConcatLabel(curlist,hl);
              Consume(AS_LLABEL);
            end;

          AS_LABEL:
            Begin
              if SearchLabel(upper(actasmpattern),hl,true) then
               ConcatLabel(curlist,hl)
              else
               Message1(asmr_e_unknown_label_identifier,actasmpattern);
              Consume(AS_LABEL);
            end;

          AS_DW :
            Begin
              inexpression:=true;
              Consume(AS_DW);
              BuildConstant(2);
              inexpression:=false;
            end;

          AS_DB :
            Begin
              inexpression:=true;
              Consume(AS_DB);
              BuildConstant(1);
              inexpression:=false;
            end;

          AS_DD :
            Begin
              inexpression:=true;
              Consume(AS_DD);
              BuildConstant(4);
              inexpression:=false;
            end;

{$ifdef cpu64bitaddr}
          AS_DQ:
            Begin
              inexpression:=true;
              Consume(AS_DQ);
              BuildConstant(8);
              inexpression:=false;
            end;
{$endif cpu64bitaddr}

          AS_ALIGN:
            Begin
              Consume(AS_ALIGN);
              ConcatAlign(curlist,BuildConstExpression);
              if actasmtoken<>AS_SEPARATOR then
                Consume(AS_SEPARATOR);
            end;

          AS_OPCODE :
            Begin
              instr:=Tx86Instruction.Create(Tx86Operand);
              BuildOpcode(instr);
              with instr do
                begin
                  { We need AT&T style operands }
                  Swapoperands;
                  { Must be done with args in ATT order }
                  CheckNonCommutativeOpcodes;
                  AddReferenceSizes;
                  SetInstructionOpsize;
                  CheckOperandSizes;
                  ConcatInstruction(curlist);
                end;
              instr.Free;
            end;

          AS_SEPARATOR :
            Begin
              Consume(AS_SEPARATOR);
            end;

          AS_END :
            break; { end assembly block }

          else
            Begin
              Message(asmr_e_syntax_error);
              RecoverConsume(false);
            end;
        end; { end case }
      until false;
      { Check LocalLabelList }
      LocalLabelList.CheckEmitted;
      LocalLabelList.Free;
      { Return the list in an asmnode }
      assemble:=curlist;
      Message1(asmr_d_finish_reading,'intel');
    end;


end.
