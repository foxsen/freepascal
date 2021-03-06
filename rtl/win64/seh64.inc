{
    This file is part of the Free Pascal run time library.
    Copyright (c) 2011 by Free Pascal development team

    Support for 64-bit Windows exception handling

    See the file COPYING.FPC, included in this distribution,
    for details about the copyright.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

 **********************************************************************}

{ exception flags }
const
  EXCEPTION_NONCONTINUABLE  = $01;
  EXCEPTION_UNWINDING       = $02;
  EXCEPTION_EXIT_UNWIND     = $04;
  EXCEPTION_STACK_INVALID   = $08;
  EXCEPTION_NESTED_CALL     = $10;
  EXCEPTION_TARGET_UNWIND   = $20;
  EXCEPTION_COLLIDED_UNWIND = $40;
  EXCEPTION_UNWIND          = $66;

  UNWIND_HISTORY_TABLE_SIZE = 12;

  UNW_FLAG_NHANDLER         = 0;

type
  PM128A=^M128A;
  M128A = record
    Low : QWord;
    High : Int64;
  end;

  PContext = ^TContext;
  TContext = record
    P1Home : QWord;
    P2Home : QWord;
    P3Home : QWord;
    P4Home : QWord;
    P5Home : QWord;
    P6Home : QWord;
    ContextFlags : DWord;
    MxCsr : DWord;
    SegCs : word;
    SegDs : word;
    SegEs : word;
    SegFs : word;
    SegGs : word;
    SegSs : word;
    EFlags : DWord;
    Dr0 : QWord;
    Dr1 : QWord;
    Dr2 : QWord;
    Dr3 : QWord;
    Dr6 : QWord;
    Dr7 : QWord;
    Rax : QWord;
    Rcx : QWord;
    Rdx : QWord;
    Rbx : QWord;
    Rsp : QWord;
    Rbp : QWord;
    Rsi : QWord;
    Rdi : QWord;
    R8 : QWord;
    R9 : QWord;
    R10 : QWord;
    R11 : QWord;
    R12 : QWord;
    R13 : QWord;
    R14 : QWord;
    R15 : QWord;
    Rip : QWord;
    Header : array[0..1] of M128A;
    Legacy : array[0..7] of M128A;
    Xmm0 : M128A;
    Xmm1 : M128A;
    Xmm2 : M128A;
    Xmm3 : M128A;
    Xmm4 : M128A;
    Xmm5 : M128A;
    Xmm6 : M128A;
    Xmm7 : M128A;
    Xmm8 : M128A;
    Xmm9 : M128A;
    Xmm10 : M128A;
    Xmm11 : M128A;
    Xmm12 : M128A;
    Xmm13 : M128A;
    Xmm14 : M128A;
    Xmm15 : M128A;
    VectorRegister : array[0..25] of M128A;
    VectorControl : QWord;
    DebugControl : QWord;
    LastBranchToRip : QWord;
    LastBranchFromRip : QWord;
    LastExceptionToRip : QWord;
    LastExceptionFromRip : QWord;
  end;

  { This is a simplified definition, only array part of unions }
  PKNONVOLATILE_CONTEXT_POINTERS=^KNONVOLATILE_CONTEXT_POINTERS;
  KNONVOLATILE_CONTEXT_POINTERS=record
    FloatingContext: array[0..15] of PM128A;
    IntegerContext: array[0..15] of PQWord;
  end;

  EXCEPTION_DISPOSITION=(
    ExceptionContinueExecution,
    ExceptionContinueSearch,
    ExceptionNestedException,
    ExceptionCollidedUnwind
  );

  PExceptionPointers = ^TExceptionPointers;
  TExceptionPointers = record
    ExceptionRecord   : PExceptionRecord;
    ContextRecord     : PContext;
  end;


  EXCEPTION_ROUTINE = function(
    var ExceptionRecord: TExceptionRecord;
    EstablisherFrame: Pointer;
    var ContextRecord: TContext;
    DispatcherContext: Pointer ): EXCEPTION_DISPOSITION;

  PRUNTIME_FUNCTION=^RUNTIME_FUNCTION;
  RUNTIME_FUNCTION=record
    BeginAddress: DWORD;
    EndAddress: DWORD;
    UnwindData: DWORD;
  end;

  UNWIND_HISTORY_TABLE_ENTRY=record
    ImageBase: QWord;
    FunctionEntry: PRUNTIME_FUNCTION;
  end;

  PUNWIND_HISTORY_TABLE=^UNWIND_HISTORY_TABLE;
  UNWIND_HISTORY_TABLE=record
    Count: DWORD;
    Search: Byte;
    RaiseStatusIndex: Byte;
    Unwind: Byte;
    Exception: Byte;
    LowAddress: QWord;
    HighAddress: QWord;
    Entry: array[0..UNWIND_HISTORY_TABLE_SIZE-1] of UNWIND_HISTORY_TABLE_ENTRY;
  end;

  PDispatcherContext = ^TDispatcherContext;
  TDispatcherContext = record
    ControlPc: QWord;
    ImageBase: QWord;
    FunctionEntry: PRUNTIME_FUNCTION;
    EstablisherFrame: QWord;
    TargetIp: QWord;
    ContextRecord: PContext;
    LanguageHandler: EXCEPTION_ROUTINE;
    HandlerData: Pointer;
    HistoryTable: PUNWIND_HISTORY_TABLE;
    ScopeIndex: DWord;
    Fill0: DWord;
  end;

procedure RtlCaptureContext(var ctx: TContext); stdcall;
  external 'kernel32.dll' name 'RtlCaptureContext';

function RtlCaptureStackBackTrace(
  FramesToSkip: DWORD;
  FramesToCapture: DWORD;
  var BackTrace: Pointer;
  BackTraceHash: PDWORD): Word; stdcall;
  external 'kernel32.dll' name 'RtlCaptureStackBackTrace';

function RtlLookupFunctionEntry(
  ControlPC: QWord;
  out ImageBase: QWord;
  HistoryTable: PUNWIND_HISTORY_TABLE): PRUNTIME_FUNCTION;
  external 'kernel32.dll' name 'RtlLookupFunctionEntry';

function RtlVirtualUnwind(
  HandlerType: DWORD;
  ImageBase: QWord;
  ControlPc: QWord;
  FunctionEntry: PRUNTIME_FUNCTION;
  var ContextRecord: TContext;
  HandlerData: PPointer;
  EstablisherFrame: PQWord;
  ContextPointers: PKNONVOLATILE_CONTEXT_POINTERS): EXCEPTION_ROUTINE;
  external 'kernel32.dll' name 'RtlVirtualUnwind';

procedure RtlUnwindEx(
  TargetFrame: Pointer;
  TargetIp: Pointer;
  ExceptionRecord: PExceptionRecord;
  ReturnValue: Pointer;
  OriginalContext: PContext;  { scratch space, initial contents ignored }
  HistoryTable: PUNWIND_HISTORY_TABLE);
  external 'kernel32.dll' name 'RtlUnwindEx';

procedure RaiseException(
  dwExceptionCode: DWORD;
  dwExceptionFlags: DWORD;
  dwArgCount: DWORD;
  lpArguments: Pointer);  // msdn: *ULONG_PTR
  external 'kernel32.dll' name 'RaiseException';

{ FPC specific stuff }
{$ifdef FPC_USE_WIN64_SEH}
const
  FPC_EXCEPTION_CODE=$E0465043;
  SCOPE_FINALLY=0;
  SCOPE_CATCHALL=1;
  SCOPE_IMPLICIT=2;

type
  PScopeRec=^TScopeRec;
  TScopeRec=record
    Typ: DWord;        { SCOPE_FINALLY: finally code in RvaHandler
                         SCOPE_CATCHALL: unwinds to RvaEnd, RvaHandler is the end of except block
                         SCOPE_IMPLICIT: finally code in RvaHandler, unwinds to RvaEnd
                         otherwise: except with 'on' stmts, value is RVA of filter data }
    RvaStart: DWord;
    RvaEnd: DWord;
    RvaHandler: DWord;
  end;

  PFilterRec=^TFilterRec;
  TFilterRec=record
    RvaClass: DWord;
    RvaHandler: DWord;
  end;

  TUnwindProc=procedure(frame: QWord);
  TExceptObjProc=function(code: Longint; const rec: TExceptionRecord): Pointer; { Exception }
  TExceptClsProc=function(code: Longint): Pointer; { ExceptClass }

{ note: context must be passed by value, so modifications are made to a local copy }
function GetBacktrace(Context: TContext; StartingFrame: Pointer; out Frames: PPointer): Longint;
var
  UnwindHistory: UNWIND_HISTORY_TABLE;
  RuntimeFunction: PRUNTIME_FUNCTION;
  HandlerData: Pointer;
  EstablisherFrame: QWord;
  ImageBase: QWord;
  FrameCount,FrameBufSize: Longint;
begin
  FillChar(UnwindHistory,sizeof(UNWIND_HISTORY_TABLE),0);
  UnwindHistory.Unwind:=1;

  FrameCount:=0;
  FrameBufSize:=0;
  Frames:=nil;
  repeat
    RuntimeFunction:=RtlLookupFunctionEntry(Context.Rip, ImageBase, @UnwindHistory);

    if Assigned(RuntimeFunction) then
      RtlVirtualUnwind(UNW_FLAG_NHANDLER, ImageBase, Context.Rip,
        RuntimeFunction, Context, @HandlerData, @EstablisherFrame, nil)
    else  { a leaf function }
    begin
      Context.Rip:=PQWord(Context.Rsp)^;
      Inc(Context.Rsp, sizeof(Pointer));
    end;

    if (Context.Rip=0) or (FrameCount>=RaiseMaxFrameCount) then
      break;

    { The StartingFrame provides a way to skip several initial calls.
      It's better to specify the number of skipped calls directly,
      because the very purpose of this function is to retrieve stacktrace
      even in optimized code (i.e. without rbp-based frames). But that's
      limited by factors such as 'raise' syntax. }

    if (Pointer(Context.Rbp)>StartingFrame) or (FrameCount>0) then
    begin
      if (FrameCount>=FrameBufSize) then
        begin
          Inc(FrameBufSize,16);
          ReallocMem(Frames,FrameBufSize*sizeof(Pointer));
        end;
      Frames[FrameCount]:=Pointer(Context.Rip);
      Inc(FrameCount);
    end;
  until False;
  Result:=FrameCount;
end;

{$push}
{$codealign localmin=16}          { TContext record requires this }
function fpc_RaiseException(Obj: TObject; AnAddr,AFrame: Pointer): TObject; [public,alias: 'FPC_RAISEEXCEPTION']; compilerproc;
var
  ctx: TContext;
  args: array[0..3] of PtrUint;
begin
  RtlCaptureContext(ctx);
  args[0]:=PtrUint(AnAddr);
  args[1]:=PtrUint(Obj);
  args[2]:=GetBacktrace(ctx,AFrame,PPointer(args[3]));
  RaiseException(FPC_EXCEPTION_CODE,EXCEPTION_NONCONTINUABLE,4,@args[0]);
end;

procedure localUnwind(frame,target: Pointer);[public,alias:'_FPC_local_unwind'];
var
  ctx: TContext;
begin
  RtlUnwindEx(frame,target,nil,nil,@ctx,nil);
end;
{$pop}

procedure fpc_reraise; [public,alias:'FPC_RERAISE']; compilerproc;
var
  hp : PExceptObject;
  args: array[0..3] of PtrUint;
begin
  hp:=ExceptObjectStack;
  args[0]:=PtrUint(hp^.addr);               { copy and clear the exception stack top }
  args[1]:=PtrUint(hp^.FObject);
  args[2]:=hp^.FrameCount;
  args[3]:=PtrUint(hp^.Frames);
  hp^.refcount:=0;
  hp^.FObject:=nil;
  hp^.Frames:=nil;
  RaiseException(FPC_EXCEPTION_CODE,EXCEPTION_NONCONTINUABLE,4,@args[0]);
end;

{ The only difference from fpc_reraise is removing the topmost exception.
  Normally this is done in __FPC_specific_handler, but it won't work for implicit
  frames, as there's no room in scope record to store the end rva of 'except' part.

  This can only happen in functions which return managed result in register;
  eventually compiler must be fixed to return managed types in parameters only. }

procedure fpc_reraise_implicit; [public,alias:'FPC_RERAISE_IMPLICIT'];
var
  hp: PExceptObject;
  args: array[0..3] of PtrUInt;
begin
  hp:=ExceptObjectStack;
  args[0]:=PtrUint(hp^.addr);
  args[1]:=PtrUint(hp^.FObject);
  args[2]:=hp^.FrameCount;
  args[3]:=PtrUint(hp^.Frames);
  hp^.refcount:=0;
  hp^.FObject:=nil;
  hp^.Frames:=nil;
  Internal_PopObjectStack.Free;
  RaiseException(FPC_EXCEPTION_CODE,EXCEPTION_NONCONTINUABLE,4,@args[0]);
end;

function RunErrorCode(const rec: TExceptionRecord): longint;
begin
  { negative result means 'FPU reset required' }
  case rec.ExceptionCode of
    STATUS_INTEGER_DIVIDE_BY_ZERO:      result := 200;    { reDivByZero }
    STATUS_FLOAT_DIVIDE_BY_ZERO:        result := -208;   { !!reZeroDivide }
    STATUS_ARRAY_BOUNDS_EXCEEDED:       result := 201;    { reRangeError }
    STATUS_STACK_OVERFLOW:              result := 202;    { reStackOverflow }
    STATUS_FLOAT_OVERFLOW:              result := -205;   { reOverflow }
    STATUS_FLOAT_DENORMAL_OPERAND,
    STATUS_FLOAT_UNDERFLOW:             result := -206;   { reUnderflow }
    STATUS_FLOAT_INEXACT_RESULT,
    STATUS_FLOAT_INVALID_OPERATION,
    STATUS_FLOAT_STACK_CHECK:           result := -207;   { reInvalidOp }
    STATUS_INTEGER_OVERFLOW:            result := 215;    { reIntOverflow }
    STATUS_ILLEGAL_INSTRUCTION:         result := -216;
    STATUS_ACCESS_VIOLATION:            result := 216;    { reAccessViolation }
    STATUS_CONTROL_C_EXIT:              result := 217;    { reControlBreak }
    STATUS_PRIVILEGED_INSTRUCTION:      result := 218;    { rePrivilegedInstruction }
  else
    result := 255;                                        { reExternalException }
  end;
end;


function FilterException(var rec:TExceptionRecord; imagebase: QWord; scope: PScopeRec): Pointer;
var
  ExClass: TClass;
  i: Longint;
  Filter: Pointer;
  curFilt: PFilterRec;
begin
  result:=nil;
  if rec.ExceptionCode=FPC_EXCEPTION_CODE then
    ExClass:=TObject(rec.ExceptionInformation[1]).ClassType
  else if Assigned(ExceptClsProc) then
    ExClass:=TClass(TExceptClsProc(ExceptClsProc)(abs(RunErrorCode(rec))))
  else
    Exit; { if we cannot determine type of exception, don't handle it }
  Filter:=Pointer(imagebase+scope^.Typ);
  for i:=0 to PLongint(Filter)^-1 do
  begin
    CurFilt:=@PFilterRec(Filter+sizeof(Longint))[i];
    if (CurFilt^.RvaClass=$FFFFFFFF) or
      { TODO: exception might be coming from another module, need more advanced comparing }
      (ExClass.InheritsFrom(TClass(imagebase+CurFilt^.RvaClass))) then
    begin
      result:=Pointer(imagebase+CurFilt^.RvaHandler);
      exit;
    end;
  end;
end;

{$ifdef DEBUG_SEH}
procedure PrintScope(idx: integer; scope: PScopeRec);
begin
  if IsConsole then
  begin
    write(stderr,'Scope #',idx,' ',hexstr(Scope^.RvaStart,8),' - ',hexStr(Scope^.RvaEnd,8));
    writeln(stderr,' type=',Scope^.Typ);
  end;
end;
{$endif DEBUG_SEH}

function PushException(var rec: TExceptionRecord; var context: TContext;
  out obj: TObject; AcceptNull: Boolean): Boolean;
var
  adr: Pointer;
  Exc: PExceptObject;
  Frames: PPointer;
  FrameCount: Longint;
  code: Longint;
begin
  Adr:=rec.ExceptionInformation[0];
  Obj:=TObject(rec.ExceptionInformation[1]);
  Framecount:=Longint(rec.ExceptionInformation[2]);
  Frames:=rec.ExceptionInformation[3];

  if rec.ExceptionCode<>FPC_EXCEPTION_CODE then
  begin
    Obj:=nil;
    Result:=False;
    code:=RunErrorCode(rec);
    if Assigned(ExceptObjProc) then
      Obj:=TObject(TExceptObjProc(ExceptObjProc)(abs(code),rec));
    if (Obj=nil) and (not AcceptNull) then
      Exit;
    adr:=rec.ExceptionAddress;
    FrameCount:=GetBacktrace(context,nil,Frames);
    if code<0 then
      SysResetFPU;
  end;

  New(Exc);
  Exc^.FObject:=Obj;
  Exc^.Addr:=adr;
  Exc^.Frames:=Frames;
  Exc^.FrameCount:=FrameCount;
  Exc^.Refcount:=0;
  { link to RaiseList }
  Exc^.Next:=ExceptObjectStack;
  ExceptObjectStack:=Exc;
  Result:=True;
end;

function __FPC_default_handler(
  var rec: TExceptionRecord;
  frame: Pointer;
  var context: TCONTEXT;
  var dispatch: TDispatcherContext): EXCEPTION_DISPOSITION; [public,alias:'__FPC_DEFAULT_HANDLER'];
label L1;
var
  exc: PExceptObject;
  obj: TObject;
begin
  if (rec.ExceptionFlags and EXCEPTION_UNWIND)=0 then
  begin
    { Athlon prefetch bug? }
    if (rec.ExceptionCode=STATUS_ACCESS_VIOLATION) and is_prefetch(pointer(Context.rip)) then
    begin
      result:=ExceptionContinueExecution;
      exit;
    end;
    PushException(rec,context,obj,True);
    RtlUnwindEx(frame, @L1, @rec, nil, dispatch.ContextRecord, dispatch.HistoryTable);
  end
  else if (rec.ExceptionFlags and EXCEPTION_TARGET_UNWIND)<>0 then
  begin
    Exc:=ExceptObjectStack;
    if Exc^.FObject=nil then
      RunError(abs(RunErrorCode(rec)))  // !!prints wrong backtrace
    else
    begin
      { if ExceptObjProc=nil, ExceptProc is typically also nil,
        so we cannot make much use of this backtrace }
      if Assigned(ExceptProc) then
      begin
        ExceptProc(Exc^.FObject,Exc^.Addr,Exc^.FrameCount,Exc^.Frames);
        Halt(217);
      end;
L1:
      RunError(217);
    end;
  end;
  result:=ExceptionContinueSearch;
end;

function __FPC_specific_handler(
  var rec: TExceptionRecord;
  frame: Pointer;
  var context: TCONTEXT;
  var dispatch: TDispatcherContext): EXCEPTION_DISPOSITION; [public,alias:'__FPC_specific_handler'];

var
  TargetRva,ControlRva: DWord;
  scope: PScopeRec;
  scopeIdx: DWord;
  TargetAddr: Pointer;
  obj:TObject;
begin
{$ifdef DEBUG_SEH}
  if IsConsole then
  begin
    writeln(stderr,'Exception handler for ',BacktraceStrFunc(Pointer(dispatch.FunctionEntry^.BeginAddress+dispatch.ImageBase)));
    writeln(stderr,'Code=', hexstr(rec.ExceptionCode,8),' Flags=',hexstr(rec.ExceptionFlags,2), ' CtrlPc=',hexstr(dispatch.ControlPc,16));
  end;
{$endif DEBUG_SEH}
  result:=ExceptionContinueSearch;
  ControlRva:=dispatch.ControlPc-dispatch.ImageBase;
  ScopeIdx:=dispatch.ScopeIndex;
  if (rec.ExceptionFlags and EXCEPTION_UNWIND)=0 then
  begin
    while ScopeIdx<PDWord(dispatch.HandlerData)^ do
    begin
      scope:=@PScopeRec(dispatch.HandlerData+sizeof(Dword))[ScopeIdx];
{$ifdef DEBUG_SEH}
      PrintScope(ScopeIdx, scope);
{$endif DEBUG_SEH}
      { Check if the exception was raised in the 'except' block,
        and dispose the existing exception object if so. }
      if (ControlRva>=scope^.RvaEnd) and (ControlRva<scope^.RvaHandler) and
        ((scope^.Typ=SCOPE_CATCHALL) or (scope^.Typ>SCOPE_IMPLICIT)) then
        Internal_PopObjectStack.Free
      else if (ControlRva>=scope^.RvaStart) and (ControlRva<scope^.RvaEnd) and
        (scope^.Typ<>SCOPE_FINALLY)then
      begin
        { Athlon prefetch bug? }
        if (rec.ExceptionCode=STATUS_ACCESS_VIOLATION) and is_prefetch(pointer(Context.rip)) then
        begin
          result:=ExceptionContinueExecution;
          exit;
        end;

        if scope^.Typ>SCOPE_IMPLICIT then  // filtering needed
        begin
          TargetAddr:=FilterException(rec,dispatch.ImageBase,scope);
          if TargetAddr=nil then
          begin
            Inc(ScopeIdx);
            Continue;
          end;
        end
        else
          TargetAddr:=Pointer(scope^.RvaEnd+dispatch.ImageBase);
{$ifdef DEBUG_SEH}
        if IsConsole then
          writeln(stderr,'match at scope #',scopeIdx,', unwind target=',hexstr(TargetAddr));
{$endif DEBUG_SEH}
        if not PushException(rec,context,obj,Scope^.Typ=SCOPE_IMPLICIT) then
          Exit;

        { Does not return, control is transferred to TargetAddr,
          obj is placed into RAX. }
        RtlUnwindEx(frame, TargetAddr, @rec, obj, dispatch.ContextRecord, dispatch.HistoryTable);
      end;
      Inc(ScopeIdx);
    end;
  end
  else
  begin
    TargetRva:=dispatch.TargetIp-dispatch.ImageBase;
{$ifdef DEBUG_SEH}
    if IsConsole then
      writeln(stderr,'Unwind, TargetRva=',hexstr(TargetRva,8),' CtrlRva=',hexstr(ControlRva,8),' idx=',ScopeIdx);
{$endif DEBUG_SEH}
    while ScopeIdx<PDword(dispatch.HandlerData)^ do
    begin
      scope:=@PScopeRec(dispatch.HandlerData+sizeof(Dword))[ScopeIdx];
{$ifdef DEBUG_SEH}
      PrintScope(scopeIdx, scope);
{$endif DEBUG_SEH}
      if (ControlRva>=scope^.RvaStart) and (ControlRva<scope^.RvaEnd) and
         ((scope^.Typ=SCOPE_FINALLY) or (scope^.Typ=SCOPE_IMPLICIT)) then
      begin
        if (TargetRva>=scope^.RvaStart) and (TargetRva<scope^.RvaEnd) and
          ((rec.ExceptionFlags and EXCEPTION_TARGET_UNWIND)<>0) then
        begin
          Exit;
        end;

        dispatch.ScopeIndex:=ScopeIdx+1;
{$ifdef DEBUG_SEH}
        if IsConsole then
          writeln(stderr,'calling handler @',hexstr(dispatch.imagebase+scope^.RvaHandler,16));
{$endif DEBUG_SEH}
        TUnwindProc(dispatch.ImageBase+scope^.RvaHandler)(context.rbp);
      end;
      Inc(ScopeIdx);
    end;
  end;
end;
{$endif FPC_USE_WIN64_SEH}

