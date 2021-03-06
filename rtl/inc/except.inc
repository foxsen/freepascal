{
    This file is part of the Free Pascal run time library.
    Copyright (c) 1999-2000 by Michael Van Canneyt
    member of the Free Pascal development team

    See the file COPYING.FPC, included in this distribution,
    for details about the copyright.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

 **********************************************************************}

{****************************************************************************
                                Exception support
****************************************************************************}


Const
  { Type of exception. Currently only one. }
  FPC_EXCEPTION   = 1;

  { types of frames for the exception address stack }
  cExceptionFrame = 1;
  cFinalizeFrame  = 2;

Type
  PExceptAddr = ^TExceptAddr;
  TExceptAddr = record
    buf       : pjmp_buf;
    next      : PExceptAddr;
    frametype : Longint;
  end;

Const
  CatchAllExceptions = PtrInt(-1);

ThreadVar
  ExceptAddrStack   : PExceptAddr;
  ExceptObjectStack : PExceptObject;

Function RaiseList : PExceptObject;
begin
  RaiseList:=ExceptObjectStack;
end;


function AcquireExceptionObject: Pointer;
var
  _ExceptObjectStack : PExceptObject;
begin
  _ExceptObjectStack:=ExceptObjectStack;
  If _ExceptObjectStack<>nil then
    begin
      Inc(_ExceptObjectStack^.refcount);
      AcquireExceptionObject := _ExceptObjectStack^.FObject;
    end
  else
    RunError(231);
end;


procedure ReleaseExceptionObject;
var
  _ExceptObjectStack : PExceptObject;
begin
  _ExceptObjectStack:=ExceptObjectStack;
  If _ExceptObjectStack <> nil then
    begin
      if _ExceptObjectStack^.refcount > 0 then
        Dec(_ExceptObjectStack^.refcount);
    end
  else
    RunError(231);
end;


Function fpc_PushExceptAddr (Ft: Longint;_buf,_newaddr : pointer): PJmp_buf ;
  [Public, Alias : 'FPC_PUSHEXCEPTADDR'];compilerproc;
var
  _ExceptAddrstack : ^PExceptAddr;
begin
{$ifdef excdebug}
  writeln ('In PushExceptAddr');
{$endif}
  _ExceptAddrstack:=@ExceptAddrstack;
  PExceptAddr(_newaddr)^.Next:=_ExceptAddrstack^;
  _ExceptAddrStack^:=PExceptAddr(_newaddr);
  PExceptAddr(_newaddr)^.Buf:=PJmp_Buf(_buf);
  PExceptAddr(_newaddr)^.FrameType:=ft;
  result:=PJmp_Buf(_buf);
end;


Procedure PushExceptObject(Obj : TObject; AnAddr,AFrame : Pointer);
var
  Newobj : PExceptObject;
  _ExceptObjectStack : ^PExceptObject;
  framebufsize,
  framecount  : longint;
  frames      : PPointer;
  prev_frame,
  curr_frame,
  caller_frame,
  caller_addr : Pointer;
begin
{$ifdef excdebug}
  writeln ('In PushExceptObject');
{$endif}
  _ExceptObjectStack:=@ExceptObjectStack;
  New(NewObj);
  NewObj^.Next:=_ExceptObjectStack^;
  _ExceptObjectStack^:=NewObj;

  NewObj^.FObject:=Obj;
  NewObj^.Addr:=AnAddr;
  NewObj^.refcount:=0;

  { Backtrace }
  curr_frame:=AFrame;
  prev_frame:=get_frame;
  frames:=nil;
  framebufsize:=0;
  framecount:=0;
  while (framecount<RaiseMaxFrameCount) and (curr_frame > prev_frame) and
        (curr_frame<(StackBottom + StackLength)) do
   Begin
     caller_addr := get_caller_addr(curr_frame);
     caller_frame := get_caller_frame(curr_frame);
     if (caller_addr=nil) or
        (caller_frame=nil) then
       break;
     if (framecount>=framebufsize) then
       begin
         inc(framebufsize,16);
         reallocmem(frames,framebufsize*sizeof(pointer));
       end;
     frames[framecount]:=caller_addr;
     inc(framecount);
     prev_frame:=curr_frame;
     curr_frame:=caller_frame;
   End;
  NewObj^.framecount:=framecount;
  NewObj^.frames:=frames;
end;

Procedure DoUnHandledException;
var
  _ExceptObjectStack : PExceptObject;
begin
  _ExceptObjectStack:=ExceptObjectStack;
  If (ExceptProc<>Nil) and (_ExceptObjectStack<>Nil) then
    with _ExceptObjectStack^ do
      begin
        TExceptProc(ExceptProc)(FObject,Addr,FrameCount,Frames);
        halt(217)
      end;
  if erroraddr = nil then
    RunError(217)
  else
    Halt(errorcode);
end;

{$ifndef FPC_SYSTEM_HAS_RAISEEXCEPTION}
Function fpc_RaiseException (Obj : TObject; AnAddr,AFrame : Pointer) : TObject;[Public, Alias : 'FPC_RAISEEXCEPTION']; compilerproc;
var
  _ExceptObjectStack : PExceptObject;
  _ExceptAddrstack : PExceptAddr;
begin
{$ifdef excdebug}
  writeln ('In RaiseException');
{$endif}
  fpc_Raiseexception:=nil;
  PushExceptObject(Obj,AnAddr,AFrame);
  _ExceptAddrstack:=ExceptAddrStack;
  If _ExceptAddrStack=Nil then
    DoUnhandledException;
  _ExceptObjectStack:=ExceptObjectStack;
  if (RaiseProc <> nil) and (_ExceptObjectStack <> nil) then
    with _ExceptObjectStack^ do
      RaiseProc(FObject,Addr,FrameCount,Frames);
  longjmp(_ExceptAddrStack^.Buf^,FPC_Exception);
end;
{$endif FPC_SYSTEM_HAS_RAISEEXCEPTION}


Procedure fpc_PopAddrStack;[Public, Alias : 'FPC_POPADDRSTACK']; compilerproc;
var
  hp : ^PExceptAddr;
begin
{$ifdef excdebug}
  writeln ('In Popaddrstack');
{$endif}
  hp:=@ExceptAddrStack;
  If hp^=nil then
    begin
{$ifdef excdebug}
      writeln ('At end of ExceptionAddresStack');
{$endif}
      halt (255);
    end
  else
    begin
      hp^:=hp^^.Next;
    end;
end;


function fpc_PopObjectStack : TObject;[Public, Alias : 'FPC_POPOBJECTSTACK']; compilerproc;
var
  hp,_ExceptObjectStack : PExceptObject;
begin
{$ifdef excdebug}
  writeln ('In PopObjectstack');
{$endif}
  _ExceptObjectStack:=ExceptObjectStack;
  If _ExceptObjectStack=nil then
    begin
{$ifdef excdebug}
      writeln ('At end of ExceptionObjectStack');
{$endif}
      halt (1);
    end
  else
    begin
       { we need to return the exception object to dispose it }
       if _ExceptObjectStack^.refcount = 0 then begin
         fpc_PopObjectStack:=_ExceptObjectStack^.FObject;
       end else begin
         fpc_PopObjectStack:=nil;
       end;
       hp:=_ExceptObjectStack;
       ExceptObjectStack:=_ExceptObjectStack^.next;
       if assigned(hp^.frames) then
         freemem(hp^.frames);
       dispose(hp);
       erroraddr:=nil;
    end;
end;


{ this is for popping exception objects when a second exception is risen }
{ in an except/on                                                        }
function fpc_PopSecondObjectStack : TObject;[Public, Alias : 'FPC_POPSECONDOBJECTSTACK']; compilerproc;
var
  hp,_ExceptObjectStack : PExceptObject;
begin
{$ifdef excdebug}
  writeln ('In PopObjectstack');
{$endif}
  _ExceptObjectStack:=ExceptObjectStack;
  If not(assigned(_ExceptObjectStack)) or
     not(assigned(_ExceptObjectStack^.next)) then
    begin
{$ifdef excdebug}
      writeln ('At end of ExceptionObjectStack');
{$endif}
      halt (1);
    end
  else
    begin
      if _ExceptObjectStack^.next^.refcount=0 then
        { we need to return the exception object to dispose it if refcount=0 }
        fpc_PopSecondObjectStack:=_ExceptObjectStack^.next^.FObject
      else
        fpc_PopSecondObjectStack:=nil;
      hp:=_ExceptObjectStack^.next;
      _ExceptObjectStack^.next:=hp^.next;
      if assigned(hp^.frames) then
        freemem(hp^.frames);
      dispose(hp);
    end;
end;

{$ifndef FPC_SYSTEM_HAS_RERAISE}
Procedure fpc_ReRaise;[Public, Alias : 'FPC_RERAISE']; compilerproc;
var
  _ExceptAddrStack : PExceptAddr;
begin
{$ifdef excdebug}
  writeln ('In reraise');
{$endif}
  _ExceptAddrStack:=ExceptAddrStack;
  If _ExceptAddrStack=Nil then
    DoUnHandledException;
  ExceptObjectStack^.refcount := 0;
  longjmp(_ExceptAddrStack^.Buf^,FPC_Exception);
end;
{$endif FPC_SYSTEM_HAS_RERAISE}

function Internal_PopSecondObjectStack : TObject; external name 'FPC_POPSECONDOBJECTSTACK';
function Internal_PopObjectStack: TObject; external name 'FPC_POPOBJECTSTACK';
procedure Internal_Reraise; external name 'FPC_RERAISE';

Function fpc_Catches(Objtype : TClass) : TObject;[Public, Alias : 'FPC_CATCHES']; compilerproc;
var
  _ExceptObjectStack : PExceptObject;
begin
  _ExceptObjectStack:=ExceptObjectStack;
  If _ExceptObjectStack=Nil then
   begin
{$ifdef excdebug}
     Writeln ('Internal error.');
{$endif}
     halt (255);
   end;
  if Not ((Objtype = TClass(CatchAllExceptions)) or
         (_ExceptObjectStack^.FObject is ObjType)) then
    fpc_Catches:=Nil
  else
    begin
      // catch !
      fpc_Catches:=_ExceptObjectStack^.FObject;
      { this can't be done, because there could be a reraise (PFV)
       PopObjectStack;

       Also the PopAddrStack shouldn't be done, we do it now
       immediatly in the exception handler (FK)
      PopAddrStack; }
    end;
end;

Procedure fpc_DestroyException(o : TObject);[Public, Alias : 'FPC_DESTROYEXCEPTION']; compilerproc;
begin
  { with free we're on the really safe side }
  o.Free;
end;

{ TODO: no longer used, clean up }
function fpc_GetExceptionAddr : Pointer;[Public, Alias : 'FPC_GETEXCEPTIONADDR']; compilerproc;
var
  _ExceptObjectStack : PExceptObject;
begin
  _ExceptObjectStack:=ExceptObjectStack;
  if _ExceptObjectStack=nil then
    fpc_GetExceptionAddr:=nil
  else
    fpc_GetExceptionAddr:=_ExceptObjectStack^.Addr;
end;

Procedure SysInitExceptions;
{
  Initialize exceptionsupport
}
begin
  ExceptObjectstack:=Nil;
  ExceptAddrStack:=Nil;
end;


procedure fpc_doneexception;[public,alias:'FPC_DONEEXCEPTION'] compilerproc;
begin
  Internal_PopObjectStack.Free;
end;

procedure fpc_raise_nested;[public,alias:'FPC_RAISE_NESTED']compilerproc;
begin
  Internal_PopSecondObjectStack.Free;
  Internal_Reraise;
end;

function fpc_safecallhandler(obj: TObject): HResult; [public,alias:'FPC_SAFECALLHANDLER']; compilerproc;
var
  raiselist: PExceptObject;
  adr: Pointer;
  exc: TObject;
begin
  raiselist:=ExceptObjectStack;
  if Assigned(raiseList) then
    adr:=raiseList^.Addr
  else
    adr:=nil;
  exc:=Internal_PopObjectStack;
  if Assigned(obj) and Assigned(exc) then
    result:=obj.SafeCallException(exc,adr)
  else
    result:=E_UNEXPECTED;
  exc.Free;
end;

