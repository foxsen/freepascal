{

    This file is part of the Free Pascal run time library.
    Copyright (c) 2004 by Karoly Balogh

    Sysutils unit for Nintendo DS.
    This unit is based on the MorphOS one and is adapted for Nintendo DS
    simply by stripping out all stuff inside funcs and procs. 
    Copyright (c) 2006 by Francesco Lombardi

    Based on Amiga version by Carl Eric Codere, and other
    parts of the RTL

    See the file COPYING.FPC, included in this distribution,
    for details about the copyright.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

 **********************************************************************}

unit sysutils;

interface

{$MODE objfpc}
{$MODESWITCH OUT}
{ force ansistrings }
{$H+}

{ Include platform independent interface part }
{$i sysutilh.inc}

implementation

uses
  sysconst;
    
{ Include platform independent implementation part }
{$i sysutils.inc}


{****************************************************************************
                              File Functions
****************************************************************************}
function FileOpen(const FileName: string; Mode: Integer): LongInt;
var
  NDSFlags: longint;
begin
  NDSFlags := 0;

  case (Mode and (fmOpenRead or fmOpenWrite or fmOpenReadWrite)) of
    fmOpenRead : NDSFlags := NDSFlags or O_RdOnly;
    fmOpenWrite : NDSFlags := NDSFlags or O_WrOnly;
    fmOpenReadWrite : NDSFlags := NDSFlags or O_RdWr;
  end;
  FileOpen := _open(pchar(FileName), NDSFlags);
end;


function FileGetDate(Handle: LongInt) : LongInt;
begin
  result := -1;
end;


function FileSetDate(Handle, Age: LongInt) : LongInt;
begin
  result := -1;
end;


function FileCreate(const FileName: string) : LongInt;
begin
  FileCreate:=_open(pointer(FileName), O_RdWr or O_Creat or O_Trunc);
end;


function FileCreate(const FileName: string; Rights: integer): LongInt;
begin
  FileCreate:=_Open(pointer(FileName),O_RdWr or O_Creat or O_Trunc,Rights);
end;


function FileCreate(const FileName: string; ShareMode : Integer; Rights: integer): LongInt;
begin
  result := FileCreate(FileName, Rights);
end;


function FileRead(Handle: LongInt; Out Buffer; Count: LongInt): LongInt;
begin
  FileRead := _Read(Handle, Buffer, Count);
end;


function FileWrite(Handle: LongInt; const Buffer; Count: LongInt): LongInt;
begin
  FileWrite := _Write(Handle, @Buffer, Count);
end;


function FileSeek(Handle, FOffset, Origin: LongInt) : LongInt;
begin
  result := longint(FileSeek(Handle, int64(FOffset), Origin));
end;

function FileSeek(Handle: LongInt; FOffset: Int64; Origin: Longint): Int64;
begin
  FileSeek := _lSeek(Handle, FOffset, Origin);
end;


procedure FileClose(Handle: LongInt);
begin
  _close(Handle);
end;


function FileTruncate(Handle: THandle; Size: Int64): Boolean;
begin
  if Size > high (longint) then
    FileTruncate := false
  else
    FileTruncate:=(_truncate(Handle,Size) = 0);
end;


function DeleteFile(const FileName: string) : Boolean;
begin
  Result := _UnLink(pointer(FileName))>= 0;
end;


function RenameFile(const OldName, NewName: string): Boolean;
begin
  RenameFile := _Rename(pointer(OldNAme), pointer(NewName)) >= 0;
end;


(****** end of non portable routines ******)


Function FileAge (Const FileName : String): Longint;
var 
  info: Stat;
begin
  if (_stat(pchar(FileName), Info) < 0) or S_ISDIR(info.st_mode) then
    exit(-1)
  else 
    Result := (info.st_mtime);
end;


Function FileExists (Const FileName : String) : Boolean;
begin
  FileExists := _Access(pointer(filename), F_OK) = 0;
end;



Function FindFirst (Const Path : String; Attr : Longint; Out Rslt : TSearchRec) : Longint;
begin
  result := -1;
end;


Function FindNext (Var Rslt : TSearchRec) : Longint;
begin
  result := -1;
end;

Procedure FindClose (Var F : TSearchrec);
begin

end;

Function FileGetAttr (Const FileName : String) : Longint;
Var Info : TStat;
begin
  If _stat(pchar(FileName), Info) <> 0 then
    Result := -1
  Else
    Result := (Info.st_mode shr 16) and $ffff;
end;


Function FileSetAttr (Const Filename : String; Attr: longint) : Longint;
begin
  result := -1;
end;



{****************************************************************************
                              Disk Functions
****************************************************************************}

Procedure AddDisk(const path:string);
begin

end;



Function DiskFree(Drive: Byte): int64;
Begin
  result := -1;
End;


Function DiskSize(Drive: Byte): int64;
Begin
  result := -1;
End;


Function GetCurrentDir : String;
begin
  result := '';
end;


Function SetCurrentDir (Const NewDir : String) : Boolean;
begin
  result := false;
end;


Function CreateDir (Const NewDir : String) : Boolean;
begin
  result := false;
end;


Function RemoveDir (Const Dir : String) : Boolean;
begin
  result := false;
end;


function DirectoryExists(const Directory: string): Boolean;
begin
  result := false;
end;



{****************************************************************************
                              Misc Functions
****************************************************************************}

Procedure SysBeep;
begin
end;


{****************************************************************************
                              Locale Functions
****************************************************************************}

Procedure GetLocalTime(var SystemTime: TSystemTime);
begin
end ;


function SysErrorMessage(ErrorCode: Integer): String;
begin
{  Result:=StrError(ErrorCode);}
  result := '';
end;

{****************************************************************************
                              OS utility functions
****************************************************************************}

Function GetEnvironmentVariable(Const EnvVar : String) : String;
begin
  result := '';
end;

Function GetEnvironmentVariableCount : Integer;
begin
  result := -1;
end;

Function GetEnvironmentString(Index : Integer) : String;
begin
  result := '';
end;

function ExecuteProcess (const Path: AnsiString; const ComLine: AnsiString;Flags:TExecuteFlags=[]): integer;
begin
  result := -1;
end;

function ExecuteProcess (const Path: AnsiString;
                                  const ComLine: array of AnsiString;Flags:TExecuteFlags=[]): integer;
begin
  result := -1;
end;


{****************************************************************************
                              Initialization code
****************************************************************************}

Initialization
  InitExceptions;
Finalization
  DoneExceptions;
end.
