{

    This file is part of the Free Pascal run time library.
    Copyright (c) 1999-2000 by Florian Klaempfl
    member of the Free Pascal development team

    Sysutils unit for OS/2

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

{$DEFINE HAS_SLEEP}
{ Include platform independent interface part }
{$i sysutilh.inc}


implementation

  uses
    sysconst, DosCalls;


type
(* Necessary here due to a different definition of TDateTime in DosCalls. *)
  TDateTime = System.TDateTime;

{$DEFINE FPC_FEXPAND_UNC} (* UNC paths are supported *)
{$DEFINE FPC_FEXPAND_DRIVES} (* Full paths begin with drive specification *)
{$DEFINE FPC_FEXPAND_GETENV_PCHAR}

{ Include platform independent implementation part }
{$i sysutils.inc}


{****************************************************************************
                              File Functions
****************************************************************************}

const
 ofRead        = $0000;     {Open for reading}
 ofWrite       = $0001;     {Open for writing}
 ofReadWrite   = $0002;     {Open for reading/writing}
 doDenyRW      = $0010;     {DenyAll (no sharing)}
 faCreateNew   = $00010000; {Create if file does not exist}
 faOpenReplace = $00040000; {Truncate if file exists}
 faCreate      = $00050000; {Create if file does not exist, truncate otherwise}

 FindResvdMask = $00003737; {Allowed bits in attribute
                             specification for DosFindFirst call.}

function FileOpen (const FileName: string; Mode: integer): THandle;
Var
  Handle: THandle;
  Rc, Action: cardinal;
begin
(* DenyNone if sharing not specified. *)
  if (Mode and 112 = 0) or (Mode and 112 > 64) then
   Mode := Mode or 64;
  Rc:=Sys_DosOpenL(PChar (FileName), Handle, Action, 0, 0, 1, Mode, nil);
  If Rc=0 then
    FileOpen:=Handle
  else
    FileOpen:=feInvalidHandle; //FileOpen:=-RC;
    //should return feInvalidHandle(=-1) if fail, other negative returned value are no more errors
end;

function FileCreate (const FileName: string): THandle;
begin
  FileCreate := FileCreate (FileName, doDenyRW, 777); (* Sharing to DenyAll *)
end;

function FileCreate (const FileName: string; Rights: integer): THandle;
begin
  FileCreate := FileCreate (FileName, doDenyRW, Rights);
                                      (* Sharing to DenyAll *)
end;

function FileCreate (const FileName: string; ShareMode: integer;
                                                     Rights: integer): THandle;
var
  Handle: THandle;
  RC, Action: cardinal;
begin
  ShareMode := ShareMode and 112;
  (* Sharing to DenyAll as default in case of values not allowed by OS/2. *)
  if (ShareMode = 0) or (ShareMode > 64) then
   ShareMode := doDenyRW;
  RC := Sys_DosOpenL (PChar (FileName), Handle, Action, 0, 0, $12,
                                    faCreate or ofReadWrite or ShareMode, nil);
  if RC = 0 then
   FileCreate := Handle
  else
   FileCreate := feInvalidHandle;
End;


function FileRead (Handle: THandle; Out Buffer; Count: longint): longint;
Var
  T: cardinal;
begin
  DosRead(Handle, Buffer, Count, T);
  FileRead := longint (T);
end;

function FileWrite (Handle: THandle; const Buffer; Count: longint): longint;
Var
  T: cardinal;
begin
  DosWrite (Handle, Buffer, Count, T);
  FileWrite := longint (T);
end;

function FileSeek (Handle: THandle; FOffset, Origin: longint): longint;
var
  NPos: int64;
begin
  if (Sys_DosSetFilePtrL (Handle, FOffset, Origin, NPos) = 0)
                                               and (NPos < high (longint)) then
    FileSeek:= longint (NPos)
  else
    FileSeek:=-1;
end;

function FileSeek (Handle: THandle; FOffset: Int64; Origin: Longint): Int64;
var
  NPos: int64;
begin
  if Sys_DosSetFilePtrL (Handle, FOffset, Origin, NPos) = 0 then
    FileSeek:= NPos
  else
    FileSeek:=-1;
end;

procedure FileClose (Handle: THandle);
begin
  DosClose(Handle);
end;

function FileTruncate (Handle: THandle; Size: Int64): boolean;
begin
  FileTruncate:=Sys_DosSetFileSizeL(Handle, Size)=0;
  FileSeek(Handle, 0, 2);
end;

function FileAge (const FileName: string): longint;
var Handle: longint;
begin
    Handle := FileOpen (FileName, 0);
    if Handle <> -1 then
        begin
            Result := FileGetDate (Handle);
            FileClose (Handle);
        end
    else
        Result := -1;
end;


function FileExists (const FileName: string): boolean;
var
  L: longint;
begin
  if FileName = '' then
   Result := false
  else
   begin
    L := FileGetAttr (FileName);
    Result := (L >= 0) and (L and (faDirectory or faVolumeID) = 0);
(* Neither VolumeIDs nor directories are files. *)
   end;
end;


type    TRec = record
            T, D: word;
        end;
        PSearchRec = ^TSearchRec;

function FindFirst (const Path: string; Attr: longint; out Rslt: TSearchRec): longint;

var SR: PSearchRec;
    FStat: PFileFindBuf3L;
    Count: cardinal;
    Err: cardinal;
    I: cardinal;

begin
  New (FStat);
  Rslt.FindHandle := THandle ($FFFFFFFF);
  Count := 1;
  if FSApi64 then
   Err := DosFindFirst (PChar (Path), Rslt.FindHandle,
            Attr and FindResvdMask, FStat, SizeOf (FStat^), Count, ilStandardL)
  else
   Err := DosFindFirst (PChar (Path), Rslt.FindHandle,
            Attr and FindResvdMask, FStat, SizeOf (FStat^), Count, ilStandard);
  if (Err = 0) and (Count = 0) then
   Err := 18;
  FindFirst := -Err;
  if Err = 0 then
   begin
    Rslt.ExcludeAttr := 0;
    TRec (Rslt.Time).T := FStat^.TimeLastWrite;
    TRec (Rslt.Time).D := FStat^.DateLastWrite;
    if FSApi64 then
     begin
      Rslt.Size := FStat^.FileSize;
      Rslt.Name := FStat^.Name;
      Rslt.Attr := FStat^.AttrFile;
     end
    else
     begin
      Rslt.Size := PFileFindBuf3 (FStat)^.FileSize;
      Rslt.Name := PFileFindBuf3 (FStat)^.Name;
      Rslt.Attr := PFileFindBuf3 (FStat)^.AttrFile;
     end;
   end
  else
   FindClose(Rslt);

  Dispose (FStat);
end;


function FindNext (var Rslt: TSearchRec): longint;
var
  SR: PSearchRec;
  FStat: PFileFindBuf3L;
  Count: cardinal;
  Err: cardinal;
begin
  New (FStat);
  Count := 1;
  Err := DosFindNext (Rslt.FindHandle, FStat, SizeOf (FStat^), Count);
  if (Err = 0) and (Count = 0) then
   Err := 18;
  FindNext := -Err;
  if Err = 0 then
  begin
    Rslt.ExcludeAttr := 0;
    TRec (Rslt.Time).T := FStat^.TimeLastWrite;
    TRec (Rslt.Time).D := FStat^.DateLastWrite;
    if FSApi64 then
     begin
      Rslt.Size := FStat^.FileSize;
      Rslt.Name := FStat^.Name;
      Rslt.Attr := FStat^.AttrFile;
     end
    else
     begin
      Rslt.Size := PFileFindBuf3 (FStat)^.FileSize;
      Rslt.Name := PFileFindBuf3 (FStat)^.Name;
      Rslt.Attr := PFileFindBuf3 (FStat)^.AttrFile;
     end;
  end;
  Dispose (FStat);
end;


procedure FindClose (var F: TSearchrec);
var
  SR: PSearchRec;
begin
  DosFindClose (F.FindHandle);
  F.FindHandle := 0;
end;

function FileGetDate (Handle: THandle): longint;
var
  FStat: TFileStatus3;
  Time: Longint;
  RC: cardinal;
begin
  RC := DosQueryFileInfo(Handle, ilStandard, @FStat, SizeOf(FStat));
  if RC = 0 then
  begin
    Time := FStat.TimeLastWrite + longint (FStat.DateLastWrite) shl 16;
    if Time = 0 then
      Time := FStat.TimeCreation + longint (FStat.DateCreation) shl 16;
  end else
    Time:=0;
  FileGetDate:=Time;
end;

function FileSetDate (Handle: THandle; Age: longint): longint;
var
  FStat: PFileStatus3;
  RC: cardinal;
begin
  New (FStat);
  RC := DosQueryFileInfo (Handle, ilStandard, FStat, SizeOf (FStat^));
  if RC <> 0 then
    FileSetDate := -1
  else
  begin
    FStat^.DateLastAccess := Hi (Age);
    FStat^.DateLastWrite := Hi (Age);
    FStat^.TimeLastAccess := Lo (Age);
    FStat^.TimeLastWrite := Lo (Age);
    RC := DosSetFileInfo (Handle, ilStandard, FStat, SizeOf (FStat^));
    if RC <> 0 then
      FileSetDate := -1
    else
      FileSetDate := 0;
  end;
  Dispose (FStat);
end;

function FileGetAttr (const FileName: string): longint;
var
  FS: PFileStatus3;
begin
  New(FS);
  Result:=-DosQueryPathInfo(PChar (FileName), ilStandard, FS, SizeOf(FS^));
  If Result=0 Then Result:=FS^.attrFile;
  Dispose(FS);
end;

function FileSetAttr (const Filename: string; Attr: longint): longint;
Var
  FS: PFileStatus3;
Begin
  New(FS);
  FillChar(FS, SizeOf(FS^), 0);
  FS^.AttrFile:=Attr;
  Result:=-DosSetPathInfo(PChar (FileName), ilStandard, FS, SizeOf(FS^), 0);
  Dispose(FS);
end;


function DeleteFile (const FileName: string): boolean;
Begin
  Result:=(DosDelete(PChar (FileName))=0);
End;

function RenameFile (const OldName, NewName: string): boolean;
Begin
  Result:=(DosMove(PChar (OldName), PChar (NewName))=0);
End;

{****************************************************************************
                              Disk Functions
****************************************************************************}

function DiskFree (Drive: byte): int64;

var FI: TFSinfo;
    RC: cardinal;

begin
        {In OS/2, we use the filesystem information.}
            RC := DosQueryFSInfo (Drive, 1, FI, SizeOf (FI));
            if RC = 0 then
                DiskFree := int64 (FI.Free_Clusters) *
                   int64 (FI.Sectors_Per_Cluster) * int64 (FI.Bytes_Per_Sector)
            else
                DiskFree := -1;
end;

function DiskSize (Drive: byte): int64;

var FI: TFSinfo;
    RC: cardinal;

begin
        {In OS/2, we use the filesystem information.}
            RC := DosQueryFSinfo (Drive, 1, FI, SizeOf (FI));
            if RC = 0 then
                DiskSize := int64 (FI.Total_Clusters) *
                   int64 (FI.Sectors_Per_Cluster) * int64 (FI.Bytes_Per_Sector)
            else
                DiskSize := -1;
end;


function GetCurrentDir: string;
begin
 GetDir (0, Result);
end;


function SetCurrentDir (const NewDir: string): boolean;
var
 OrigInOutRes: word;
begin
 OrigInOutRes := InOutRes;
 InOutRes := 0;
{$I-}
 ChDir (NewDir);
 Result := InOutRes = 0;
{$I+}
 InOutRes := OrigInOutRes;
end;


function CreateDir (const NewDir: string): boolean;
var
 OrigInOutRes: word;
begin
 OrigInOutRes := InOutRes;
 InOutRes := 0;
{$I-}
 MkDir (NewDir);
 Result := InOutRes = 0;
{$I+}
 InOutRes := OrigInOutRes;
end;


function RemoveDir (const Dir: string): boolean;
var
 OrigInOutRes: word;
begin
 OrigInOutRes := InOutRes;
 InOutRes := 0;
{$I-}
 RmDir (Dir);
 Result := InOutRes = 0;
{$I+}
 InOutRes := OrigInOutRes;
end;


function DirectoryExists (const Directory: string): boolean;
var
  L: longint;
begin
  if Directory = '' then
   Result := false
  else
   begin
    if ((Length (Directory) = 2) or
        (Length (Directory) = 3) and
        (Directory [3] in AllowDirectorySeparators)) and
       (Directory [2] in AllowDriveSeparators) and
       (UpCase (Directory [1]) in ['A'..'Z']) then
(* Checking attributes for 'x:' is not possible but for 'x:.' it is. *)
     L := FileGetAttr (Directory + '.')
    else if (Directory [Length (Directory)] in AllowDirectorySeparators) and
                                              (Length (Directory) > 1) and
(* Do not remove '\' in '\\' (invalid path, possibly broken UNC path). *)
      not (Directory [Length (Directory) - 1] in AllowDirectorySeparators) then
     L := FileGetAttr (Copy (Directory, 1, Length (Directory) - 1))
    else
     L := FileGetAttr (Directory);
    Result := (L > 0) and (L and faDirectory = faDirectory);
   end;
end;


{****************************************************************************
                              Time Functions
****************************************************************************}

procedure GetLocalTime (var SystemTime: TSystemTime);
var
  DT: DosCalls.TDateTime;
begin
  DosGetDateTime(DT);
  with SystemTime do
  begin
    Year:=DT.Year;
    Month:=DT.Month;
    Day:=DT.Day;
    Hour:=DT.Hour;
    Minute:=DT.Minute;
    Second:=DT.Second;
    MilliSecond:=DT.Sec100;
  end;
end;

{****************************************************************************
                              Misc Functions
****************************************************************************}
procedure sysbeep;

begin
  // Maybe implement later on ?

end;

{****************************************************************************
                              Locale Functions
****************************************************************************}

procedure InitAnsi;
var I: byte;
    Country: TCountryCode;
begin
    for I := 0 to 255 do
        UpperCaseTable [I] := Chr (I);
    Move (UpperCaseTable, LowerCaseTable, SizeOf (UpperCaseTable));
            FillChar (Country, SizeOf (Country), 0);
            DosMapCase (SizeOf (UpperCaseTable), Country, @UpperCaseTable);
    for I := 0 to 255 do
        if UpperCaseTable [I] <> Chr (I) then
            LowerCaseTable [Ord (UpperCaseTable [I])] := Chr (I);
end;


procedure InitInternational;
var Country: TCountryCode;
    CtryInfo: TCountryInfo;
    Size: cardinal;
    RC: cardinal;
begin
    Size := 0;
    FillChar (Country, SizeOf (Country), 0);
    FillChar (CtryInfo, SizeOf (CtryInfo), 0);
    RC := DosQueryCtryInfo (SizeOf (CtryInfo), Country, CtryInfo, Size);
    if RC = 0 then
        begin
            DateSeparator := CtryInfo.DateSeparator;
            case CtryInfo.DateFormat of
             1: begin
                    ShortDateFormat := 'd/m/y';
                    LongDateFormat := 'dd" "mmmm" "yyyy';
                end;
             2: begin
                    ShortDateFormat := 'y/m/d';
                    LongDateFormat := 'yyyy" "mmmm" "dd';
                end;
             3: begin
                    ShortDateFormat := 'm/d/y';
                    LongDateFormat := 'mmmm" "dd" "yyyy';
                end;
            end;
            TimeSeparator := CtryInfo.TimeSeparator;
            DecimalSeparator := CtryInfo.DecimalSeparator;
            ThousandSeparator := CtryInfo.ThousandSeparator;
            CurrencyFormat := CtryInfo.CurrencyFormat;
            CurrencyString := PChar (CtryInfo.CurrencyUnit);
        end;
    InitAnsi;
    InitInternationalGeneric;
end;

function SysErrorMessage(ErrorCode: Integer): String;

begin
  Result:=Format(SUnknownErrorCode,[ErrorCode]);
end;


{****************************************************************************
                              OS Utils
****************************************************************************}

function GetEnvPChar (EnvVar: shortstring): PChar;
(* The assembler version is more than three times as fast as Pascal. *)
var
 P: PChar;
begin
 EnvVar := UpCase (EnvVar);
{$ASMMODE INTEL}
 asm
  cld
  mov edi, Environment
  lea esi, EnvVar
  xor eax, eax
  lodsb
@NewVar:
  cmp byte ptr [edi], 0
  jz @Stop
  push eax        { eax contains length of searched variable name }
  push esi        { esi points to the beginning of the variable name }
  mov ecx, -1     { our character ('=' - see below) _must_ be found }
  mov edx, edi    { pointer to beginning of variable name saved in edx }
  mov al, '='     { searching until '=' (end of variable name) }
  repne
  scasb           { scan until '=' not found }
  neg ecx         { what was the name length? }
  dec ecx         { corrected }
  dec ecx         { exclude the '=' character }
  pop esi         { restore pointer to beginning of variable name }
  pop eax         { restore length of searched variable name }
  push eax        { and save both of them again for later use }
  push esi
  cmp ecx, eax    { compare length of searched variable name with name }
  jnz @NotEqual   { ... of currently found variable, jump if different }
  xchg edx, edi   { pointer to current variable name restored in edi }
  repe
  cmpsb           { compare till the end of variable name }
  xchg edx, edi   { pointer to beginning of variable contents in edi }
  jz @Equal       { finish if they're equal }
@NotEqual:
  xor eax, eax    { look for 00h }
  mov ecx, -1     { it _must_ be found }
  repne
  scasb           { scan until found }
  pop esi         { restore pointer to beginning of variable name }
  pop eax         { restore length of searched variable name }
  jmp @NewVar     { ... or continue with new variable otherwise }
@Stop:
  xor eax, eax
  mov P, eax      { Not found - return nil }
  jmp @End
@Equal:
  pop esi         { restore the stack position }
  pop eax
  mov P, edi      { place pointer to variable contents in P }
@End:
 end ['eax','ecx','edx','esi','edi'];
 GetEnvPChar := P;
end;
{$ASMMODE ATT}


Function GetEnvironmentVariable(Const EnvVar : String) : String;

begin
    GetEnvironmentVariable := StrPas (GetEnvPChar (EnvVar));
end;


Function GetEnvironmentVariableCount : Integer;

begin
(*  Result:=FPCCountEnvVar(EnvP); - the amount is already known... *)
  GetEnvironmentVariableCount := EnvC;
end;


Function GetEnvironmentString(Index : Integer) : String;

begin
  Result:=FPCGetEnvStrFromP (EnvP, Index);
end;


procedure Sleep (Milliseconds: cardinal);

begin
 DosSleep (Milliseconds);
end;


function ExecuteProcess (const Path: AnsiString; const ComLine: AnsiString;Flags:TExecuteFlags=[]):
                                                                       integer;
var
 E: EOSError;
 CommandLine: ansistring;
 Args0, Args: DosCalls.PByteArray;
 ObjNameBuf: PChar;
 ArgSize: word;
 Res: TResultCodes;
 ObjName: shortstring;
 RC: cardinal;
 ExecAppType: cardinal;

const
 MaxArgsSize = 3072; (* Amount of memory reserved for arguments in bytes. *)
 ObjBufSize = 512;

function StartSession: cardinal;
var
 HQ: THandle;
 SPID, STID, QName: shortstring;
 SID, PID: cardinal;
 SD: TStartData;
 RD: TRequestData;
 PCI: PChildInfo;
 CISize: cardinal;
 Prio: byte;
begin
 Result := $FFFFFFFF;
 FillChar (SD, SizeOf (SD), 0);
 SD.Length := SizeOf (SD);
 SD.Related := ssf_Related_Child;
 if FileExists (Path) then
(* Full path necessary for starting different executable files from current *)
(* directory. *)
  CommandLine := ExpandFileName (Path)
 else
  CommandLine := Path;
 SD.PgmName := PChar (CommandLine);
 if ComLine <> '' then
  SD.PgmInputs := PChar (ComLine);
 if ExecInheritsHandles in Flags then
   SD.InheritOpt := ssf_InhertOpt_Parent;
 Str (GetProcessID, SPID);
 Str (ThreadID, STID);
 QName := '\QUEUES\FPC_ExecuteProcess_p' + SPID + 't' + STID + '.QUE'#0;
 SD.TermQ := @QName [1];
 SD.ObjectBuffer := ObjNameBuf;
 SD.ObjectBuffLen := ObjBufSize;
 RC := DosCreateQueue (HQ, quFIFO or quConvert_Address, @QName [1]);
 if RC <> 0 then
  Move (QName [1], ObjNameBuf^, Length (QName))
 else
  begin
   RC := DosStartSession (SD, SID, PID);
   if (RC = 0) or (RC = 457) then
    begin
     RC := DosReadQueue (HQ, RD, CISize, PCI, 0, 0, Prio, 0);
     if RC = 0 then
      begin
       Result := PCI^.Return;
       DosCloseQueue (HQ);
       DosFreeMem (PCI);
       FreeMem (ObjNameBuf, ObjBufSize);
      end
     else
      DosCloseQueue (HQ);
    end
   else
    DosCloseQueue (HQ);
  end;
end;

begin
 Result := integer ($FFFFFFFF);
 ObjName := '';
 GetMem (ObjNameBuf, ObjBufSize);
 FillChar (ObjNameBuf^, ObjBufSize, 0);

 if (DosQueryAppType (PChar (Path), ExecAppType) = 0) and
                               (ApplicationType and 3 = ExecAppType and 3) then
(* DosExecPgm should work... *)
  begin
   if ComLine = '' then
    begin
     Args0 := nil;
     Args := nil;
    end
   else
    begin
     GetMem (Args0, MaxArgsSize);
     Args := Args0;
(* Work around a bug in OS/2 - argument to DosExecPgm *)
(* should not cross 64K boundary. *)
     if ((PtrUInt (Args) + 1024) and $FFFF) < 1024 then
      Inc (pointer (Args), 1024);
     ArgSize := 0;
     Move (Path [1], Args^ [ArgSize], Length (Path));
     Inc (ArgSize, Length (Path));
     Args^ [ArgSize] := 0;
     Inc (ArgSize);
     {Now do the real arguments.}
     Move (ComLine [1], Args^ [ArgSize], Length (ComLine));
     Inc (ArgSize, Length (ComLine));
     Args^ [ArgSize] := 0;
     Inc (ArgSize);
     Args^ [ArgSize] := 0;
    end;
   Res.ExitCode := $FFFFFFFF;
   RC := DosExecPgm (ObjNameBuf, ObjBufSize, 0, Args, nil, Res, PChar (Path));
   if Args0 <> nil then
    FreeMem (Args0, MaxArgsSize);
   if RC = 0 then
    begin
     Result := Res.ExitCode;
     FreeMem (ObjNameBuf, ObjBufSize);
    end
   else
    begin
     if (RC = 190) or (RC = 191) then
      Result := StartSession;
    end;
  end
 else
  Result := StartSession;
 if RC <> 0 then
  begin
   ObjName := StrPas (ObjNameBuf);
   FreeMem (ObjNameBuf, ObjBufSize);
   if ComLine = '' then
    CommandLine := Path
   else
    CommandLine := Path + ' ' + ComLine;
   if ObjName = '' then
    E := EOSError.CreateFmt (SExecuteProcessFailed, [CommandLine, RC])
   else
    E := EOSError.CreateFmt (SExecuteProcessFailed + ' (' + ObjName + ')', [CommandLine, RC]);
   E.ErrorCode := Result;
   raise E;
  end;
end;


function ExecuteProcess (const Path: AnsiString;
                                  const ComLine: array of AnsiString;Flags:TExecuteFlags=[]): integer;

var
  CommandLine: AnsiString;
  I: integer;

begin
  Commandline := '';
  for I := 0 to High (ComLine) do
   if Pos (' ', ComLine [I]) <> 0 then
    CommandLine := CommandLine + ' ' + '"' + ComLine [I] + '"'
   else
    CommandLine := CommandLine + ' ' + Comline [I];
  ExecuteProcess := ExecuteProcess (Path, CommandLine);
end;



{****************************************************************************
                              Initialization code
****************************************************************************}

Initialization
  InitExceptions;       { Initialize exceptions. OS independent }
  InitInternational;    { Initialize internationalization settings }
  OnBeep:=@SysBeep;
Finalization
  DoneExceptions;
end.
