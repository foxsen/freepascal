{%skiptarget=wince}

{ This file is to check if there is some memory corruption
  due to startup code with argument loading
  go32v2 target had this problem
  close to 2.2 release 2007-03-27 pierre }

program create_startup_test_crash;

{$ifdef go32v2}
{$define HasExeSuffix}
{$endif}
{$ifdef win32}
{$define HasExeSuffix}
{$endif}
{$ifdef win64}
{$define HasExeSuffix}
{$endif}
{$ifdef wince}
{$define HasExeSuffix}
{$endif}
{$ifdef os2}
{$define HasExeSuffix}
{$endif}
{$ifdef emx}
{$define HasExeSuffix}
{$endif}
{$ifdef wdosx}
{$define HasExeSuffix}
{$endif}
{$ifdef netware}
{$define HasNlmSuffix}
{$endif}
{$ifdef netwlibc}
{$define HasNlmSuffix}
{$endif}

uses
  dos;

const
  Prefix =
{$ifdef Unix}
  './'
{$else}
  ''
{$endif}
  ;
  ExeSuffix =
{$ifdef HasExeSuffix}
  '.exe'
{$else}
  {$ifdef HasNlmSuffix}
    '.nlm'
  {$else}
    ''
  {$endif}
{$endif}
  ;
const
  MAX = 255;

var
  cmd,
  arg : string;
  i, first_wrong : longint;
const
  Everything_ok : boolean = true;
begin
  cmd:=Prefix+'targ1a'+ExeSuffix;
  arg:='';
  first_wrong:=-1;
  for i:=0 to MAX do
    begin
      Writeln(stderr,'Going to call "',cmd,'" with arg = "',arg,'"');
      Writeln(stderr,'arg length =',length(arg));
      Exec(cmd,arg);
      if (DosExitCode<>0) or (DosError<>0) then
        begin
          Writeln(stderr,'Crash detected, DosError=', DosError);
          Writeln(stderr,'DosExitCode=',DosExitCode);
          if first_wrong=-1 then
            first_wrong:=i;
          Everything_ok := false;
        end;
      arg:=arg+'a';
    end;
  if Everything_ok then
    begin
      Writeln(stderr,'Test successful: no memory corruption occurs');
    end
  else
    begin
      Writeln(stderr,'Test fails: Memory corruption occurs');
      Writeln(stderr,'First arg length where error appears is ',first_wrong);
      if first_wrong<100 then
        RunError(1)
      else
        Writeln(stderr,'Warning: when using Dos.Exec, arg length must be smaller than ',first_wrong);
    end;
end.

