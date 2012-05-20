{$ifndef ALLPACKAGES}
{$mode objfpc}{$H+}
program fpmake;

uses fpmkunit;

{$endif not ALLPACKAGES}

procedure add_dblib;

Const
  DBLibOSes         = [linux,freebsd,netbsd,openbsd,win32,win64,haiku];

Var
  P : TPackage;
  T : TTarget;
begin
  With Installer do
    begin
      P:=AddPackage('dblib');
{$ifdef ALLPACKAGES}
      P.Directory:='dblib';
{$endif ALLPACKAGES}
      P.Version:='1.0';
      P.Author := 'Library: (FreeTDS/Microsoft), header: Ladislav Karrach';
      P.License := 'Library: FreeTDS License, header: LGPL with modification, ';
      P.HomepageURL := 'www.freepascal.org';
      P.Email := '';
      P.Description := 'Headers for the MS SQL Server RDBMS';
      P.NeedLibC:= true;  // true for headers that indirectly link to libc?

      P.SourcePath.Add('src');
      P.IncludePath.Add('src');

      T:=P.Targets.AddUnit('dblib.pp',DBLibOSes);
    end;
end;

{$ifndef ALLPACKAGES}
begin
  add_dblib;
  Installer.Run;
end.
{$endif ALLPACKAGES}
