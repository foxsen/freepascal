{$ifndef ALLPACKAGES}
{$mode objfpc}{$H+}
program fpmake;

uses fpmkunit;

Var
  P : TPackage;
  T : TTarget;
begin
  With Installer do
    begin
{$endif ALLPACKAGES}

    P:=AddPackage('zlib');
{$ifdef ALLPACKAGES}
    P.Directory:='zlib';
{$endif ALLPACKAGES}
    P.Version:='2.7.1';
    P.OSes := AllUnixOSes+AllWindowsOSes+[os2,emx,netware,netwlibc]-[qnx];
    P.SourcePath.Add('src');

    T:=P.Targets.AddUnit('zlib.pp');


{$ifndef ALLPACKAGES}
    Run;
    end;
end.
{$endif ALLPACKAGES}
