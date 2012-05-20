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

    P:=AddPackage('utmp');
{$ifdef ALLPACKAGES}
    P.Directory:='utmp';
{$endif ALLPACKAGES}
    P.Version:='2.7.1';
    P.SourcePath.Add('src');
    P.OSes := [beos,haiku,freebsd,darwin,iphonesim,solaris,netbsd,openbsd,linux];

    T:=P.Targets.AddUnit('utmp.pp');

    P.ExamplePath.Add('examples');
    P.Targets.AddExampleProgram('testutmp.pp');

{$ifndef ALLPACKAGES}
    Run;
    end;
end.
{$endif ALLPACKAGES}
