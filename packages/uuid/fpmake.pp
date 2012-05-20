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

    P:=AddPackage('uuid');
{$ifdef ALLPACKAGES}
    P.Directory:='uuid';
{$endif ALLPACKAGES}
    P.Version:='2.7.1';
    P.SourcePath.Add('src');
    P.OSes := [linux];

    T:=P.Targets.AddUnit('libuuid.pp');
    T:=P.Targets.AddUnit('macuuid.pp');

    P.Sources.AddSrc('README.txt');

    P.ExamplePath.Add('examples');
    P.Targets.AddExampleProgram('testlibuid.pp');
    P.Targets.AddExampleProgram('testuid.pp');
    P.Sources.AddExampleFiles('examples/*',false,'.');


{$ifndef ALLPACKAGES}
    Run;
    end;
end.
{$endif ALLPACKAGES}
