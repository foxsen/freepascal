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

    P:=AddPackage('modplug');
{$ifdef ALLPACKAGES}
    P.Directory:='modplug';
{$endif ALLPACKAGES}
    P.Version:='2.7.1';
    P.OSes := [linux];
    P.SourcePath.Add('src');

    T:=P.Targets.AddUnit('modplug.pas');


{$ifndef ALLPACKAGES}
    Run;
    end;
end.
{$endif ALLPACKAGES}
