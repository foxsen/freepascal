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

    P:=AddPackage('mad');
{$ifdef ALLPACKAGES}
    P.Directory:='mad';
{$endif ALLPACKAGES}
    P.Version:='2.7.1';
    P.OSes := [linux,win32,win64];
    P.SourcePath.Add('src');

    T:=P.Targets.AddUnit('mad.pas');


{$ifndef ALLPACKAGES}
    Run;
    end;
end.
{$endif ALLPACKAGES}
