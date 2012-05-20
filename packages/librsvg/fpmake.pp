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

    P:=AddPackage('rsvg');
{$ifdef ALLPACKAGES}
    P.Directory:='librsvg';
{$endif ALLPACKAGES}
    P.OSes := [beos,haiku,freebsd,netbsd,openbsd,linux,win32,aix];
    // Do not build x11 on iPhone (=arm-darwin)
    if Defaults.CPU<>arm then
      P.OSes := P.OSes + [darwin];
    P.Version:='2.7.1';
    P.SourcePath.Add('src');
    P.IncludePath.Add('src');
    P.Dependencies.Add('gtk2');

  T:=P.Targets.AddUnit('rsvg.pas');

{$ifndef ALLPACKAGES}
    Run;
    end;
end.
{$endif ALLPACKAGES}
