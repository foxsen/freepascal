{$ifndef ALLPACKAGES}
{$mode objfpc}{$H+}
program fpmake;

uses fpmkunit;

Var
  P : TPackage;
begin
  With Installer do
    begin
{$endif ALLPACKAGES}

    P:=AddPackage('os2units');
{$ifdef ALLPACKAGES}
    P.Directory:='os2units';
{$endif ALLPACKAGES}
    P.Version:='2.7.1';
    P.OSes := [OS2,emx];
    P.SourcePath.Add('src');
//    P.Dependencies.Add('x11');
   // P.Targets.AddUnit('buildall.pas',[OS2]);
    P.Targets.AddUnit('clkdll.pas');
    P.Targets.AddUnit('dive.pas');
    P.Targets.AddUnit('ftpapi.pas');
    P.Targets.AddUnit('hwvideo.pas');
    P.Targets.AddUnit('lvm.pas');
    P.Targets.AddUnit('mciapi.pas');
    P.Targets.AddUnit('mcidrv.pas');
    P.Targets.AddUnit('mci.pas');
    P.Targets.AddUnit('mmbase.pas');
    P.Targets.AddUnit('mmio.pas');
//    P.Targets.AddUnit('som.pas');
    P.Targets.AddUnit('sw.pas');
//    P.Targets.AddUnit('wpstk.pp');

    P.Sources.AddSrc('readme.txt');

   // not compilable defunct for now

    P.ExamplePath.Add('examples');
    P.Targets.AddExampleProgram('mciapi1.pas');
    P.Targets.AddExampleProgram('mciapi2.pas');
    P.Targets.AddExampleProgram('clktest.pas');
    P.Targets.AddExampleProgram('ftptest.pas');
    P.Targets.AddExampleProgram('lvmtest.pas');
    P.Sources.AddExampleFiles('examples/*',false,'.');

{$ifndef ALLPACKAGES}
    Run;
    end;
end.
{$endif ALLPACKAGES}