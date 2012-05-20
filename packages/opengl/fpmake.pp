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

    P:=AddPackage('opengl');
{$ifdef ALLPACKAGES}
    P.Directory:='opengl';
{$endif ALLPACKAGES}
    P.Version:='2.7.1';
    P.OSes:=AllUnixOSes+[Win32,Win64];

    P.Dependencies.Add('x11',AllUnixOSes-[darwin,iphonesim]);
    if Defaults.CPU<>arm then
      P.Dependencies.Add('x11',[darwin]);

    P.SourcePath.Add('src');
    P.IncludePath.Add('src');

    T:=P.Targets.AddImplicitUnit('freeglut.pp',AllOSes-[morphos]);
    T:=P.Targets.AddUnit('glext.pp');
    T:=P.Targets.AddUnit('gl.pp');
    T:=P.Targets.AddUnit('glu.pp');
    T:=P.Targets.AddUnit('glut.pp');
    // T.Dependencies.Add('freeglut',AllOSes-[morphos]);
    T:=P.Targets.AddUnit('glx.pp',AllUnixOSes-[darwin,iphonesim]);
    if Defaults.CPU<>arm then
      T:=P.Targets.AddUnit('glx.pp',[darwin]);

    P.ExamplePath.Add('examples');
    P.Targets.AddExampleProgram('radblur.pp');
    P.Targets.AddExampleProgram('bounce.pp');
    P.Targets.AddExampleProgram('morph3d.pp');
    P.Targets.AddExampleProgram('glutdemo.pp');
    P.Targets.AddExampleProgram('glxtest.pp');
    P.Sources.AddSrc('readme');

{$ifndef ALLPACKAGES}
    Run;
    end;
end.
{$endif ALLPACKAGES}
