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

    P:=AddPackage('oggvorbis');
{$ifdef ALLPACKAGES}
    P.Directory:='oggvorbis';
{$endif ALLPACKAGES}
    P.Version:='2.7.1';
    P.SourcePath.Add('src');
    P.OSes := [linux,win32,wince];
//    P.Dependencies.Add('x11');

   T:=P.Targets.AddUnit('ogg.pas');
   T:=P.Targets.AddUnit('vorbis.pas');
   with T.Dependencies do
     begin
       AddUnit('ogg');
     end;

{$ifndef ALLPACKAGES}
    Run;
    end;
end.
{$endif ALLPACKAGES}
