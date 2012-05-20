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

    P:=AddPackage('unzip');
{$ifdef ALLPACKAGES}
    P.Directory:='unzip';
{$endif ALLPACKAGES}
    P.Version:='2.7.1';
    P.SourcePath.Add('src');
    P.OSes := P.OSes - [nativent];

    T:=P.Targets.AddUnit('unzip51g.pp');
      with T.Dependencies do
        begin
          AddUnit('ziptypes');
        end;
    T:=P.Targets.AddUnit('ziptypes.pp');
    T:=P.Targets.AddUnit('unzipdll.pp',[emx,os2]);
{$ifndef ALLPACKAGES}
    Run;
    end;
end.
{$endif ALLPACKAGES}
