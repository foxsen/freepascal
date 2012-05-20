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

    P:=AddPackage('regexpr');
{$ifdef ALLPACKAGES}
    P.Directory:='regexpr';
{$endif ALLPACKAGES}
    P.Version:='2.7.1';
    P.SourcePath.Add('src');

    // Sorokin's RegExpr
    T:=P.Targets.AddUnit('regexpr.pas');

    // RegEx from Joost
    T:=P.Targets.AddUnit('oldregexpr.pp');
    T:=P.Targets.AddUnit('regex.pp');

    T.ResourceStrings := True;

    P.ExamplePath.Add('examples');
    P.Targets.AddExampleProgram('testreg1.pp');
    P.Sources.AddExampleFiles('examples/*',false,'.');

{$ifndef ALLPACKAGES}
    Run;
    end;
end.
{$endif ALLPACKAGES}
