{$ifndef ALLPACKAGES}
{$mode objfpc}{$H+}
program fpmake;

uses fpmkunit;
{$endif ALLPACKAGES}

procedure add_h2pas;

Var
  P : TPackage;
  T : TTarget;

begin
  With Installer do
    begin
    P:=AddPackage('h2pas');

    P.Author := '<various>';
    P.License := 'LGPL with modification';
    P.HomepageURL := 'www.freepascal.org';
    P.Email := '';
    P.Description := 'An utility to create Pascal header files from c header files.';
    P.NeedLibC:= false;

{$ifdef ALLPACKAGES}
    P.Directory:='h2pas';
{$endif ALLPACKAGES}
    P.Version:='2.7.1';

    P.Options.Add('-Sg');

    p.Commands.AddCommand(caBeforeCompile,'pyacc','h2pas.y','h2pas.pas','h2pas.y');
    p.Commands.AddCommand(caBeforeCompile,'plex','scan.l','scan.pas','scan.l');

    T:=P.Targets.AddProgram('h2pas.pas');
    T.Dependencies.AddUnit('h2poptions');
    T.Dependencies.AddUnit('h2plexlib');
    T.Dependencies.AddUnit('scan');
    T.Dependencies.AddUnit('h2pyacclib');
    T.Dependencies.AddUnit('converu');

    T:=P.Targets.AddUnit('scan.pas');
    T.Install:=false;
    T.Dependencies.AddUnit('converu');
    T.Dependencies.AddUnit('h2poptions');

    T:=P.Targets.AddProgram('h2paspp.pas');

    P.Targets.AddUnit('h2poptions.pas').install:=false;
    P.Targets.AddUnit('h2plexlib.pas').install:=false;
    P.Targets.AddUnit('h2pyacclib.pas').install:=false;
    P.Targets.AddUnit('converu.pas').install:=false;
    end;
end;

{$ifndef ALLPACKAGES}
begin
  add_h2pas;
  Installer.Run;
end.
{$endif ALLPACKAGES}




