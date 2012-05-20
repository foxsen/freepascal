{$ifndef ALLPACKAGES}
{$mode objfpc}{$H+}
program fpmake;

uses fpmkunit;
{$endif ALLPACKAGES}

procedure add_fpdoc;

Var
  P : TPackage;
  T : TTarget;

begin
  With Installer do
    begin
    P:=AddPackage('fpdoc');

    P.Author := '<various>';
    P.License := 'LGPL with modification';
    P.HomepageURL := 'www.freepascal.org';
    P.Email := '';
    P.Description := 'Free Pascal documentation generation utility.';
    P.NeedLibC:= false;

    P.Dependencies.Add('fcl-base');
    P.Dependencies.Add('fcl-xml');
    P.Dependencies.Add('fcl-passrc');
    P.Dependencies.Add('chm');
    P.Dependencies.Add('univint',[darwin,iphonesim]);


{$ifdef ALLPACKAGES}
    P.Directory:='fpdoc';
{$endif ALLPACKAGES}
    P.Version:='2.7.1';

    P.Options.Add('-S2h');

    T:=P.Targets.AddProgram('fpdoc.pp');
    T.Dependencies.AddUnit('dglobals');
    T.Dependencies.AddUnit('dw_ipflin');
    T.Dependencies.AddUnit('dwriter');
    T.Dependencies.AddUnit('dw_xml');
    T.Dependencies.AddUnit('dglobals');
    T.Dependencies.AddUnit('sh_pas');
    T.Dependencies.AddUnit('dw_html');
    T.Dependencies.AddUnit('dw_latex');
    T.Dependencies.AddUnit('dwlinear');
    T.Dependencies.AddUnit('dw_txt');
    T.Dependencies.AddUnit('dw_linrtf');

    T:=P.Targets.AddProgram('makeskel.pp');
    T.ResourceStrings:=true;
    T.Dependencies.AddUnit('dglobals');

    T:=P.Targets.AddProgram('unitdiff.pp');
    T.ResourceStrings:=true;
    T:=P.Targets.AddProgram('fpclasschart.pp');
    T.ResourceStrings:=true;

    T := P.Targets.AddUnit('dglobals.pp');
    T.install:=false;
    T.ResourceStrings:=true;

    T := P.Targets.AddUnit('dwriter.pp');
    T.install:=false;
    T.ResourceStrings:=true;

    T := P.Targets.AddUnit('fpdocxmlopts.pas');
    T.install:=false;
    T.ResourceStrings:=true;

    P.Targets.AddUnit('dw_xml.pp').install:=false;
    P.Targets.AddUnit('sh_pas.pp').install:=false;
    P.Targets.AddUnit('dw_html.pp').install:=false;
    P.Targets.AddUnit('dw_latex.pp').install:=false;
    P.Targets.AddUnit('dw_txt.pp').install:=false;
    P.Targets.AddUnit('dw_man.pp').install:=false;
    P.Targets.AddUnit('dwlinear.pp').install:=false;
    P.Targets.AddUnit('dw_linrtf.pp').install:=false;
    P.Targets.AddUnit('dw_dxml.pp').install:=false;
    P.Targets.AddUnit('fpdocproj.pas').install:=false;
    P.Targets.AddUnit('mkfpdoc.pp').install:=false;
    P.Targets.AddUnit('dw_ipflin.pas').install:=false;
    end;
end;

{$ifndef ALLPACKAGES}
begin
  add_fpdoc;
  Installer.Run;
end.
{$endif ALLPACKAGES}




