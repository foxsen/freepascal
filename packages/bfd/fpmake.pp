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

    P:=AddPackage('bfd');
{$ifdef ALLPACKAGES}
    P.Directory:='bfd';
{$endif ALLPACKAGES}
    P.Version:='2.7.1';
    P.Author := 'Library: Cygnus Support, header: by Uli Tessel';
    P.License := 'Library: GPL2 or later, header: LGPL with modification, ';
    P.HomepageURL := 'www.freepascal.org';
    P.Email := '';
    P.Description := 'Binary File Descriptor library.';
    P.NeedLibC:= true;
    P.OSes := [beos,haiku,freebsd,darwin,iphonesim,solaris,netbsd,openbsd,linux,aix];

    P.SourcePath.Add('src');

    T:=P.Targets.AddUnit('bfd.pas');

{$ifndef ALLPACKAGES}
    Run;
    end;
end.
{$endif ALLPACKAGES}
