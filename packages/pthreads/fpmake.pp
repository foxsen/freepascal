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

    P:=AddPackage('pthreads');
{$ifdef ALLPACKAGES}
    P.Directory:='pthreads';
{$endif ALLPACKAGES}
    P.Version:='2.7.1';
    P.OSes := [beos,haiku,freebsd,darwin,iphonesim,solaris,netbsd,openbsd,linux,aix];
    P.SourcePath.Add('src');
    P.IncludePath.Add('src');

    T:=P.Targets.AddUnit('pthreads.pp');
    with T.Dependencies do
      begin
        AddInclude('pthrlinux.inc',[Linux]);
        AddInclude('pthrbeos.inc',[Beos]);
        AddInclude('pthrsnos.inc',[Solaris]);
        AddInclude('pthrbsd.inc',AllBSDOses);
        AddInclude('pthraix.inc',[AIX]);
      end;

{$ifndef ALLPACKAGES}
    Run;
    end;
end.
{$endif ALLPACKAGES}
