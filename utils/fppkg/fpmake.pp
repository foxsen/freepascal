{$ifndef ALLPACKAGES}
{$mode objfpc}{$H+}
program fpmake;

uses fpmkunit;
{$endif ALLPACKAGES}

procedure add_fppkg_util;

const
  lnetOSes = [linux,beos,haiku,freebsd,netbsd,openbsd,darwin,iphonesim,solaris,win32,win64,wince,aix];

Var
  P : TPackage;
  T : TTarget;

begin
  With Installer do
    begin
    P:=AddPackage('fppkg-util');

    P.Author := '<various>';
    P.License := 'LGPL with modification';
    P.HomepageURL := 'www.freepascal.org';
    P.Email := '';
    P.Description := 'Free Pascal package repository utility.';
    P.NeedLibC:= false;

{$ifdef ALLPACKAGES}
    P.Directory:='fppkg';
{$endif ALLPACKAGES}
    P.Version:='2.7.1';

    P.SourcePath.Add('lnet',lnetOSes);
    P.IncludePath.Add('lnet/sys',lnetOSes);

    P.SupportBuildModes:=[bmOneByOne];

    P.Dependencies.Add('fcl-base');
    P.Dependencies.Add('fcl-xml');
    P.Dependencies.Add('fcl-process');
    P.Dependencies.Add('fcl-net');
    P.Dependencies.Add('paszlib');
    //P.Dependencies.Add('libcurl',[beos,haiku,freebsd,darwin,iphonesim,solaris,netbsd,openbsd,linux,aix]);
    P.Dependencies.Add('fppkg');
    P.Dependencies.Add('univint', [Darwin, iphonesim]);

    T:=P.Targets.AddProgram('fppkg.pp');

    T := P.Targets.AddUnit('pkglnet.pp', lnetOSes);
    T.Dependencies.AddUnit('lnet');
    T.Dependencies.AddUnit('lftp');
    T.Dependencies.AddUnit('lhttp');
    T.Install:=false;
    P.Targets.AddUnit('lnet/fastcgi_base.pp', lnetOSes).install:=false;
    P.Targets.AddUnit('lnet/lcontrolstack.pp', lnetOSes).install:=false;
    P.Targets.AddUnit('lnet/lhttp.pp', lnetOSes).install:=false;
    P.Targets.AddUnit('lnet/lmimestreams.pp', lnetOSes).install:=false;
    P.Targets.AddUnit('lnet/lmimewrapper.pp', lnetOSes).install:=false;
    P.Targets.AddUnit('lnet/lprocess.pp', lnetOSes).install:=false;
    P.Targets.AddUnit('lnet/lspawnfcgi.pp', lnetOSes).install:=false;
    P.Targets.AddUnit('lnet/ltelnet.pp', lnetOSes).install:=false;
    P.Targets.AddUnit('lnet/lcommon.pp', lnetOSes).install:=false;
    P.Targets.AddUnit('lnet/levents.pp', lnetOSes).install:=false;
    P.Targets.AddUnit('lnet/lftp.pp', lnetOSes).install:=false;
    P.Targets.AddUnit('lnet/lhttputil.pp', lnetOSes).install:=false;
    P.Targets.AddUnit('lnet/lmimetypes.pp', lnetOSes).install:=false;
    P.Targets.AddUnit('lnet/lnet.pp', lnetOSes).install:=false;
    P.Targets.AddUnit('lnet/lstrbuffer.pp', lnetOSes).install:=false;
    P.Targets.AddUnit('lnet/ltimer.pp', lnetOSes).install:=false;

    P.Sources.AddSrc('lnet/lsmtp.pp');
    P.Sources.AddSrc('lnet/lwebserver.pp');
    P.Sources.AddSrc('lnet/lfastcgi.pp');
    P.Sources.AddSrc('lnet/lcontainers.inc');
    P.Sources.AddSrc('lnet/lcontainersh.inc');
    P.Sources.AddSrc('lnet/lws2tcpip.pp');
    P.Sources.AddSrc('lnet/sys/lepolleventerh.inc');
    P.Sources.AddSrc('lnet/sys/lkqueueeventerh.inc');
    P.Sources.AddSrc('lnet/sys/lspawnfcgiwin.inc');
    P.Sources.AddSrc('lnet/sys/lepolleventer.inc');
    P.Sources.AddSrc('lnet/sys/lkqueueeventer.inc');
    P.Sources.AddSrc('lnet/sys/lspawnfcgiunix.inc');
    P.Sources.AddSrc('lnet/sys/osunits.inc');

    end;
end;

{$ifndef ALLPACKAGES}
begin
  add_fppkg_util;
  Installer.Run;
end.
{$endif ALLPACKAGES}




