{ %target=darwin }
{ %cpu=powerpc,powerpc64,i386,x86_64,arm }

{ Written by Jonas Maebe in 2009, released into the Public Domain }

{$mode objfpc}
{$modeswitch objectivec1}

type
  { should succeed because both methods have the same selector }
  ta = objcclass(NSObject)
    function proc1(para: longint): longint; message 'proc1:';
  end;

  tb = objcclass(NSObject)
    function proc1(para: longint): longint; message 'proc1:';
  end;

function ta.proc1(para: longint): longint;
begin
  writeln(para);
  proc1:=para;
end;

function tb.proc1(para: longint): longint;
begin
  writeln(para);
  proc1:=para;
end;

var
  a: id;
begin
  a:=ta.alloc.init;
  a.proc1(5);
end.
