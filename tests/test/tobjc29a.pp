{ %target=darwin }
{ %cpu=powerpc,powerpc64,i386,x86_64,arm }
{ %fail }

{ Written by Jonas Maebe in 2009, released into the public domain }

{$mode objfpc}
{$modeswitch objectivec1}

type
  ta = objcclass(NSObject)
    function tabaseproc(cp: longint): double; message 'tabaseproc:';
  end;

  ca = objccategory(ta)
    function tabaseproc(cp: longint): double; reintroduce;
  end;

function ta.tabaseproc(cp: longint): double;
begin
  result:=cp;
  halt(1);
end;

function ca.tabaseproc(cp: longint): double;
begin
  result:=inherited tabaseproc(cp+1);
end;

var
  a: ta;
begin
  a:=ta(ta.alloc).init;
  if a.tabaseproc(4320)<>123.625 then
    halt(2);
  a.release;
end.
