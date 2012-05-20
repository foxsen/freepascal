{ %target=darwin }
{ %cpu=powerpc,powerpc64,i386,x86_64,arm }
{ %opt=-vh -Seh }
{ %fail }

{ Written by Jonas Maebe in 2009, released into the public domain }

{$mode objfpc}
{$modeswitch objectivec1}

uses
  ctypes;

type
  TMyTestClass = objcclass(NSObject)
  end;

  TMyTestClass2 = objcclass external name 'TMyTestClass' (NSObject)
    { should give a hint because of a missing 'override' }
    function hash: cuint;
  end;

var
  a: id;
  b: tmytestclass2;
begin
  b:=nil;
  if assigned(b) then
    ;
  { avoid warnings/hints about unused types/variables }
  a:=TMyTestClass.alloc;
  tmytestclass(a).Retain;
end.
