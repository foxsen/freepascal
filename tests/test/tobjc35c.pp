{ %target=darwin }
{ %cpu=powerpc,powerpc64,i386,x86_64,arm }
{ %fail }

{ Written by Jonas Maebe in 2010, released into the public domain }

{$mode objfpc}
{$modeswitch objectivec1}

type
  NSArray = objcclass external;

var
  a: NSObject;
begin
  a:=NSArray.alloc.init;
end.
