{ %target=darwin }
{ %cpu=powerpc,powerpc64,i386,x86_64,arm }
{ %fail }

{ Written by Jonas Maebe in 2009, released into the public domain }

{$modeswitch objectivec1}

uses
  uobjc27a;

var
  a: ta;

begin
  { da_category method is declared in uobjc27a, which is used in the
    implementation of uobjc27b -> should not be visible here }
  a.da_categorymethod;
end.
