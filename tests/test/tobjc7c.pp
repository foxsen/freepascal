{ %target=darwin }
{ %cpu=powerpc,powerpc64,i386,x86_64,arm }
{ %norun }

{ Written by Jonas Maebe in 2009, released into the public domain }

{$mode objfpc}
{$modeswitch objectivec1}

uses
  uobjc7;

type
{ fake external name to avoid linking errors because
  we add external references to ensure that all
  necessary libraries are linked, like gcc does }
  tobjcclass = objcclass external name 'NSObject' (tobjcprot)
    procedure isrequired;
    procedure isoptional;
    procedure alsorequired;
  end; 


begin
end.
