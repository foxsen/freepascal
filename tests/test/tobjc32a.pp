{ %fail }

{ %target=darwin }
{ %cpu=powerpc,powerpc64,i386,x86_64,arm }

{$mode objfpc}
{$modeswitch objectivec1}

type
  tc = objcclass(NSObject)
    function test: ansistring; message 'test';
  end;

procedure tc.test: ansistring;
  begin
  end;

begin
end.
