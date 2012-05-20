{ %target=darwin }
{ %cpu=powerpc,powerpc64,i386,x86_64,arm }

{$mode objfpc}
{$modeswitch objectivec1}

{ test program by saabino80 at alice in Italy for nested procedures in
  Objective-C methods }

Program Foo;
uses
        ctypes;

Type MyObjc= objcclass(NSObject)
Procedure nested; message 'nested';

End;
Procedure MyObjc.nested;

Procedure one;
Begin;
 WriteLn('Ciao');
End;
Begin
one;
End;

Var My:MyObjc;
Begin
My := MyObjc.alloc;
My.nested;
My.release;
End.

