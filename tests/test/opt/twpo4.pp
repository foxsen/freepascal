{ %target=darwin,linux,freebsd,solaris,aix }
{ %wpoparas=devirtcalls,optvmts,symbolliveness }
{ %wpopasses=2 }
{ %opt=-CX -XX -Xs- -g- }

{ -g- because DWARF debug info does not work with smart linking }

{ not enabled for windows yet because symbolliveness doesn't work there without
  installing "nm" (until implemented by way of internal linker there)
}

{$mode objfpc}

{ test case that can be optimised based on taking into account dead code
  stripping
}

type
  tbase = class
    procedure test; virtual;
  end;

  tchild1 = class(tbase)
    procedure test; override;
  end;

  tchild2 = class(tbase)
    procedure test; override;
  end;

procedure tbase.test;
begin
  halt(1);
end;

var
  a: longint;

procedure tchild1.test;
begin
  if a<>1 then
    halt(2);
end;

procedure tchild2.test;
begin
  if a<>2 then
    halt(3);
end;

procedure notcalled;
var
  bb: tbase;
begin
  bb:=tchild2.create;
  bb.test;
  bb.free;
end;

var
  bb: tbase;
begin
  bb:=tchild1.create;
  a:=1;
  bb.test;
  a:=2;
  bb.free;
end.
