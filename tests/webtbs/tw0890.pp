{$ifdef FPC}
  {$MODE TP}
{$endif FPC}

unit tw0890;

INTERFACE

procedure GetScreenLine(const x: Integer);

function dummy2(var x : integer) : integer;
function dummystr(x : integer) : string;

IMPLEMENTATION


procedure GetScreenLine;
begin
end;

function dummy2;
begin
  dummy2:=x;
  x:=0;
end;

function dummystr;
var
  s : string;
begin
  str(x,s);
  dummystr:=s;
end;

begin
end.
