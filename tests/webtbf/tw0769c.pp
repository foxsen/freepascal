{ %OPT=-Sew -vw }
{ %fail }
{ this should generate a warning
  because s is not initialized }

{$mode tp}

Program test;

type
  SimpleProc = function : integer;

procedure test_provar;
var x,y:integer;
    s : SimpleProc;

begin
  {y:=5;
  for x:=0 to 10 do if x<y then writeln(x);}
  x:=s;
end;

begin
end.
