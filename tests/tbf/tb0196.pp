{ %norun }
{ %fail }
{ %opt=-Sen -vn }

type
 tr = record
   x, y: longint;
 end;
 ta = array[1..10] of tr;

var
  a: ta;
  i: longint;
begin
  for i := low(a) to high(a) do
    with a[i] do
      begin
        x:=i*2;
        y:=i+5;
      end;
end.
