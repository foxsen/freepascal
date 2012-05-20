{ %NORUN }

{ this tests that nested non-generic structured types can be used inside
  generics - here: object in object }
program tgeneric68;

{$ifdef fpc}
  {$mode delphi}
{$endif}

type
  TTest<T> = object
  type
    TTestSub = object
      function Test(a: T): T;
    end;
  end;

function TTest<T>.TTestSub.Test(a: T): T;
begin
  Result := a;
end;

var
  t: TTest<Integer>.TTestSub;
begin
  t.Test(42);
end.
