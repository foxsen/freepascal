{ helpers may override existing default properties }
program tchlp7;

{$ifdef fpc}
  {$mode delphi}
{$endif}
{$apptype console}

type
  TTest = class
  private
    function GetTest(aIndex: Integer): Integer;
  public
    property Test[Index: Integer]: Integer read GetTest; default;
  end;

  TTestHelper = class helper for TTest
    function GetTest(aIndex: Integer): Integer;
    property Test[Index: Integer]: Integer read GetTest; default;
  end;

function TTest.GetTest(aIndex: Integer): Integer;
begin
  Result := - aIndex;
end;

function TTestHelper.GetTest(aIndex: Integer): Integer;
begin
  Result := aIndex;
end;

var
  t: TTest;
  res: Integer;
begin
  t := TTest.Create;
  res := t[3];
  Writeln('value: ', res);
  if res <> 3 then
    Halt(1);
  Writeln('ok');
end.
