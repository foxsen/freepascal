{ %OPT=-gl }
program Project1;

{$mode objfpc}{$H+}

type
  MyClass = class(TObject)
  private
    FClassVar: integer; static;
  end;

begin
  myclass.fclassvar := 1;
end.

