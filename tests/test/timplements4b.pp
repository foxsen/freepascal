{ %OPT=-gh }
{$ifdef fpc}
{$mode objfpc}
{$endif fpc}
uses
  classes;

type
  to1 = class(TObject,IInterface)
    fi : TInterfacedObject;
    property i : TInterfacedObject read fi implements IInterface;
  end;

var
  o1 : to1;
  i1,i2 : IInterface;
begin
  o1:=to1.create;
  o1.fi:=TInterfacedObject.Create;
  writeln('o1 and o1.fi created');
  i1:=o1;
  i1.QueryInterface(IInterface,i2);
  writeln('i2 queried the first time');
  if i2=nil then
    halt(1);
  writeln('setting o1.fi to nil');
  o1.fi:=nil;
  o1.free;
  try
    i1.QueryInterface(IInterface,i2);
    if i2=nil then
      halt(1);
  except
    writeln('ok');
    halt(0);
  end;
  halt(1)
end.

