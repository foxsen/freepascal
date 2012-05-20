{$ifndef bigfile}
{$ifdef fpc}
{$mode delphi}
{$else fpc}
{$define FPC_HAS_TYPE_EXTENDED}
{$endif fpc}
{$endif bigfile}

type 
{$ifdef FPC_COMP_IS_INT64}
  comp135 = double;
{$else FPC_COMP_IS_INT64}
  comp135 = comp;
{$endif FPC_COMP_IS_INT64}
procedure test135(a: shortint); overload;
  begin
    writeln('shortint called instead of widechar');
  end;

procedure test135(a: widechar); overload;
  begin
    writeln('widechar called instead of shortint');
    halt(1)
  end;

var
  x135: shortint;

  y135: widechar;
procedure dotest135;
var
  v: variant;

begin
  try
    v := x135;
    test135(v);
  except
    on E : TObject do
      halt(1);
  end;

  try
    v := y135;
    test135(v);
  except
    on E : TObject do
      halt(1);
  end;
end;

{$ifndef bigfile} begin
  dotest135;
end. {$endif not bigfile}
