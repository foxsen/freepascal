{$mode objfpc}
unit tw11431;

interface

uses sysutils;

type

  generic IGenericCollection<_T> = interface
  end;

  generic CGenericCollection<_T> = class(TInterfacedObject, specialize IGenericCollection<_T>)
  end;

implementation


end.
