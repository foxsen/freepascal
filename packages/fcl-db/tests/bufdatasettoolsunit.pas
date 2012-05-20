unit BufDatasetToolsUnit;

{ Sets up bufdataset for testing.
Tests expect Get*Dataset tho return a dataset with structure and test data, but closed.
A closed BufDataset normally has no data, so these tests won't work.

To circumvent this, this unit saves the dataset contents to file and reloads them on opening using BufDataset persistence mechanism.

}
{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, toolsunit,
  db,
  BufDataset;

type
{ TbufdatasetConnector }

  { TbufdatasetDBConnector }

  TbufdatasetDBConnector = class(TDBConnector)
  private
    FUniDirectional: boolean;
   protected
    procedure CreateNDatasets; override;
    procedure CreateFieldDataset; override;
    procedure DropNDatasets; override;
    procedure DropFieldDataset; override;
    Function InternalGetNDataset(n : integer) : TDataset; override;
    Function InternalGetFieldDataset : TDataSet; override;
    procedure SetTestUniDirectional(const AValue: boolean); override;
    function GetTestUniDirectional: boolean; override;
  end;

implementation

type

  { TPersistentBufDataSet }

  TPersistentBufDataSet=class(TBufDataset)
    private
      TempFileName:string;
    public
      destructor Destroy; override;
  end;

{ TPersistentBufDataSet }

destructor TPersistentBufDataSet.Destroy;
begin
  Close; // no locks on TempFileName
  DeleteFile(TempFileName);
  inherited Destroy;
end;

{ TbufdatasetDBConnector }

procedure TbufdatasetDBConnector.CreateNDatasets;
begin
// All datasets are created in InternalGet*Dataset
end;

procedure TbufdatasetDBConnector.CreateFieldDataset;
begin
  // All datasets are created in InternalGet*Dataset
end;

procedure TbufdatasetDBConnector.DropNDatasets;
begin
  // All datasets are created in InternalGet*Dataset and cleaned up when destroyed
end;

procedure TbufdatasetDBConnector.DropFieldDataset;
begin
  // All datasets are created in InternalGet*Dataset and cleaned up when destroyed
end;

function TbufdatasetDBConnector.InternalGetNDataset(n: integer): TDataset;
var BufDataset  : TPersistentBufDataSet;
    i      : integer;

begin
  BufDataset := TPersistentBufDataSet.Create(nil);
  BufDataset.FieldDefs.Add('ID',ftInteger);
  BufDataset.FieldDefs.Add('NAME',ftString,50);
  BufDataset.CreateDataset;
  BufDataset.Open;
  for i := 1 to n do
    begin
    BufDataset.Append;
    BufDataset.FieldByName('ID').AsInteger := i;
    BufDataset.FieldByName('NAME').AsString := 'TestName' + inttostr(i);
    BufDataset.Post;
    end;
  BufDataset.TempFileName:=GetTempFileName;
  BufDataset.FileName:=BufDataset.TempFileName;
  BufDataset.Close; // Save data into file
  Result := BufDataset;
end;

function TbufdatasetDBConnector.InternalGetFieldDataset : TDataSet;


var BufDataset  : TPersistentBufDataSet;
    i      : integer;

begin
  // Values >= 24:00:00.000 can't be handled by bufdataset
  testTimeValues[2] := '23:59:59.000';
  testTimeValues[3] := '23:59:59.003';

  BufDataset := TPersistentBufDataSet.Create(nil);
  with BufDataset do
    begin
    UniDirectional := FUniDirectional;
    FieldDefs.Add('ID',ftInteger);
    FieldDefs.Add('FSTRING',ftString,10);
    FieldDefs.Add('FSMALLINT',ftSmallint);
    FieldDefs.Add('FINTEGER',ftInteger);
    // Not supported by BufDataset:
    // FieldDefs.Add('FWORD',ftWord);
    FieldDefs.Add('FBOOLEAN',ftBoolean);
    FieldDefs.Add('FFLOAT',ftFloat);
    FieldDefs.Add('FCURRENCY',ftCurrency);
    FieldDefs.Add('FBCD',ftBCD);
    FieldDefs.Add('FDATE',ftDate);
    FieldDefs.Add('FTIME',ftTime);
    FieldDefs.Add('FDATETIME',ftDateTime);
    FieldDefs.Add('FLARGEINT',ftLargeint);
    CreateDataset;
    Open;
    for i := 0 to testValuesCount-1 do
    begin
      Append;
      FieldByName('ID').AsInteger := i;
      FieldByName('FSTRING').AsString := testStringValues[i];
      FieldByName('FSMALLINT').AsInteger := testSmallIntValues[i];
      FieldByName('FINTEGER').AsInteger := testIntValues[i];
      FieldByName('FBOOLEAN').AsBoolean := testBooleanValues[i];
      FieldByName('FFLOAT').AsFloat := testFloatValues[i];
      FieldByName('FCURRENCY').AsCurrency := testCurrencyValues[i];
      FieldByName('FBCD').AsCurrency := testCurrencyValues[i];
      FieldByName('FDATE').AsDateTime := StrToDateTime(testDateValues[i], Self.FormatSettings);
      FieldByName('FTIME').AsDateTime := StrToTime(testTimeValues[i], Self.FormatSettings);
      FieldByName('FLARGEINT').AsLargeInt := testLargeIntValues[i];
      Post;
    end;
    BufDataset.TempFileName:=GetTempFileName;
    BufDataset.FileName:=BufDataset.TempFileName;
    Close; // Save data into file
    end;
  Result := BufDataset;
end;

procedure TbufdatasetDBConnector.SetTestUniDirectional(const AValue: boolean);
begin
  FUniDirectional := AValue;
end;

function TbufdatasetDBConnector.GetTestUniDirectional: boolean;
begin
  Result := FUniDirectional;
end;

initialization
  RegisterClass(TbufdatasetDBConnector);
end.

