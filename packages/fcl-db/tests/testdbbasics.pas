unit TestDBBasics;

{$IFDEF FPC}
  {$mode Delphi}{$H+}
{$ENDIF}

interface

uses
{$IFDEF FPC}
  fpcunit, testutils, testregistry, testdecorator,
{$ELSE FPC}
  TestFramework,
{$ENDIF FPC}
  Classes, SysUtils, db, ToolsUnit;

type

  { TTestDBBasics }

  TTestDBBasics = class(TTestCase)
  private
    procedure TestfieldDefinition(AFieldType : TFieldType;ADatasize : integer;var ADS : TDataset; var AFld: TField);
    procedure TestcalculatedField_OnCalcfields(DataSet: TDataSet);

  protected
    procedure SetUp; override;
    procedure TearDown; override;
  published
    procedure TestSetFieldValues;
    procedure TestGetFieldValues;

    procedure TestSupportIntegerFields;
    procedure TestSupportSmallIntFields;
    procedure TestSupportStringFields;
    procedure TestSupportBooleanFields;
    procedure TestSupportFloatFields;
    procedure TestSupportLargeIntFields;
    procedure TestSupportDateFields;
    procedure TestSupportTimeFields;
    procedure TestSupportCurrencyFields;
    procedure TestSupportBCDFields;
    procedure TestSupportfmtBCDFields;
    procedure TestSupportFixedStringFields;

    procedure TestDoubleClose;
    procedure TestCalculatedField;
    procedure TestAssignFieldftString;
    procedure TestAssignFieldftFixedChar;
    procedure TestSelectQueryBasics;
    procedure TestPostOnlyInEditState;
    procedure TestMove;                    // bug 5048
    procedure TestActiveBufferWhenClosed;
    procedure TestEOFBOFClosedDataset;
    procedure TestLayoutChangedEvents;
    procedure TestDataEventsResync;
    procedure TestRecordcountAfterReopen;  // partly bug 8228
    procedure TestdeFieldListChange;
    procedure TestExceptionLocateClosed;    // bug 13938
    procedure TestCanModifySpecialFields;
  end;

  { TTestBufDatasetDBBasics }
{$ifdef fpc}
  TTestBufDatasetDBBasics = class(TTestCase)
  private
    procedure FTestXMLDatasetDefinition(ADataset : TDataset);
    procedure TestAddIndexFieldType(AFieldType : TFieldType; ActiveDS : boolean);
  protected
    procedure SetUp; override;
    procedure TearDown; override;
  published
    procedure TestClosedIndexFieldNames; // bug 16695
    procedure TestFileNameProperty;
    procedure TestClientDatasetAsMemDataset;
    procedure TestSafeAsXML;
    procedure TestIsEmpty;
    procedure TestBufDatasetCancelUpd; //bug 6938
    procedure TestBufDatasetCancelUpd1;
    procedure TestMultipleDeleteUpdateBuffer;
    procedure TestDoubleDelete;
    procedure TestReadOnly;
    procedure TestMergeChangeLog;
  // index tests
    procedure TestAddIndexInteger;
    procedure TestAddIndexSmallInt;
    procedure TestAddIndexBoolean;
    procedure TestAddIndexFloat;
    procedure TestAddIndexLargeInt;
    procedure TestAddIndexDateTime;
    procedure TestAddIndexCurrency;
    procedure TestAddIndexBCD;

    procedure TestAddIndex;
    procedure TestAddDescIndex;
    procedure TestAddCaseInsIndex;
    procedure TestInactSwitchIndex;

    procedure TestAddIndexActiveDS;
    procedure TestAddIndexEditDS;

    procedure TestIndexFieldNames;
    procedure TestIndexFieldNamesAct;

    procedure TestIndexCurRecord;

    procedure TestAddDblIndex;
    procedure TestIndexEditRecord;
    procedure TestIndexAppendRecord;
  end;

{$endif fpc}

  TTestUniDirectionalDBBasics = class(TTestDBBasics)
  end;

  { TTestCursorDBBasics }

  TTestCursorDBBasics = class(TTestCase)
  private
    procedure TestOnFilterProc(DataSet: TDataSet; var Accept: Boolean);
    procedure FTestDelete1(TestCancelUpdate : boolean);
    procedure FTestDelete2(TestCancelUpdate : boolean);
  protected
    procedure SetUp; override;
    procedure TearDown; override;
  published
    procedure TestCancelUpdDelete1;
    procedure TestCancelUpdDelete2;

    procedure TestAppendInsertRecord;

    procedure TestBookmarks;
    procedure TestBookmarkValid;

    procedure TestDelete1;
    procedure TestDelete2;

    procedure TestLocate;
    procedure TestLocateCaseIns;

    procedure TestFirst;
    procedure TestIntFilter;
    procedure TestOnFilter;
    procedure TestStringFilter;

    procedure TestNullAtOpen;

    procedure TestAppendOnEmptyDataset;
    procedure TestInsertOnEmptyDataset;

    procedure TestEofAfterFirst;           //bug 7211
    procedure TestLastAppendCancel;        // bug 5058
    procedure TestRecNo;                   // bug 5061
    procedure TestSetRecNo;                // bug 6919
    procedure TestBug7007;
    procedure TestBug6893;
    procedure TestRequired;
    procedure TestOldValue;
  end;


  { TDBBasicsUniDirectionalTestSetup }
{$ifdef fpc}
  TDBBasicsUniDirectionalTestSetup = class(TDBBasicsTestSetup)
  protected
    procedure OneTimeSetup; override;
    procedure OneTimeTearDown; override;
  end;
{$endif fpc}
implementation

uses
{$ifdef fpc}
  bufdataset,
  sqldb,
{$endif fpc}
  variants,
  strutils,
  FmtBCD;

type THackDataLink=class(TdataLink);

{ TTestCursorDBBasics }

procedure TTestCursorDBBasics.SetUp;
begin
  DBConnector.StartTest;
end;

procedure TTestCursorDBBasics.TearDown;
begin
  DBConnector.StopTest;
end;

procedure TTestCursorDBBasics.TestAppendOnEmptyDataset;
begin
  with DBConnector.GetNDataset(0) do
    begin
    open;
    CheckTrue(CanModify);
    CheckTrue(eof);
    CheckTrue(bof);
    append;
    FieldByName('id').AsInteger:=0;
    CheckFalse(Bof);
    CheckTrue(Eof);
    post;
    CheckFalse(eof);
    CheckFalse(bof);
    end;
end;

procedure TTestCursorDBBasics.TestInsertOnEmptyDataset;
begin
  with DBConnector.GetNDataset(0) do
    begin
    open;
    CheckTrue(CanModify);
    CheckTrue(eof);
    CheckTrue(bof);
    CheckTrue(IsEmpty);
    insert;
    FieldByName('id').AsInteger:=0;
    CheckTrue(Bof);
    CheckTrue(Eof);
    CheckFalse(IsEmpty);
    post;
    CheckFalse(IsEmpty);
    CheckFalse(eof);
    CheckFalse(bof);
    end;
end;

procedure TTestDBBasics.TestSelectQueryBasics;
var b : TFieldType;
begin
  with DBConnector.GetNDataset(1) do
    begin
    Open;

    CheckEquals(1,RecNo);
    CheckEquals(1,RecordCount);

    CheckEquals(2,FieldCount);

    CheckTrue(CompareText('ID',fields[0].FieldName)=0);
    CheckTrue(CompareText('ID',fields[0].DisplayName)=0);
    CheckTrue(ftInteger=fields[0].DataType, 'The datatype of the field ''ID'' is incorrect, it should be ftInteger');

    CheckTrue(CompareText('NAME',fields[1].FieldName)=0);
    CheckTrue(CompareText('NAME',fields[1].DisplayName)=0);
    CheckTrue(ftString=fields[1].DataType);

    CheckEquals(1,fields[0].Value);
    CheckEquals('TestName1',fields[1].Value);

    Close;
    end;
end;

procedure TTestDBBasics.TestPostOnlyInEditState;
begin
  with DBConnector.GetNDataset(1) do
    begin
    open;
    CheckException(Post,EDatabaseError,'Post was called in a non-edit state');
    end;
end;

procedure TTestDBBasics.TestMove;
var i,count      : integer;
    aDatasource  : TDataSource;
    aDatalink    : TDataLink;
    ABufferCount : Integer;

begin
  aDatasource := TDataSource.Create(nil);
  aDatalink := TTestDataLink.Create;
  try
    aDatalink.DataSource := aDatasource;
    ABufferCount := 11;
    aDatalink.BufferCount := ABufferCount;
    DataEvents := '';
    for count := 0 to 32 do
      begin
      aDatasource.DataSet := DBConnector.GetNDataset(count);
      with aDatasource.Dataset do
        begin
        i := 1;
        Open;
        CheckEquals('deUpdateState:0;',DataEvents);
        DataEvents := '';
        while not EOF do
          begin
          CheckEquals(i,fields[0].AsInteger);
          CheckEquals('TestName'+inttostr(i),fields[1].AsString);
          inc(i);

          Next;
          if (i > ABufferCount) and not EOF then
            CheckEquals('deCheckBrowseMode:0;deDataSetScroll:-1;DataSetScrolled:1;DataSetChanged;',DataEvents)
          else
            CheckEquals('deCheckBrowseMode:0;deDataSetScroll:0;DataSetScrolled:0;DataSetChanged;',DataEvents);
          DataEvents := '';
          end;
        CheckEquals(count,i-1);
        close;
        CheckEquals('deUpdateState:0;',DataEvents);
        DataEvents := '';
        end;
      end;
  finally
    aDatalink.Free;
    aDatasource.Free;
  end;
end;

procedure TTestDBBasics.TestdeFieldListChange;

var i,count     : integer;
    aDatasource : TDataSource;
    aDatalink   : TDataLink;
    ds          : TDataset;

begin
  aDatasource := TDataSource.Create(nil);
  aDatalink := TTestDataLink.Create;
  aDatalink.DataSource := aDatasource;
  ds := DBConnector.GetNDataset(1);
  with ds do
    begin
    aDatasource.DataSet := ds;
    DataEvents := '';
    open;
    Fields.add(tfield.Create(DBConnector.GetNDataset(1)));
    CheckEquals('deUpdateState:0;deFieldListChange:0;',DataEvents);
    DataEvents := '';
    fields.Clear;
    CheckEquals('deFieldListChange:0;',DataEvents)
    end;
  aDatasource.Free;
  aDatalink.Free;
end;


procedure TTestDBBasics.TestActiveBufferWhenClosed;
begin
  with DBConnector.GetNDataset(0) do
    begin
{$ifdef fpc}
    AssertNull(ActiveBuffer);
{$endif fpc}
    open;
    CheckFalse(ActiveBuffer = nil,'Activebuffer of an empty dataset shouldn''t be nil');
    end;
end;

procedure TTestDBBasics.TestEOFBOFClosedDataset;
begin
  with DBConnector.GetNDataset(1) do
    begin
    CheckTrue(EOF);
    CheckTrue(BOF);
    open;
    close;
    CheckTrue(EOF);
    CheckTrue(BOF);
    end;
end;

procedure TTestDBBasics.TestLayoutChangedEvents;
var aDatasource : TDataSource;
    aDatalink   : TDataLink;
    ds          : tdataset;

begin
  aDatasource := TDataSource.Create(nil);
  aDatalink := TTestDataLink.Create;
  try
    aDatalink.DataSource := aDatasource;
    ds := DBConnector.GetNDataset(6);
    aDatasource.DataSet:=ds;
    with ds do
      begin
      open;

      DataEvents := '';
      DisableControls;
      Active:=False;
      Active:=True;
      EnableControls;
      CheckEquals('deLayoutChange:0;DataSetChanged;',DataEvents);

      close;
      end;
  finally
    aDatasource.Free;
    aDatalink.Free;
  end;
end;

procedure TTestDBBasics.TestDataEventsResync;
var i,count     : integer;
    aDatasource : TDataSource;
    aDatalink   : TDataLink;
    ds          : tdataset;

begin
  aDatasource := TDataSource.Create(nil);
  aDatalink := TTestDataLink.Create;
  try
    aDatalink.DataSource := aDatasource;
    ds := DBConnector.GetNDataset(6);
    ds.BeforeScroll := DBConnector.DataEvent;
    with ds do
      begin
      aDatasource.DataSet := ds;
      open;
      DataEvents := '';
      Resync([rmExact]);
      CheckEquals('deDataSetChange:0;DataSetChanged;',DataEvents);
      DataEvents := '';
      next;
      CheckEquals('deCheckBrowseMode:0;DataEvent;deDataSetScroll:0;DataSetScrolled:1;DataSetChanged;',DataEvents);
      close;
      end;
  finally
    aDatasource.Free;
    aDatalink.Free;
  end;
end;

procedure TTestCursorDBBasics.TestLastAppendCancel;

var count : integer;

begin
  for count := 0 to 32 do with DBConnector.GetNDataset(count) do
    begin
    open;

    Last;
    Append;
    Cancel;

    CheckEquals(count,fields[0].asinteger);
    CheckEquals(count,RecordCount);

    Close;

    end;
end;

procedure TTestCursorDBBasics.TestRecNo;
var i       : longint;
    passed  : boolean;
begin
  with DBConnector.GetNDataset(0) do
    begin
    // Accessing RecNo on a closed dataset should raise an EDatabaseError or should
    // return 0
    passed := false;
    try
      i := recno;
    except on E: Exception do
      begin
      passed := E.classname = EDatabaseError.className
      end;
    end;
    if not passed then
      CheckEquals(0,RecNo,'Failed to get the RecNo from a closed dataset');

    // Accessing Recordcount on a closed dataset should raise an EDatabaseError or should
    // return 0
    passed := false;
    try
      i := recordcount;
    except on E: Exception do
      begin
      passed := E.classname = EDatabaseError.className
      end;
    end;
    if not passed then
      CheckEquals(0,RecNo,'Failed to get the Recordcount from a closed dataset');

    Open;

    CheckEquals(0,RecordCount);
    CheckEquals(0,RecNo);

    first;
    CheckEquals(0,RecordCount);
    CheckEquals(0,RecNo);

    last;
    CheckEquals(0,RecordCount);
    CheckEquals(0,RecNo);

    append;
    CheckEquals(0,RecNo);
    CheckEquals(0,RecordCount);

    first;
    CheckEquals(0,RecNo);
    CheckEquals(0,RecordCount);

    append;
    FieldByName('id').AsInteger := 1;
    CheckEquals(0,RecNo);
    CheckEquals(0,RecordCount);

    first;
    CheckEquals(1,RecNo);
    CheckEquals(1,RecordCount);

    last;
    CheckEquals(1,RecNo);
    CheckEquals(1,RecordCount);

    append;
    FieldByName('id').AsInteger := 1;
    CheckEquals(0,RecNo);
    CheckEquals(1,RecordCount);

    Close;
    end;
end;

procedure TTestCursorDBBasics.TestSetRecNo;
begin
  with DBConnector.GetNDataset(15) do
    begin
    Open;
    RecNo := 1;
    CheckEquals(1,fields[0].AsInteger);
    CheckEquals(1,RecNo);

    RecNo := 2;
    CheckEquals(2,fields[0].AsInteger);
    CheckEquals(2,RecNo);

    RecNo := 8;
    CheckEquals(8,fields[0].AsInteger);
    CheckEquals(8,RecNo);

    RecNo := 15;
    CheckEquals(15,fields[0].AsInteger);
    CheckEquals(15,RecNo);

    RecNo := 3;
    CheckEquals(3,fields[0].AsInteger);
    CheckEquals(3,RecNo);

    RecNo := 14;
    CheckEquals(14,fields[0].AsInteger);
    CheckEquals(14,RecNo);

    RecNo := 15;
    CheckEquals(15,fields[0].AsInteger);
    CheckEquals(15,RecNo);

    // test for exceptions...
{    RecNo := 16;
    CheckEquals(15,fields[0].AsInteger);
    CheckEquals(15,RecNo);}

    Close;
    end;
end;

procedure TTestCursorDBBasics.TestRequired;
begin
  with DBConnector.GetNDataset(2) do
    begin
    Open;
    FieldByName('ID').Required := True;
    Append;
    CheckException(Post, EDatabaseError);
    FieldByName('ID').AsInteger := 1000;
    Post;
    Close;
    end;
end;

procedure TTestDBBasics.TestExceptionLocateClosed;
var passed: boolean;
begin
  with DBConnector.GetNDataset(15) do
    begin
    passed := false;
    try
      locate('name','TestName1',[]);
    except on E: Exception do
      begin
      passed := E.classname = EDatabaseError.className
      end;
    end;
    CheckTrue(passed);
    end;
end;


procedure TTestDBBasics.SetUp;
begin
  DBConnector.StartTest;
end;

procedure TTestDBBasics.TearDown;
begin
  DBConnector.StopTest;
end;

procedure TTestCursorDBBasics.TestOldValue;
var v : variant;
    bufds: TDataset;
begin
  bufds := DBConnector.GetNDataset(0) as TDataset;
  bufds.Open;
  bufds.InsertRecord([0,'name']);
  v := VarToStr(bufds.fields[1].OldValue);
end;

procedure TTestDBBasics.TestCanModifySpecialFields;
var ds    : TDataset;
    lds   : TDataset;
    fld   : TField;
begin
  lds := DBConnector.GetNDataset(10);
  ds := DBConnector.GetNDataset(5);
  with ds do
    begin
    Fld := TIntegerField.Create(ds);
    Fld.FieldName:='ID';
    Fld.DataSet:=ds;

    Fld := TStringField.Create(ds);
    Fld.FieldName:='LookupFld';
    Fld.FieldKind:=fkLookup;
    Fld.DataSet:=ds;
    Fld.LookupDataSet:=lds;
    Fld.LookupResultField:='NAME';
    Fld.LookupKeyFields:='ID';
    Fld.KeyFields:='ID';

    lds.Open;
    Open;
    CheckTrue(FieldByName('ID').CanModify);
    CheckFalse(FieldByName('LookupFld').CanModify);
    CheckFalse(FieldByName('ID').ReadOnly);
    CheckFalse(FieldByName('LookupFld').ReadOnly);

    CheckEquals(1,FieldByName('ID').AsInteger);
    CheckEquals('name1',FieldByName('LookupFld').AsString);
    close;
    lds.Close;
    end;
end;


procedure TTestCursorDBBasics.TestAppendInsertRecord;
begin
  with DBConnector.GetNDataset(true,6) do
    begin
    open;
    // InsertRecord should insert a record, set the values, post the record and
    // make the new record active.
    InsertRecord([152,'TestInsRec']);
    CheckEquals(152,fields[0].AsInteger);
    CheckEquals('TestInsRec',fields[1].AsString);
    CheckTrue(state=dsBrowse);

    // AppendRecord should append a record, further the same as InsertRecord
    AppendRecord([151,'TestInsRec']);
    CheckEquals(151,fields[0].AsInteger);
    CheckEquals('TestInsRec',fields[1].AsString);
    CheckTrue(state=dsBrowse);
    next;
    CheckTrue(EOF);
    end;
end;

procedure TTestCursorDBBasics.TestBookmarks;
var BM1,BM2,BM3,BM4,BM5 : TBookmark;
begin
  with DBConnector.GetNDataset(true,14) do
    begin
{$ifdef fpc}
    AssertNull(GetBookmark);
{$endif fpc}
    open;
    BM1:=GetBookmark; // id=1, BOF
    next;next;
    BM2:=GetBookmark; // id=3
    next;next;next;
    BM3:=GetBookmark; // id=6
    next;next;next;next;next;next;next;next;
    BM4:=GetBookmark; // id=14
    next;
    BM5:=GetBookmark; // id=14, EOF
    
    GotoBookmark(BM2);
    CheckEquals(3,FieldByName('id').AsInteger);

    GotoBookmark(BM1);
    CheckEquals(1,FieldByName('id').AsInteger);

    GotoBookmark(BM3);
    CheckEquals(6,FieldByName('id').AsInteger);

    GotoBookmark(BM4);
    CheckEquals(14,FieldByName('id').AsInteger);

    GotoBookmark(BM3);
    CheckEquals(6,FieldByName('id').AsInteger);

    GotoBookmark(BM5);
    CheckEquals(14,FieldByName('id').AsInteger);

    GotoBookmark(BM1);
    CheckEquals(1,FieldByName('id').AsInteger);

    next;
    delete;

    GotoBookmark(BM2);
    CheckEquals(3,FieldByName('id').AsInteger);
    
    delete;delete;

    GotoBookmark(BM3);
    CheckEquals(6,FieldByName('id').AsInteger);

    GotoBookmark(BM1);
    CheckEquals(1,FieldByName('id').AsInteger);
    insert;
    fieldbyname('id').AsInteger:=20;
    insert;
    fieldbyname('id').AsInteger:=21;
    insert;
    fieldbyname('id').AsInteger:=22;
    insert;
    fieldbyname('id').AsInteger:=23;
    post;
    
    GotoBookmark(BM3);
    CheckEquals(6,FieldByName('id').AsInteger);

    GotoBookmark(BM1);
    CheckEquals(1,FieldByName('id').AsInteger);

    GotoBookmark(BM5);
    CheckEquals(14,FieldByName('id').AsInteger);
    end;
end;

procedure TTestCursorDBBasics.TestBookmarkValid;
var BM1,BM2,BM3,BM4,BM5 : TBookmark;
begin
  with DBConnector.GetNDataset(true,14) do
    begin
    BM1 := Nil;
    CheckFalse(BookmarkValid(BM1));
    open;
    BM1:=GetBookmark; // id=1, BOF
    CheckTrue(BookmarkValid(BM1));
    next;next;
    BM2:=GetBookmark; // id=3
    CheckTrue(BookmarkValid(BM2));
    next;next;next;
    BM3:=GetBookmark; // id=6
    CheckTrue(BookmarkValid(BM3));
    next;next;next;next;next;next;next;next;
    BM4:=GetBookmark; // id=14
    CheckTrue(BookmarkValid(BM4));
    next;
    BM5:=GetBookmark; // id=14, EOF
    CheckTrue(BookmarkValid(BM5));

    CheckTrue(BookmarkValid(BM4));
    CheckTrue(BookmarkValid(BM3));
    CheckTrue(BookmarkValid(BM2));
    CheckTrue(BookmarkValid(BM1));
    GotoBookmark(BM2);
    CheckTrue(BookmarkValid(BM5));
    CheckTrue(BookmarkValid(BM4));
    CheckTrue(BookmarkValid(BM3));
    CheckTrue(BookmarkValid(BM2));
    CheckTrue(BookmarkValid(BM1));
    end;
end;

procedure TTestCursorDBBasics.TestLocate;
begin
  with DBConnector.GetNDataset(true,13) do
    begin
    open;
    CheckTrue(Locate('id',vararrayof([5]),[]));
    CheckEquals(5,FieldByName('id').AsInteger);
    CheckFalse(Locate('id',vararrayof([15]),[]));
    CheckTrue(Locate('id',vararrayof([12]),[]));
    CheckEquals(12,FieldByName('id').AsInteger);
    close;
    open;
    CheckTrue(Locate('id',vararrayof([12]),[]));
    CheckEquals(12,FieldByName('id').AsInteger);
    CheckTrue(Locate('id;name',vararrayof([4,'TestName4']),[]));
    CheckEquals(4,FieldByName('id').AsInteger);

    CheckFalse(Locate('id;name',vararrayof([4,'TestName5']),[]));

    end;
end;

procedure TTestCursorDBBasics.TestLocateCaseIns;
begin
  with DBConnector.GetNDataset(true,13) do
    begin
    open;
    CheckFalse(Locate('name',vararrayof(['TEstName5']),[]));
    CheckTrue(Locate('name',vararrayof(['TEstName5']),[loCaseInsensitive]));
    CheckEquals(5,FieldByName('id').AsInteger);

    CheckFalse(Locate('name',vararrayof(['TestN']),[]));
    CheckTrue(Locate('name',vararrayof(['TestN']),[loPartialKey]));

    CheckFalse(Locate('name',vararrayof(['TestNA']),[loPartialKey]));
    CheckTrue(Locate('name',vararrayof(['TestNA']),[loPartialKey, loCaseInsensitive]));
    close;
    end;
end;

procedure TTestDBBasics.TestSetFieldValues;
var PassException : boolean;
begin
  with DBConnector.GetNDataset(true,11) do
    begin
    open;
    first;
    edit;
    FieldValues['id']:=5;
    post;
    CheckEquals('TestName1',FieldByName('name').AsString);
    CheckEquals(5,FieldByName('id').AsInteger);
    edit;
    FieldValues['name']:='FieldValuesTestName';
    post;
    CheckEquals('FieldValuesTestName',FieldByName('name').AsString);
    CheckEquals(5,FieldByName('id').AsInteger);
    edit;
    FieldValues['id;name']:= VarArrayOf([243,'ValuesTestName']);
    post;
    CheckEquals('ValuesTestName',FieldByName('name').AsString);
    CheckEquals(243,FieldByName('id').AsInteger);
    
    PassException:=false;
    try
      edit;
      FieldValues['id;name;fake']:= VarArrayOf([243,'ValuesTestName',4]);
    except
      on E: EDatabaseError do PassException := True;
    end;
    post;
    CheckTrue(PassException);
    end;
end;

procedure TTestDBBasics.TestGetFieldValues;
var AVar          : Variant;
    PassException : boolean;
begin
  with DBConnector.GetNDataset(true,14) do
    begin
    open;
    AVar:=FieldValues['id'];
    CheckEquals(AVar,1);

    AVar:=FieldValues['name'];
    CheckEquals(AVar,'TestName1');

    AVar:=FieldValues['id;name'];
    CheckEquals(AVar[0],1);
    CheckEquals(AVar[1],'TestName1');

    AVar:=FieldValues['name;id;'];
    CheckEquals(AVar[1],1);
    CheckEquals(AVar[0],'TestName1');
    
    PassException:=false;
    try
      AVar:=FieldValues['name;id;fake'];
    except
      on E: EDatabaseError do PassException := True;
    end;
    CheckTrue(PassException);

    end;
end;

procedure TTestCursorDBBasics.TestFirst;
var i : integer;
begin
  with DBConnector.GetNDataset(true,14) do
    begin
    open;
    CheckEquals(1,FieldByName('ID').AsInteger);
    First;
    CheckEquals(1,FieldByName('ID').AsInteger);
    next;
    CheckEquals(2,FieldByName('ID').AsInteger);
    First;
    CheckEquals(1,FieldByName('ID').AsInteger);
    for i := 0 to 12 do
      next;
    CheckEquals(14,FieldByName('ID').AsInteger);
    First;
    CheckEquals(1,FieldByName('ID').AsInteger);
    close;
    end;
end;

procedure TTestCursorDBBasics.TestDelete1;
begin
  FTestDelete1(false);
end;

procedure TTestCursorDBBasics.TestDelete2;
begin
  FTestDelete2(false);
end;

procedure TTestCursorDBBasics.TestCancelUpdDelete1;
begin
  FTestDelete1(true);
end;

procedure TTestCursorDBBasics.TestCancelUpdDelete2;
begin
  FTestDelete2(true);
end;

procedure TTestCursorDBBasics.FTestDelete1(TestCancelUpdate : boolean);
// Test the deletion of records, including the first and the last one
var i  : integer;
    ds : TDataset;
begin
  ds := DBConnector.GetNDataset(true,17);
  with ds do
    begin
    Open;

    for i := 0 to 16 do if i mod 4=0 then
      delete
    else
       next;

    First;
    for i := 0 to 16 do
      begin
      if i mod 4<>0 then
        begin
        CheckEquals(i+1,FieldByName('ID').AsInteger);
        CheckEquals('TestName'+inttostr(i+1),FieldByName('NAME').AsString);
        next;
        end;
      end;
    end;

{$ifdef fpc}
  if TestCancelUpdate then
    begin
    if not (ds is TCustomBufDataset) then
      Ignore('This test only applies to TCustomBufDataset and descendents.');
    with TCustomBufDataset(ds) do
      begin
      CancelUpdates;

      First;
      for i := 0 to 16 do
        begin
        CheckEquals(i+1,FieldByName('ID').AsInteger);
        CheckEquals('TestName'+inttostr(i+1),FieldByName('NAME').AsString);
        next;
        end;

      close;
      end;
    end;
{$endif}
end;

procedure TTestCursorDBBasics.FTestDelete2(TestCancelUpdate : boolean);
// Test the deletion of edited and appended records
var i : integer;
    ds : TDataset;
begin
  ds := DBConnector.GetNDataset(true,17);
  with ds do
    begin
    Open;

    for i := 0 to 16 do
      begin
      if i mod 4=0 then
        begin
        edit;
        fieldbyname('name').AsString:='this record will be gone soon';
        post;
        end;
      next;
      end;

    for i := 17 to 20 do
      begin
      append;
      fieldbyname('id').AsInteger:=i+1;
      fieldbyname('name').AsString:='TestName'+inttostr(i+1);
      post;
      end;

    first;
    for i := 0 to 20 do if i mod 4=0 then
      delete
    else
       next;

    First;
    i := 0;
    for i := 0 to 20 do
      begin
      if i mod 4<>0 then
        begin
        CheckEquals(i+1,FieldByName('ID').AsInteger);
        CheckEquals('TestName'+inttostr(i+1),FieldByName('NAME').AsString);
        next;
        end;
      end;
    end;

{$ifdef fpc}
  if TestCancelUpdate then
    begin
    if not (ds is TCustomBufDataset) then
      Ignore('This test only applies to TCustomBufDataset and descendents.');
    with TCustomBufDataset(ds) do
      begin
      CancelUpdates;

      First;
      for i := 0 to 16 do
        begin
        CheckEquals(i+1,FieldByName('ID').AsInteger);
        CheckEquals('TestName'+inttostr(i+1),FieldByName('NAME').AsString);
        next;
        end;

      close;
      end;
    end;
{$endif fpc}
end;

procedure TTestCursorDBBasics.TestOnFilterProc(DataSet: TDataSet; var Accept: Boolean);

var a : TDataSetState;
begin
  Accept := odd(Dataset.FieldByName('ID').AsInteger);
end;

procedure TTestCursorDBBasics.TestOnFilter;
var tel : byte;
begin
  with DBConnector.GetNDataset(15) do
    begin
    OnFilterRecord := TestOnFilterProc;
    Filtered := True;
    Open;
    for tel := 1 to 8 do
      begin
      CheckTrue(odd(FieldByName('ID').asinteger));
      next;
      end;
    CheckTrue(EOF);
    end;
end;

procedure TTestCursorDBBasics.TestIntFilter;
var tel : byte;
begin
  with DBConnector.GetNDataset(15) do
    begin
    Filtered := True;
    Filter := '(id>4) and (id<9)';
    Open;
    for tel := 5 to 8 do
      begin
      CheckEquals(tel,FieldByName('ID').asinteger);
      next;
      end;
    CheckTrue(EOF);
    Close;
    end;
end;

procedure TTestDBBasics.TestRecordcountAfterReopen;
var
  datalink1: tdatalink;
  datasource1: tdatasource;
  query1: TDataSet;

begin
  query1:= DBConnector.GetNDataset(11);
  datalink1:= TDataLink.create;
  datasource1:= tdatasource.create(nil);
  try
    datalink1.datasource:= datasource1;
    datasource1.dataset:= query1;

    query1.active := true;
    query1.active := False;
    CheckEquals(0, THackDataLink(datalink1).RecordCount);
    query1.active := true;
    CheckTrue(THackDataLink(datalink1).RecordCount>0);
    query1.active := false;
  finally
    datalink1.free;
    datasource1.free;
  end;
end;

procedure TTestCursorDBBasics.TestStringFilter;
var tel : byte;
begin
  with DBConnector.GetNDataset(15) do
    begin
    Open;
    Filter := '(name=''TestName3'')';
    Filtered := True;
    CheckFalse(EOF);
    CheckEquals(3,FieldByName('ID').asinteger);
    CheckEquals('TestName3',FieldByName('NAME').asstring);
    next;
    CheckTrue(EOF);

    // Check partial compare
    Filter := '(name=''*Name5'')';
    CheckFalse(EOF);
    CheckEquals(5,FieldByName('ID').asinteger);
    CheckEquals('TestName5',FieldByName('NAME').asstring);
    next;
    CheckTrue(EOF);

    // Check case-sensitivity
    Filter := '(name=''*name3'')';
    first;
    CheckTrue(EOF);

    FilterOptions:=[foCaseInsensitive];
    Filter := '(name=''testname3'')';
    first;
    CheckFalse(EOF);
    CheckEquals(3,FieldByName('ID').asinteger);
    CheckEquals('TestName3',FieldByName('NAME').asstring);
    next;
    CheckTrue(EOF);

    // Check case-insensitive partial compare
    Filter := '(name=''*name3'')';
    first;
    CheckFalse(EOF);
    CheckEquals(3,FieldByName('ID').asinteger);
    CheckEquals('TestName3',FieldByName('NAME').asstring);
    next;
    CheckTrue(EOF);

    Filter := '(name=''*name*'')';
    first;
    CheckFalse(EOF);
    CheckEquals(1,FieldByName('ID').asinteger);
    CheckEquals('TestName1',FieldByName('NAME').asstring);
    next;
    CheckFalse(EOF);
    CheckEquals(2,FieldByName('ID').asinteger);
    CheckEquals('TestName2',FieldByName('NAME').asstring);

    Filter := '(name=''*neme*'')';
    first;
    CheckTrue(EOF);


    Close;
    end;
end;

{$ifdef fpc}
procedure TTestBufDatasetDBBasics.TestIsEmpty;
begin
  with tCustombufdataset(DBConnector.GetNDataset(True,1)) do
    begin
    open;
    delete;
    Resync([]);
    applyupdates;
    CheckTrue(IsEmpty);

    end;
end;

procedure TTestBufDatasetDBBasics.TestClosedIndexFieldNames;
var s : string;
    bufds: TCustomBufDataset;
begin
  bufds := DBConnector.GetNDataset(5) as TCustomBufDataset;
  s := bufds.IndexFieldNames;
  s := bufds.IndexName;
  bufds.CompareBookmarks(nil,nil);
end;

procedure TTestBufDatasetDBBasics.TestSafeAsXML;
var ds    : TDataset;
    LoadDs: TCustomBufDataset;
begin
  ds := DBConnector.GetNDataset(true,5);

  ds.open;
  TCustomBufDataset(ds).SaveToFile('test.xml');
  ds.close;

  LoadDs := TCustomBufDataset.Create(nil);
  LoadDs.LoadFromFile('test.xml');
  FTestXMLDatasetDefinition(LoadDS);
end;

procedure TTestBufDatasetDBBasics.TestFileNameProperty;
var ds1,ds2: TDataset;
    LoadDs: TCustomBufDataset;
begin
  ds2 := nil;
  ds1 := DBConnector.GetNDataset(true,5);
  try
    ds1.open;
    TCustomBufDataset(ds1).FileName:='test.xml';
    ds1.close;

    ds2 := DBConnector.GetNDataset(True,7);
    TCustomBufDataset(ds2).FileName:='test.xml';
    ds2.Open;
    FTestXMLDatasetDefinition(Ds2);
  finally
    TCustomBufDataset(ds1).FileName:='';
    if assigned(ds2) then
      TCustomBufDataset(ds2).FileName:='';
  end;
end;

procedure TTestBufDatasetDBBasics.TestClientDatasetAsMemDataset;
var ds : TCustomBufDataset;
    i  : integer;
begin
  ds := TCustomBufDataset.Create(nil);
  DS.FieldDefs.Add('ID',ftInteger);
  DS.FieldDefs.Add('NAME',ftString,50);
  DS.CreateDataset;
  DS.Open;
  for i := 1 to 10 do
    begin
    ds.Append;
    ds.FieldByName('ID').AsInteger := i;
    ds.FieldByName('NAME').AsString := 'TestName' + inttostr(i);
    DS.Post;
    end;
  ds.first;
  for i := 1 to 10 do
    begin
    CheckEquals(i,ds.fieldbyname('ID').asinteger);
    CheckEquals('TestName' + inttostr(i),ds.fieldbyname('NAME').AsString);
    ds.next;
    end;
  CheckTrue(ds.EOF);
  DS.Close;
end;

procedure TTestBufDatasetDBBasics.TestBufDatasetCancelUpd;
var i : byte;
begin
  with DBConnector.GetNDataset(5) as TCustomBufDataset do
    begin
    open;
    next;
    next;

    edit;
    FieldByName('name').AsString := 'changed';
    post;
    next;
    delete;

    CancelUpdates;

    First;

    for i := 1 to 5 do
      begin
      CheckEquals(i,fields[0].AsInteger);
      CheckEquals('TestName'+inttostr(i),fields[1].AsString);
      Next;
      end;
    end;
end;

procedure TTestBufDatasetDBBasics.TestBufDatasetCancelUpd1;
var i : byte;
begin
  with DBConnector.GetNDataset(5) as TCustomBufDataset do
    begin
    open;
    next;
    next;

    delete;
    insert;
    FieldByName('id').AsInteger := 100;
    post;

    CancelUpdates;

    last;

    for i := 5 downto 1 do
      begin
      CheckEquals(i,fields[0].AsInteger);
      CheckEquals('TestName'+inttostr(i),fields[1].AsString);
      Prior;
      end;
    end;
end;

procedure TTestBufDatasetDBBasics.TestMultipleDeleteUpdateBuffer;
var ds    : TDataset;
begin
  ds := DBConnector.GetNDataset(true,5);

  ds.open;
  with TCustomBufDataset(ds) do
    begin
    CheckEquals(0,ChangeCount);
    edit;
    fieldbyname('id').asinteger := 500;
    fieldbyname('name').AsString := 'JoJo';
    post;
    CheckEquals(1,ChangeCount);
    next; next;
    Delete;
    CheckEquals(2,ChangeCount);
    Delete;
    CheckEquals(3,ChangeCount);
    CancelUpdates;
    end;
  ds.close;
end;

procedure TTestBufDatasetDBBasics.TestDoubleDelete;
var ds    : TCustomBufDataset;
begin
  ds := TCustomBufDataset(DBConnector.GetNDataset(true,5));

  with ds do
    begin
    open;
    next; next;
    Delete;
    Delete;

    first;
    CheckEquals(1,fieldbyname('id').AsInteger);
    next;
    CheckEquals(2,fieldbyname('id').AsInteger);
    next;
    CheckEquals(5,fieldbyname('id').AsInteger);

    CancelUpdates;

    first;
    CheckEquals(1,fieldbyname('id').AsInteger);
    next;
    CheckEquals(2,fieldbyname('id').AsInteger);
    next;
    CheckEquals(3,fieldbyname('id').AsInteger);
    next;
    CheckEquals(4,fieldbyname('id').AsInteger);
    next;
    CheckEquals(5,fieldbyname('id').AsInteger);
    end;
end;

procedure TTestBufDatasetDBBasics.TestReadOnly;
var
  ds: TCustomBufDataset;
begin
  ds := DBConnector.GetFieldDataset as TCustomBufDataset;
  with ds do
    begin
    ReadOnly:=true;
    CheckFalse(CanModify);
    end;
end;

procedure TTestBufDatasetDBBasics.TestMergeChangeLog;
var
  ds: TCustomBufDataset;
  i: integer;
  s: string;
begin
  ds := DBConnector.GetNDataset(5) as TCustomBufDataset;
  with ds do
    begin
    open;
    Edit;
    i := fields[0].AsInteger;
    s := fields[1].AsString;
    fields[0].AsInteger:=64;
    fields[1].AsString:='Changed';
    Post;
    checkequals(fields[0].OldValue,i);
    checkequals(fields[1].OldValue,s);
    CheckEquals(ChangeCount,1);
    MergeChangeLog;
    CheckEquals(ChangeCount,0);
    checkequals(fields[0].OldValue,64);
    checkequals(fields[1].OldValue,'Changed');
    end;
end;

procedure TTestBufDatasetDBBasics.FTestXMLDatasetDefinition(ADataset: TDataset);
var i : integer;
begin
  CheckEquals(2,ADataset.FieldDefs.Count);
  CheckEquals(2,ADataset.Fields.Count);
  CheckTrue(SameText('ID',ADataset.Fields[0].FieldName));
  CheckTrue(SameText('NAME',ADataset.Fields[1].FieldName));
  CheckTrue(ADataset.fields[1].DataType=ftString,'Incorrect fieldtype');
  i := 1;
  while not ADataset.EOF do
    begin
    CheckEquals('TestName'+inttostr(i),ADataset.FieldByName('name').AsString);
    ADataset.Next;
    inc(i);
    end;
end;

procedure TTestBufDatasetDBBasics.TestAddIndexFieldType(AFieldType: TFieldType; ActiveDS : boolean);
var ds : TCustomBufDataset;
    FList : TStringList;
    LastValue : Variant;
    StrValue : String;
begin
  ds := DBConnector.GetFieldDataset as TCustomBufDataset;
  with ds do
    begin
    
    if not ActiveDS then
      begin
      AddIndex('testindex','F'+FieldTypeNames[AfieldType],[]);
      IndexName:='testindex';
      end
    else
      MaxIndexesCount := 3;

    try
      open;
    except
      if not assigned(ds.FindField('F'+FieldTypeNames[AfieldType])) then
        Ignore('Fields of the type ' + FieldTypeNames[AfieldType] + ' are not supported by this type of dataset')
      else
        raise;
    end;

    if ActiveDS then
      begin
      if not assigned(ds.FindField('F'+FieldTypeNames[AfieldType])) then
        Ignore('Fields of the type ' + FieldTypeNames[AfieldType] + ' are not supported by this type of dataset');
      AddIndex('testindex','F'+FieldTypeNames[AfieldType],[]);
      IndexName:='testindex';
      First;
      end;

    LastValue:=null;
    while not eof do
      begin
      if AFieldType=ftString then
        CheckTrue(AnsiCompareStr(VarToStr(LastValue),VarToStr(FieldByName('F'+FieldTypeNames[AfieldType]).AsString))<=0)
      else
        CheckTrue(LastValue<=FieldByName('F'+FieldTypeNames[AfieldType]).AsVariant);
      LastValue:=FieldByName('F'+FieldTypeNames[AfieldType]).AsVariant;
      Next;
      end;

    while not bof do
      begin
      if AFieldType=ftString then
        CheckTrue(AnsiCompareStr(VarToStr(LastValue),VarToStr(FieldByName('F'+FieldTypeNames[AfieldType]).AsString))>=0)
      else
        CheckTrue(LastValue>=FieldByName('F'+FieldTypeNames[AfieldType]).AsVariant);
      LastValue:=FieldByName('F'+FieldTypeNames[AfieldType]).AsVariant;
      Prior;
      end;
    end;
end;

procedure TTestBufDatasetDBBasics.TestAddIndexSmallInt;
begin
  TestAddIndexFieldType(ftSmallint,False);
end;

procedure TTestBufDatasetDBBasics.TestAddIndexBoolean;
begin
  TestAddIndexFieldType(ftBoolean,False);
end;

procedure TTestBufDatasetDBBasics.TestAddIndexFloat;
begin
  TestAddIndexFieldType(ftFloat,False);
end;

procedure TTestBufDatasetDBBasics.TestAddIndexInteger;
begin
  TestAddIndexFieldType(ftInteger,False);
end;

procedure TTestBufDatasetDBBasics.TestAddIndexLargeInt;
begin
  TestAddIndexFieldType(ftLargeint,False);
end;

procedure TTestBufDatasetDBBasics.TestAddIndexDateTime;
begin
  TestAddIndexFieldType(ftDateTime,False);
end;

procedure TTestBufDatasetDBBasics.TestAddIndexCurrency;
begin
  TestAddIndexFieldType(ftCurrency,False);
end;

procedure TTestBufDatasetDBBasics.TestAddIndexBCD;
begin
  TestAddIndexFieldType(ftBCD,False);
end;

procedure TTestBufDatasetDBBasics.TestAddIndex;
var ds : TCustomBufDataset;
    AFieldType : TFieldType;
    FList : TStringList;
    i : integer;
begin
  ds := DBConnector.GetFieldDataset as TCustomBufDataset;
  with ds do
    begin

    AFieldType:=ftString;
    AddIndex('testindex','F'+FieldTypeNames[AfieldType],[]);
    FList := TStringList.Create;
    FList.Sorted:=true;
    FList.CaseSensitive:=True;
    FList.Duplicates:=dupAccept;
    open;

    while not eof do
      begin
      flist.Add(FieldByName('F'+FieldTypeNames[AfieldType]).AsString);
      Next;
      end;

    IndexName:='testindex';
    first;
    i:=0;

    while not eof do
      begin
      CheckEquals(flist[i],FieldByName('F'+FieldTypeNames[AfieldType]).AsString);
      inc(i);
      Next;
      end;

    while not bof do
      begin
      dec(i);
      CheckEquals(flist[i],FieldByName('F'+FieldTypeNames[AfieldType]).AsString);
      Prior;
      end;
    end;
end;

procedure TTestBufDatasetDBBasics.TestAddDescIndex;
var ds : TCustomBufDataset;
    AFieldType : TFieldType;
    FList : TStringList;
    i : integer;
begin
  ds := DBConnector.GetFieldDataset as TCustomBufDataset;
  with ds do
    begin

    AFieldType:=ftString;
    AddIndex('testindex','F'+FieldTypeNames[AfieldType],[],'F'+FieldTypeNames[AfieldType]);
    FList := TStringList.Create;
    FList.Sorted:=true;
    FList.CaseSensitive:=True;
    FList.Duplicates:=dupAccept;
    open;

    while not eof do
      begin
      flist.Add(FieldByName('F'+FieldTypeNames[AfieldType]).AsString);
      Next;
      end;

    IndexName:='testindex';
    first;
    i:=FList.Count-1;

    while not eof do
      begin
      CheckEquals(flist[i],FieldByName('F'+FieldTypeNames[AfieldType]).AsString);
      dec(i);
      Next;
      end;

    while not bof do
      begin
      inc(i);
      CheckEquals(flist[i],FieldByName('F'+FieldTypeNames[AfieldType]).AsString);
      Prior;
      end;
    end;
end;

procedure TTestBufDatasetDBBasics.TestAddCaseInsIndex;
var ds : TCustomBufDataset;
    AFieldType : TFieldType;
    FList : TStringList;
    i : integer;
begin
  ds := DBConnector.GetFieldDataset as TCustomBufDataset;
  with ds do
    begin

    AFieldType:=ftString;
    AddIndex('testindex','F'+FieldTypeNames[AfieldType],[],'','F'+FieldTypeNames[AfieldType]);
    FList := TStringList.Create;
    FList.Sorted:=true;
    FList.Duplicates:=dupAccept;
    open;

    while not eof do
      begin
      flist.Add(FieldByName('F'+FieldTypeNames[AfieldType]).AsString);
      Next;
      end;

    IndexName:='testindex';
    first;
    i:=0;

    while not eof do
      begin
      CheckEquals(flist[i],FieldByName('F'+FieldTypeNames[AfieldType]).AsString);
      inc(i);
      Next;
      end;

    while not bof do
      begin
      dec(i);
      CheckEquals(flist[i],FieldByName('F'+FieldTypeNames[AfieldType]).AsString);
      Prior;
      end;
    end;
end;

procedure TTestBufDatasetDBBasics.TestInactSwitchIndex;
// Test if the default-index is properly build when the active index is not
// the default-index while opening then dataset
var ds : TCustomBufDataset;
    AFieldType : TFieldType;
    i : integer;
begin
  ds := DBConnector.GetFieldDataset as TCustomBufDataset;
  with ds do
    begin

    AFieldType:=ftString;
    AddIndex('testindex','F'+FieldTypeNames[AfieldType],[]);
    IndexName:='testindex';
    open;
    IndexName:=''; // This should set the default index (default_order)
    first;
    
    i := 0;

    while not eof do
      begin
      CheckEquals(testStringValues[i],FieldByName('F'+FieldTypeNames[AfieldType]).AsString);
      inc(i);
      Next;
      end;
    end;
end;

procedure TTestBufDatasetDBBasics.TestAddIndexActiveDS;
var ds   : TCustomBufDataset;
    I    : integer;
begin
  TestAddIndexFieldType(ftString,true);
end;

procedure TTestBufDatasetDBBasics.TestAddIndexEditDS;
var ds        : TCustomBufDataset;
    I         : integer;
    LastValue : String;
begin
  ds := DBConnector.GetNDataset(True,5) as TCustomBufDataset;
  with ds do
    begin
    MaxIndexesCount:=3;
    open;
    edit;
    FieldByName('name').asstring := 'Zz';
    post;
    next;
    next;
    edit;
    FieldByName('name').asstring := 'aA';
    post;

    AddIndex('test','name',[]);

    first;
    ds.IndexName:='test';
    first;
    LastValue:='';
    while not eof do
      begin
      CheckTrue(AnsiCompareStr(LastValue,FieldByName('name').AsString)<=0);
      LastValue:=FieldByName('name').AsString;
      Next;
      end;
    end;
end;

procedure TTestBufDatasetDBBasics.TestIndexFieldNamesAct;
var ds : TCustomBufDataset;
    AFieldType : TFieldType;
    FList : TStringList;
    i : integer;
begin
  ds := DBConnector.GetFieldDataset as TCustomBufDataset;
  with ds do
    begin
    AFieldType:=ftString;
    FList := TStringList.Create;
    FList.Sorted:=true;
    FList.CaseSensitive:=True;
    FList.Duplicates:=dupAccept;
    open;

    while not eof do
      begin
      flist.Add(FieldByName('F'+FieldTypeNames[AfieldType]).AsString);
      Next;
      end;

    IndexFieldNames:='F'+FieldTypeNames[AfieldType];
    first;
    i:=0;

    while not eof do
      begin
      CheckEquals(flist[i],FieldByName('F'+FieldTypeNames[AfieldType]).AsString);
      inc(i);
      Next;
      end;

    while not bof do
      begin
      dec(i);
      CheckEquals(flist[i],FieldByName('F'+FieldTypeNames[AfieldType]).AsString);
      Prior;
      end;

    CheckEquals('F'+FieldTypeNames[AfieldType],IndexFieldNames);

    IndexFieldNames:='ID';
    first;
    i:=0;

    while not eof do
      begin
      CheckEquals(testStringValues[i],FieldByName('F'+FieldTypeNames[AfieldType]).AsString);
      inc(i);
      Next;
      end;

    CheckEquals('ID',IndexFieldNames);

    IndexFieldNames:='';
    first;
    i:=0;

    while not eof do
      begin
      CheckEquals(testStringValues[i],FieldByName('F'+FieldTypeNames[AfieldType]).AsString);
      inc(i);
      Next;
      end;

    CheckEquals('',IndexFieldNames);

    end;
end;

procedure TTestBufDatasetDBBasics.TestIndexCurRecord;
// Test if the currentrecord stays the same after an index change
var ds : TCustomBufDataset;
    AFieldType : TFieldType;
    i : integer;
    OldID : Integer;
    OldStringValue : string;
begin
  ds := DBConnector.GetFieldDataset as TCustomBufDataset;
  with ds do
    begin
    AFieldType:=ftString;
    AddIndex('testindex','F'+FieldTypeNames[AfieldType],[]);
    open;

    for i := 0 to (testValuesCount div 3) do
      Next;

    OldID:=FieldByName('id').AsInteger;
    OldStringValue:=FieldByName('F'+FieldTypeNames[AfieldType]).AsString;

    IndexName:='testindex';

    CheckEquals(OldID,FieldByName('id').AsInteger);
    CheckEquals(OldStringValue,FieldByName('F'+FieldTypeNames[AfieldType]).AsString);

    next;
    CheckTrue(OldStringValue<=FieldByName('F'+FieldTypeNames[AfieldType]).AsString);
    prior;
    prior;
    CheckTrue(OldStringValue>=FieldByName('F'+FieldTypeNames[AfieldType]).AsString);

    OldID:=FieldByName('id').AsInteger;
    OldStringValue:=FieldByName('F'+FieldTypeNames[AfieldType]).AsString;

    IndexName:='';

    CheckEquals(OldID,FieldByName('id').AsInteger);
    CheckEquals(OldStringValue,FieldByName('F'+FieldTypeNames[AfieldType]).AsString);
    
    next;
    CheckEquals(OldID+1,FieldByName('ID').AsInteger);
    prior;
    prior;
    CheckEquals(OldID-1,FieldByName('ID').AsInteger);
    end;
end;

procedure TTestBufDatasetDBBasics.TestAddDblIndex;
var ds : TCustomBufDataset;
    LastInteger : Integer;
    LastString : string;
begin
  ds := DBConnector.GetFieldDataset as TCustomBufDataset;
  with ds do
    begin

    AddIndex('testindex','F'+FieldTypeNames[ftString]+';F'+FieldTypeNames[ftInteger],[]);
    open;

    IndexName:='testindex';
    first;

    LastString:='';
    while not eof do
      begin
      CheckTrue(AnsiCompareStr(FieldByName('F'+FieldTypeNames[ftString]).AsString,LastString)>=0);
      LastString:= FieldByName('F'+FieldTypeNames[ftString]).AsString;

      LastInteger:=-MaxInt;
      while (FieldByName('F'+FieldTypeNames[ftString]).AsString=LastString) and not eof do
        begin
        CheckTrue(FieldByName('F'+FieldTypeNames[ftInteger]).AsInteger>=LastInteger);
        LastInteger:=FieldByName('F'+FieldTypeNames[ftInteger]).AsInteger;
        next;
        end;
      end;
    while not bof do
      begin
      CheckTrue(AnsiCompareStr(FieldByName('F'+FieldTypeNames[ftString]).AsString,LastString)<=0);
      LastString:= FieldByName('F'+FieldTypeNames[ftString]).AsString;

      LastInteger:=+MaxInt;
      while (FieldByName('F'+FieldTypeNames[ftString]).AsString=LastString) and not bof do
        begin
        CheckTrue(FieldByName('F'+FieldTypeNames[ftInteger]).AsInteger<=LastInteger);
        LastInteger:=FieldByName('F'+FieldTypeNames[ftInteger]).AsInteger;
        prior;
        end;
      end;
    end;
end;

procedure TTestBufDatasetDBBasics.TestIndexEditRecord;
var ds : TCustomBufDataset;
    AFieldType : TFieldType;
    i : integer;
    OldID : Integer;
    OldStringValue : string;
begin
  ds := DBConnector.GetFieldDataset as TCustomBufDataset;
  with ds do
    begin
    AFieldType:=ftString;
    AddIndex('testindex','F'+FieldTypeNames[AfieldType],[]);
    IndexName:='testindex';
    open;
    OldStringValue:=FieldByName('F'+FieldTypeNames[AfieldType]).AsString;
    next;
    CheckTrue(OldStringValue<=FieldByName('F'+FieldTypeNames[AfieldType]).AsString);
    OldStringValue:=FieldByName('F'+FieldTypeNames[AfieldType]).AsString;
    next;
    CheckTrue(AnsiCompareStr(OldStringValue,FieldByName('F'+FieldTypeNames[AfieldType]).AsString)<=0);
    prior;
    
    edit;
    FieldByName('F'+FieldTypeNames[AfieldType]).AsString := 'ZZZ';
    post;
    prior;
    CheckTrue(AnsiCompareStr('ZZZ',FieldByName('F'+FieldTypeNames[AfieldType]).AsString)>=0, 'Prior>');
    next;
    next;
    CheckTrue(AnsiCompareStr('ZZZ',FieldByName('F'+FieldTypeNames[AfieldType]).AsString)<=0, 'Next<');
    close;
    end;
end;

procedure TTestBufDatasetDBBasics.TestIndexAppendRecord;
var i: integer;
    LastValue: string;
begin
  with DBConnector.GetNDataset(true,0) as TCustomBufDataset do
  begin
    MaxIndexesCount:=4;
    // add index to closed dataset with no data
    AddIndex('testindex','NAME',[]);
    IndexName:='testindex';
    Open;
    // empty dataset and other than default index (default_order) active
    CheckTrue(BOF, 'No BOF when opening empty dataset');
    CheckTrue(EOF, 'No EOF when opening empty dataset');

    // append data at end
    for i:=20 downto 0 do
      AppendRecord([i, inttostr(i)]);
    First;
    // insert data at begining
    for i:=21 to 22 do
      InsertRecord([i, inttostr(i)]);

    // ATM new records are not ordered as they are added ?
    LastValue := '';
    First;
    for i:=22 downto 0 do
    begin
      CheckEquals(23-i, RecNo, 'testindex.RecNo:');
      CheckEquals(inttostr(i), Fields[1].AsString, 'testindex.Fields[1].Value:');
      //CheckTrue(AnsiCompareStr(LastValue,Fields[1].AsString) < 0, 'testindex.LastValue>CurrValue');
      LastValue := Fields[1].AsString;
      Next;
    end;
    CheckTrue(EOF, 'testindex.No EOF after last record');

    // switch back to default index (unordered)
    IndexName:='';
    First;
    for i:=22 downto 0 do
    begin
      CheckEquals(23-i, RecNo, 'index[0].RecNo:');
      CheckEquals(i, Fields[0].AsInteger, 'index[0].Fields[0].Value:');
      Next;
    end;
    CheckTrue(EOF, 'index[0].No EOF after last record');

    // add index to opened dataset with data
    AddIndex('testindex2','ID',[]);
    IndexName:='testindex2';
    First;
    for i:=0 to 22 do
    begin
      CheckEquals(1+i, RecNo, 'index2.RecNo:');
      CheckEquals(i, Fields[0].AsInteger, 'index2.Fields[0].Value:');
      Next;
    end;
    CheckTrue(EOF, 'index2.No EOF after last record');

    Close;
  end;
end;

procedure TTestBufDatasetDBBasics.TestIndexFieldNames;
var ds : TCustomBufDataset;
    AFieldType : TFieldType;
    PrevValue : String;
begin
  ds := DBConnector.GetFieldDataset as TCustomBufDataset;
  with ds do
    begin
    AFieldType:=ftString;
    
    IndexFieldNames:='F'+FieldTypeNames[AfieldType];

    open;
    PrevValue:='';
    while not eof do
      begin
      CheckTrue(AnsiCompareStr(FieldByName('F'+FieldTypeNames[AfieldType]).AsString,PrevValue)>=0);
      PrevValue:=FieldByName('F'+FieldTypeNames[AfieldType]).AsString;
      Next;
      end;

    CheckEquals('F'+FieldTypeNames[AfieldType],IndexFieldNames);

    end;
end;
{$endif fpc}

procedure TTestDBBasics.TestcalculatedField_OnCalcfields(DataSet: TDataSet);
begin
  case dataset.fieldbyname('ID').asinteger of
    1 : dataset.fieldbyname('CALCFLD').AsInteger := 5;
    2 : dataset.fieldbyname('CALCFLD').AsInteger := 70000;
    3 : dataset.fieldbyname('CALCFLD').Clear;
    4 : dataset.fieldbyname('CALCFLD').AsInteger := 1234;
    10 : dataset.fieldbyname('CALCFLD').Clear;
  else
    dataset.fieldbyname('CALCFLD').AsInteger := 1;
  end;
end;

procedure TTestDBBasics.TestCalculatedField;
var ds   : TDataset;
    AFld1, AFld2, AFld3 : Tfield;
begin
  ds := DBConnector.GetNDataset(5);
  with ds do
    begin
    AFld1 := TIntegerField.Create(ds);
    AFld1.FieldName := 'ID';
    AFld1.DataSet := ds;

    AFld2 := TStringField.Create(ds);
    AFld2.FieldName := 'NAME';
    AFld2.DataSet := ds;

    AFld3 := TIntegerField.Create(ds);
    AFld3.FieldName := 'CALCFLD';
    AFld3.DataSet := ds;
    Afld3.FieldKind := fkCalculated;

    CheckEquals(3,FieldCount);
    ds.OnCalcFields := TestcalculatedField_OnCalcfields;
    open;
    CheckEquals(1,FieldByName('ID').asinteger);
    CheckEquals(5,FieldByName('CALCFLD').asinteger);
    next;
    CheckEquals(70000,FieldByName('CALCFLD').asinteger);
    next;
    CheckEquals(true,FieldByName('CALCFLD').isnull);
    next;
    CheckEquals(1234,FieldByName('CALCFLD').AsInteger);
    edit;
    FieldByName('ID').AsInteger := 10;
    post;
    CheckEquals(true,FieldByName('CALCFLD').isnull);
    close;
    AFld1.Free;
    AFld2.Free;
    AFld3.Free;
    end;
end;

procedure TTestCursorDBBasics.TestEofAfterFirst;
begin
  with DBConnector.GetNDataset(0) do
    begin
    open;
    CheckTrue(eof);
    CheckTrue(BOF);
    first;
    CheckTrue(eof);
    CheckTrue(BOF);
    end;
end;

procedure TTestDBBasics.TestfieldDefinition(AFieldType : TFieldType;ADatasize : integer;var ADS : TDataset; var AFld: TField);

var i          : byte;

begin
  ADS := DBConnector.GetFieldDataset;
  ADS.Open;

  AFld := ADS.FindField('F'+FieldTypeNames[AfieldType]);

{$ifdef fpc}
  if not assigned (AFld) then
    Ignore('Fields of the type ' + FieldTypeNames[AfieldType] + ' are not supported by this type of dataset');
{$endif fpc}
  CheckTrue(Afld.DataType = AFieldType);
  CheckEquals(ADatasize,Afld.DataSize );
end;

procedure TTestDBBasics.TestSupportIntegerFields;

var i          : byte;
    ds         : TDataset;
    Fld        : TField;

begin
  TestfieldDefinition(ftInteger,4,ds,Fld);

  for i := 0 to testValuesCount-1 do
    begin
    CheckEquals(testIntValues[i],Fld.AsInteger);
    ds.Next;
    end;
  ds.close;
end;

procedure TTestDBBasics.TestSupportSmallIntFields;

var i          : byte;
    ds         : TDataset;
    Fld        : TField;

begin
  TestfieldDefinition(ftSmallint,2,ds,Fld);

  for i := 0 to testValuesCount-1 do
    begin
    CheckEquals(testSmallIntValues[i],Fld.AsInteger);
    ds.Next;
    end;
  ds.close;
end;


procedure TTestDBBasics.TestSupportStringFields;

var i          : byte;
    ds         : TDataset;
    Fld        : TField;

begin
  TestfieldDefinition(ftString,11,ds,Fld);

  for i := 0 to testValuesCount-1 do
    begin
    CheckEquals(testStringValues[i],Fld.AsString);
    ds.Next;
    end;
  ds.close;
end;

procedure TTestDBBasics.TestSupportBooleanFields;

var i          : byte;
    ds         : TDataset;
    Fld        : TField;

begin
  TestfieldDefinition(ftBoolean,2,ds,Fld);

  for i := 0 to testValuesCount-1 do
    begin
    CheckEquals(testBooleanValues[i],Fld.AsBoolean);
    ds.Next;
    end;
  ds.close;
end;

procedure TTestDBBasics.TestSupportFloatFields;

var i          : byte;
    ds         : TDataset;
    Fld        : TField;

begin
  TestfieldDefinition(ftFloat,8,ds,Fld);

  for i := 0 to testValuesCount-1 do
    begin
    CheckEquals(testFloatValues[i],Fld.AsFloat);
    ds.Next;
    end;
  ds.close;
end;

procedure TTestDBBasics.TestSupportLargeIntFields;

var i          : byte;
    ds         : TDataset;
    Fld        : TField;

begin
  TestfieldDefinition(ftLargeint,8,ds,Fld);

  for i := 0 to testValuesCount-1 do
    begin
    CheckEquals(testLargeIntValues[i],Fld.AsLargeInt);
    ds.Next;
    end;
  ds.close;
end;

procedure TTestDBBasics.TestSupportDateFields;

var i          : byte;
    ds         : TDataset;
    Fld        : TField;

begin
  TestfieldDefinition(ftDate,8,ds,Fld);

  for i := 0 to testValuesCount-1 do
    begin
    CheckEquals(testDateValues[i], FormatDateTime('yyyy/mm/dd', Fld.AsDateTime, DBConnector.FormatSettings));
    ds.Next;
    end;
  ds.close;
end;

procedure TTestDBBasics.TestSupportTimeFields;
var i          : byte;
    ds         : TDataset;
    Fld        : TField;
begin
  TestfieldDefinition(ftTime,8,ds,Fld);

  for i := 0 to testValuesCount-1 do
    begin
    CheckEquals(testTimeValues[i],DateTimeToTimeString(fld.AsDateTime));
    ds.Next;
    end;
  ds.close;
end;

procedure TTestDBBasics.TestSupportCurrencyFields;

var i          : byte;
    ds         : TDataset;
    Fld        : TField;

begin
  TestfieldDefinition(ftCurrency,8,ds,Fld);

  for i := 0 to testValuesCount-1 do
    begin
    CheckEquals(testCurrencyValues[i],Fld.AsCurrency);
    CheckEquals(testCurrencyValues[i],Fld.AsFloat);
    ds.Next;
    end;
  ds.close;
end;

procedure TTestDBBasics.TestSupportBCDFields;

var i          : byte;
    ds         : TDataset;
    Fld        : TField;

begin
  TestfieldDefinition(ftBCD,8,ds,Fld);

  for i := 0 to testValuesCount-1 do
    begin
    CheckEquals(CurrToStr(testCurrencyValues[i]),Fld.AsString);
    CheckEquals(testCurrencyValues[i],Fld.AsCurrency);
    CheckEquals(testCurrencyValues[i],Fld.AsFloat);
    ds.Next;
    end;
  ds.close;
end;

procedure TTestDBBasics.TestSupportfmtBCDFields;
var i          : byte;
    ds         : TDataset;
    Fld        : TField;

begin
  TestfieldDefinition(ftFMTBcd,sizeof(TBCD),ds,Fld);

  for i := 0 to testValuesCount-1 do
    begin
    CheckEquals(testFmtBCDValues[i], BCDToStr(Fld.AsBCD,DBConnector.FormatSettings));
    CheckEquals(StrToFloat(testFmtBCDValues[i],DBConnector.FormatSettings), Fld.AsFloat);
    ds.Next;
    end;
  ds.close;
end;

procedure TTestDBBasics.TestSupportFixedStringFields;
var i          : byte;
    ds         : TDataset;
    Fld        : TField;

begin
  TestfieldDefinition(ftFixedChar,11,ds,Fld);
  for i := 0 to testValuesCount-1 do
    begin
    if Fld.IsNull then // If the field is null, .AsString always returns an empty, non-padded string
      CheckEquals(testStringValues[i],Fld.AsString)
    else
{$ifdef fpc}
      CheckEquals(PadRight(testStringValues[i],10),Fld.AsString);
{$else fpc}
      CheckEquals(testStringValues[i],Fld.AsString);
{$endif fpc}
    ds.Next;
    end;
  ds.close;
end;

procedure TTestDBBasics.TestDoubleClose;
begin
  with DBConnector.GetNDataset(1) do
    begin
    close;
    close;
    open;
    close;
    close;
    end;
end;

procedure TTestDBBasics.TestAssignFieldftString;
var AParam : TParam;
    AField : TField;
begin
  AParam := TParam.Create(nil);

  with DBConnector.GetNDataset(1) do
    begin
    open;
    AField := fieldbyname('name');
    AParam.AssignField(AField);
    CheckTrue(ftString=AParam.DataType);
    close;
    end;
  AParam.Free;
end;

procedure TTestDBBasics.TestAssignFieldftFixedChar;
var AParam : TParam;
    AField : TField;
begin
  AParam := TParam.Create(nil);
  with DBConnector.GetNDataset(1) do
    begin
    open;
    AField := fieldbyname('name');
    (AField as tstringfield).FixedChar := true;
    AParam.AssignField(AField);
    CheckTrue(ftFixedChar=AParam.DataType);
    close;
    end;
  AParam.Free;
end;

procedure TTestCursorDBBasics.Testbug7007;

var
  datalink1: tdatalink;
  datasource1: tdatasource;
  query1: TDataSet;

begin
  query1:= DBConnector.GetNDataset(6);
  datalink1:= TTestDataLink.create;
  datasource1:= tdatasource.create(nil);
  try
    datalink1.datasource:= datasource1;
    datasource1.dataset:= query1;
    datalink1.datasource:= datasource1;

    DataEvents := '';
    query1.open;
    datalink1.buffercount:= query1.recordcount;
    CheckEquals('deUpdateState:0;',DataEvents);
    CheckEquals(0, datalink1.ActiveRecord);
    CheckEquals(6, datalink1.RecordCount);
    CheckEquals(6, query1.RecordCount);
    CheckEquals(1, query1.RecNo);

    DataEvents := '';
    query1.append;
    CheckEquals('deCheckBrowseMode:0;deUpdateState:0;deDataSetChange:0;DataSetChanged;',DataEvents);
    CheckEquals(5, datalink1.ActiveRecord);
    CheckEquals(6, datalink1.RecordCount);
    CheckEquals(6, query1.RecordCount);
    CheckTrue(query1.RecNo in [0,7]);

    DataEvents := '';
    query1.cancel;
    CheckEquals('deCheckBrowseMode:0;deUpdateState:0;deDataSetChange:0;DataSetChanged;',DataEvents);
    CheckEquals(5, datalink1.ActiveRecord);
    CheckEquals(6, datalink1.RecordCount);
    CheckEquals(6, query1.RecordCount);
    CheckEquals(6, query1.RecNo);
  finally
    datalink1.free;
    datasource1.free;
  end;
end;

procedure TTestCursorDBBasics.TestBug6893;
var
  datalink1: tdatalink;
  datasource1: tdatasource;
  query1: TDataSet;

begin
  query1:= DBConnector.GetNDataset(25);
  datalink1:= TDataLink.create;
  datasource1:= tdatasource.create(nil);
  try
    datalink1.datasource:= datasource1;
    datasource1.dataset:= query1;

    datalink1.buffercount:= 5;
    query1.active := true;
    query1.MoveBy(20);
{$ifdef fpc}
    CheckEquals(5, THackDataLink(datalink1).Firstrecord);
    CheckEquals(4, datalink1.ActiveRecord);
    CheckEquals(21, query1.RecNo);

    query1.active := False;

    CheckEquals(0, THackDataLink(datalink1).Firstrecord);
    CheckEquals(0, datalink1.ActiveRecord);

    query1.active := true;

    CheckEquals(0, THackDataLink(datalink1).Firstrecord);
    CheckEquals(0, datalink1.ActiveRecord);
    CheckEquals(1, query1.RecNo);
{$endif fpc}

  finally
    datalink1.free;
    datasource1.free;
  end;
end;

procedure TTestCursorDBBasics.TestNullAtOpen;
begin
  with dbconnector.getndataset(0) do
    begin
    active:= true;
    CheckTrue(fieldbyname('id').IsNull,'Field isn''t NULL on a just-opened empty dataset');
    append;
    CheckTrue(fieldbyname('id').IsNull,'Field isn''t NULL after append on an empty dataset');
    fieldbyname('id').asinteger:= 123;
    cancel;
    CheckTrue(fieldbyname('id').IsNull,'Field isn''t NULL after cancel');
    end;
end;

{ TDBBasicsUniDirectionalTestSetup }
{$ifdef fpc}
procedure TDBBasicsUniDirectionalTestSetup.OneTimeSetup;
begin
  inherited OneTimeSetup;
  DBConnector.TestUniDirectional:=true;
end;

procedure TDBBasicsUniDirectionalTestSetup.OneTimeTearDown;
begin
  DBConnector.TestUniDirectional:=false;
  inherited OneTimeTearDown;
end;

{ TTestBufDatasetDBBasics }

procedure TTestBufDatasetDBBasics.SetUp;
begin
  DBConnector.StartTest;
end;

procedure TTestBufDatasetDBBasics.TearDown;
begin
  DBConnector.StopTest;
end;
{$endif fpc}

initialization
{$ifdef fpc}
  RegisterTestDecorator(TDBBasicsTestSetup, TTestDBBasics);
  RegisterTestDecorator(TDBBasicsTestSetup, TTestCursorDBBasics);

  // The SQL connectors are descendents of bufdataset and therefore benefit from testing:
  if (uppercase(dbconnectorname)='SQL') or (uppercase(dbconnectorname)='BUFDATASET') then
    begin
    RegisterTestDecorator(TDBBasicsTestSetup, TTestBufDatasetDBBasics);
    RegisterTestDecorator(TDBBasicsUniDirectionalTestSetup, TTestUniDirectionalDBBasics);
    end;
{$else fpc}
  RegisterTest(TTestDBBasics.Suite);
{$endif fpc}
end.
