{
    Copyright (c) 2004 by Joost van der Sluis

    SQL database & dataset

    See the file COPYING.FPC, included in this distribution,
    for details about the copyright.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

 **********************************************************************}

unit sqldb;

{$mode objfpc}
{$H+}
{$M+}   // ### remove this!!!

interface

uses SysUtils, Classes, DB, bufdataset, sqlscript;

type TSchemaType = (stNoSchema, stTables, stSysTables, stProcedures, stColumns, stProcedureParams, stIndexes, stPackages);
     TConnOption = (sqSupportParams,sqEscapeSlash,sqEscapeRepeat);
     TConnOptions= set of TConnOption;

     TRowsCount = LargeInt;

type
  TSQLConnection = class;
  TSQLTransaction = class;
  TCustomSQLQuery = class;
  TSQLQuery = class;
  TSQLScript = class;


  TStatementType = (stUnknown, stSelect, stInsert, stUpdate, stDelete,
    stDDL, stGetSegment, stPutSegment, stExecProcedure,
    stStartTrans, stCommit, stRollback, stSelectForUpd);

  TDBEventType = (detCustom, detPrepare, detExecute, detFetch, detCommit,detRollBack);
  TDBEventTypes = set of TDBEventType;
  TDBLogNotifyEvent = Procedure (Sender : TSQLConnection; EventType : TDBEventType; Const Msg : String) of object;

  TSQLHandle = Class(TObject)
  end;

  { TSQLCursor }

  TSQLCursor = Class(TSQLHandle)
  public
    FPrepared      : Boolean;
    FInitFieldDef  : Boolean;
    FStatementType : TStatementType;
    FSchemaType    : TSchemaType;
  end;

type TQuoteChars = array[0..1] of char;

const
  SingleQuotes : TQuoteChars = ('''','''');
  DoubleQuotes : TQuoteChars = ('"','"');
  LogAllEvents = [detCustom, detPrepare, detExecute, detFetch, detCommit, detRollBack];
  StatementTokens : Array[TStatementType] of string = ('(unknown)', 'select',
                  'insert', 'update', 'delete',
                  'create', 'get', 'put', 'execute',
                  'start','commit','rollback', '?'
                 );

type

  { TServerIndexDefs }

  TServerIndexDefs = class(TIndexDefs)
  Private
  public
    constructor Create(ADataSet: TDataSet); override;
    procedure Update; override;
  end;

type

  { TSQLConnection }

  TSQLConnection = class (TDatabase)
  private
    FFieldNameQuoteChars : TQuoteChars;
    FLogEvents: TDBEventTypes;
    FOnLog: TDBLogNotifyEvent;
    FPassword            : string;
    FTransaction         : TSQLTransaction;
    FUserName            : string;
    FHostName            : string;
    FCharSet             : string;
    FRole                : String;


    function GetPort: cardinal;
    procedure Setport(const AValue: cardinal);
  protected
    FConnOptions         : TConnOptions;
    FSQLFormatSettings : TFormatSettings;
    procedure GetDBInfo(const ASchemaType : TSchemaType; const ASchemaObjectName, AReturnField : string; AList: TStrings);
    procedure SetTransaction(Value : TSQLTransaction);virtual;
    function StrToStatementType(s : string) : TStatementType; virtual;
    procedure DoInternalConnect; override;
    procedure DoInternalDisconnect; override;
    function GetAsSQLText(Field : TField) : string; overload; virtual;
    function GetAsSQLText(Param : TParam) : string; overload; virtual;
    function GetHandle : pointer; virtual; virtual;
    Function LogEvent(EventType : TDBEventType) : Boolean;
    Procedure Log(EventType : TDBEventType; Const Msg : String); virtual;
    Function AllocateCursorHandle : TSQLCursor; virtual; abstract;
    Procedure DeAllocateCursorHandle(var cursor : TSQLCursor); virtual; abstract;
    Function AllocateTransactionHandle : TSQLHandle; virtual; abstract;

    procedure PrepareStatement(cursor: TSQLCursor;ATransaction : TSQLTransaction;buf : string; AParams : TParams); virtual; abstract;
    procedure Execute(cursor: TSQLCursor;atransaction:tSQLtransaction; AParams : TParams); virtual; abstract;
    function Fetch(cursor : TSQLCursor) : boolean; virtual; abstract;
    procedure AddFieldDefs(cursor: TSQLCursor; FieldDefs : TfieldDefs); virtual; abstract;
    procedure UnPrepareStatement(cursor : TSQLCursor); virtual; abstract;

    procedure FreeFldBuffers(cursor : TSQLCursor); virtual;
    function LoadField(cursor : TSQLCursor;FieldDef : TfieldDef;buffer : pointer; out CreateBlob : boolean) : boolean; virtual; abstract;
    function GetTransactionHandle(trans : TSQLHandle): pointer; virtual; abstract;
    function Commit(trans : TSQLHandle) : boolean; virtual; abstract;
    function RollBack(trans : TSQLHandle) : boolean; virtual; abstract;
    function StartdbTransaction(trans : TSQLHandle; aParams : string) : boolean; virtual; abstract;
    procedure CommitRetaining(trans : TSQLHandle); virtual; abstract;
    procedure RollBackRetaining(trans : TSQLHandle); virtual; abstract;
    procedure UpdateIndexDefs(IndexDefs : TIndexDefs;TableName : string); virtual;
    function GetSchemaInfoSQL(SchemaType : TSchemaType; SchemaObjectName, SchemaPattern : string) : string; virtual;
    procedure LoadBlobIntoBuffer(FieldDef: TFieldDef;ABlobBuf: PBufBlobField; cursor: TSQLCursor; ATransaction : TSQLTransaction); virtual; abstract;
    function RowsAffected(cursor: TSQLCursor): TRowsCount; virtual;
    property port: cardinal read GetPort write Setport;
  public
    property Handle: Pointer read GetHandle;
    property FieldNameQuoteChars: TQuoteChars read FFieldNameQuoteChars write FFieldNameQuoteChars;
    constructor Create(AOwner: TComponent); override;
    destructor Destroy; override;
    procedure StartTransaction; override;
    procedure EndTransaction; override;
    property ConnOptions: TConnOptions read FConnOptions;
    procedure ExecuteDirect(SQL : String); overload; virtual;
    procedure ExecuteDirect(SQL : String; ATransaction : TSQLTransaction); overload; virtual;
    procedure GetTableNames(List : TStrings; SystemTables : Boolean = false); virtual;
    procedure GetProcedureNames(List : TStrings); virtual;
    procedure GetFieldNames(const TableName : string; List :  TStrings); virtual;
    procedure CreateDB; virtual;
    procedure DropDB; virtual;
  published
    property Password : string read FPassword write FPassword;
    property Transaction : TSQLTransaction read FTransaction write SetTransaction;
    property UserName : string read FUserName write FUserName;
    property CharSet : string read FCharSet write FCharSet;
    property HostName : string Read FHostName Write FHostName;
    Property OnLog : TDBLogNotifyEvent Read FOnLog Write FOnLog;
    Property LogEvents : TDBEventTypes Read FLogEvents Write FLogEvents Default LogAllEvents;
    property Connected;
    Property Role :  String read FRole write FRole;
    property DatabaseName;
    property KeepConnection;
    property LoginPrompt;
    property Params;
    property OnLogin;
  end;

{ TSQLTransaction }

  TCommitRollbackAction = (caNone, caCommit, caCommitRetaining, caRollback,
    caRollbackRetaining);

  TSQLTransaction = class (TDBTransaction)
  private
    FTrans               : TSQLHandle;
    FAction              : TCommitRollbackAction;
    FParams              : TStringList;
    procedure SetParams(const AValue: TStringList);
  protected
    function GetHandle : Pointer; virtual;
    Procedure SetDatabase (Value : TDatabase); override;
    Function LogEvent(EventType : TDBEventType) : Boolean;
    Procedure Log(EventType : TDBEventType; Const Msg : String); virtual;
  public
    procedure Commit; virtual;
    procedure CommitRetaining; virtual;
    procedure Rollback; virtual;
    procedure RollbackRetaining; virtual;
    procedure StartTransaction; override;
    constructor Create(AOwner : TComponent); override;
    destructor Destroy; override;
    property Handle: Pointer read GetHandle;
    procedure EndTransaction; override;
  published
    property Action : TCommitRollbackAction read FAction write FAction;
    property Database;
    property Params : TStringList read FParams write SetParams;
  end;

{ TCustomSQLQuery }

  TCustomSQLQuery = class (TCustomBufDataset)
  private
    FCursor              : TSQLCursor;
    FUpdateable          : boolean;
    FTableName           : string;
    FSQL                 : TStringList;
    FUpdateSQL,
    FInsertSQL,
    FDeleteSQL           : TStringList;
    FIsEOF               : boolean;
    FLoadingFieldDefs    : boolean;
    FUpdateMode          : TUpdateMode;
    FParams              : TParams;
    FusePrimaryKeyAsKey  : Boolean;
    FSQLBuf              : String;
    FWhereStartPos       : integer;
    FWhereStopPos        : integer;
    FParseSQL            : boolean;
    FMasterLink          : TMasterParamsDatalink;
//    FSchemaInfo          : TSchemaInfo;

    FServerFilterText    : string;
    FServerFiltered      : Boolean;

    FServerIndexDefs     : TServerIndexDefs;

    // Used by SetSchemaType
    FSchemaType          : TSchemaType;
    FSchemaObjectName    : string;
    FSchemaPattern       : string;

    FUpdateQry,
    FDeleteQry,
    FInsertQry           : TCustomSQLQuery;
    procedure FreeFldBuffers;
    function GetServerIndexDefs: TServerIndexDefs;
    function GetStatementType : TStatementType;
    procedure SetDeleteSQL(const AValue: TStringlist);
    procedure SetInsertSQL(const AValue: TStringlist);
    procedure SetParseSQL(AValue : Boolean);
    procedure SetSQL(const AValue: TStringlist);
    procedure SetUpdateSQL(const AValue: TStringlist);
    procedure SetUsePrimaryKeyAsKey(AValue : Boolean);
    procedure SetUpdateMode(AValue : TUpdateMode);
    procedure OnChangeSQL(Sender : TObject);
    procedure OnChangeModifySQL(Sender : TObject);
    procedure Execute;
    Function SQLParser(const ASQL : string) : TStatementType;
    procedure ApplyFilter;
    Function AddFilter(SQLstr : string) : string;
  protected
    // abstract & virtual methods of TBufDataset
    function Fetch : boolean; override;
    function LoadField(FieldDef : TFieldDef;buffer : pointer; out CreateBlob : boolean) : boolean; override;
    // abstract & virtual methods of TDataset
    procedure UpdateServerIndexDefs; virtual;
    procedure SetDatabase(Value : TDatabase); override;
    Procedure SetTransaction(Value : TDBTransaction); override;
    procedure InternalAddRecord(Buffer: Pointer; AAppend: Boolean); override;
    procedure InternalClose; override;
    procedure InternalInitFieldDefs; override;
    procedure InternalOpen; override;
    function  GetCanModify: Boolean; override;
    procedure ApplyRecUpdate(UpdateKind : TUpdateKind); override;
    Function IsPrepared : Boolean; virtual;
    Procedure SetActive (Value : Boolean); override;
    procedure SetServerFiltered(Value: Boolean); virtual;
    procedure SetServerFilterText(const Value: string); virtual;
    Function GetDataSource : TDatasource; override;
    Procedure SetDataSource(AValue : TDatasource);
    procedure LoadBlobIntoBuffer(FieldDef: TFieldDef;ABlobBuf: PBufBlobField); override;
    procedure BeforeRefreshOpenCursor; override;
    procedure SetReadOnly(AValue : Boolean); override;
    Function LogEvent(EventType : TDBEventType) : Boolean;
    Procedure Log(EventType : TDBEventType; Const Msg : String); virtual;
  public
    procedure Prepare; virtual;
    procedure UnPrepare; virtual;
    procedure ExecSQL; virtual;
    constructor Create(AOwner : TComponent); override;
    destructor Destroy; override;
    procedure SetSchemaInfo( ASchemaType : TSchemaType; ASchemaObjectName, ASchemaPattern : string); virtual;
    property Prepared : boolean read IsPrepared;
    procedure Notification(AComponent: TComponent; Operation: TOperation); override;
    function RowsAffected: TRowsCount; virtual;
    function ParamByName(Const AParamName : String) : TParam;
  protected

    // redeclared data set properties
    property Active;
    property Filter;
    property Filtered;
//    property FilterOptions;
    property BeforeOpen;
    property AfterOpen;
    property BeforeClose;
    property AfterClose;
    property BeforeInsert;
    property AfterInsert;
    property BeforeEdit;
    property AfterEdit;
    property BeforePost;
    property AfterPost;
    property BeforeCancel;
    property AfterCancel;
    property BeforeDelete;
    property AfterDelete;
    property BeforeScroll;
    property AfterScroll;
    property OnCalcFields;
    property OnDeleteError;
    property OnEditError;
    property OnFilterRecord;
    property OnNewRecord;
    property OnPostError;
    property AutoCalcFields;
    property Database;
  // protected
    property SchemaType : TSchemaType read FSchemaType default stNoSchema;
    property Transaction;
    property SQL : TStringlist read FSQL write SetSQL;
    property UpdateSQL : TStringlist read FUpdateSQL write SetUpdateSQL;
    property InsertSQL : TStringlist read FInsertSQL write SetInsertSQL;
    property DeleteSQL : TStringlist read FDeleteSQL write SetDeleteSQL;
    property Params : TParams read FParams write FParams;
    property UpdateMode : TUpdateMode read FUpdateMode write SetUpdateMode default upWhereKeyOnly;
    property UsePrimaryKeyAsKey : boolean read FUsePrimaryKeyAsKey write SetUsePrimaryKeyAsKey default true;
    property StatementType : TStatementType read GetStatementType;
    property ParseSQL : Boolean read FParseSQL write SetParseSQL default true;
    Property DataSource : TDatasource Read GetDataSource Write SetDatasource;
    property ServerFilter: string read FServerFilterText write SetServerFilterText;
    property ServerFiltered: Boolean read FServerFiltered write SetServerFiltered default False;
    property ServerIndexDefs : TServerIndexDefs read GetServerIndexDefs;
  end;

{ TSQLQuery }
  TSQLQuery = Class(TCustomSQLQuery)
  public
    property SchemaType;
  Published
    property MaxIndexesCount;
   // TDataset stuff
    property FieldDefs;
    Property Active;
    Property AutoCalcFields;
    Property Filter;
    Property Filtered;
    Property AfterCancel;
    Property AfterClose;
    Property AfterDelete;
    Property AfterEdit;
    Property AfterInsert;
    Property AfterOpen;
    Property AfterPost;
    Property AfterScroll;
    Property BeforeCancel;
    Property BeforeClose;
    Property BeforeDelete;
    Property BeforeEdit;
    Property BeforeInsert;
    Property BeforeOpen;
    Property BeforePost;
    Property BeforeScroll;
    Property OnCalcFields;
    Property OnDeleteError;
    Property OnEditError;
    Property OnFilterRecord;
    Property OnNewRecord;
    Property OnPostError;

    //    property SchemaInfo default stNoSchema;
    property Database;
    property Transaction;
    property ReadOnly;
    property SQL;
    property UpdateSQL;
    property InsertSQL;
    property DeleteSQL;
    property IndexDefs;
    property Params;
    property UpdateMode;
    property UsePrimaryKeyAsKey;
    property ParseSQL;
    Property DataSource;
    property ServerFilter;
    property ServerFiltered;
    property ServerIndexDefs;
  end;

{ TSQLScript }

  TSQLScript = class (TCustomSQLscript)
  private
    FOnDirective: TSQLScriptDirectiveEvent;
    FQuery   : TCustomSQLQuery;
    FDatabase : TDatabase;
    FTransaction : TDBTransaction;
  protected
    procedure ExecuteStatement (SQLStatement: TStrings; var StopExecution: Boolean); override;
    procedure ExecuteDirective (Directive, Argument: String; var StopExecution: Boolean); override;
    procedure ExecuteCommit; override;
    Procedure SetDatabase (Value : TDatabase); virtual;
    Procedure SetTransaction(Value : TDBTransaction); virtual;
    Procedure CheckDatabase;
  public
    constructor Create(AOwner : TComponent); override;
    destructor Destroy; override;
    procedure Execute; override;
    procedure ExecuteScript;
  published
    Property DataBase : TDatabase Read FDatabase Write SetDatabase;
    Property Transaction : TDBTransaction Read FTransaction Write SetTransaction;
    property OnDirective: TSQLScriptDirectiveEvent read FOnDirective write FOnDirective;
    property Directives;
    property Defines;
    property Script;
    property Terminator;
    property CommentsinSQL;
    property UseSetTerm;
    property UseCommit;
    property UseDefines;
    property OnException;
  end;

  { TSQLConnector }

  TSQLConnector = Class(TSQLConnection)
  private
    FProxy : TSQLConnection;
    FConnectorType: String;
    procedure SetConnectorType(const AValue: String);
  protected
    procedure SetTransaction(Value : TSQLTransaction);override;
    procedure DoInternalConnect; override;
    procedure DoInternalDisconnect; override;
    Procedure CheckProxy;
    Procedure CreateProxy; virtual;
    Procedure FreeProxy; virtual;
    function StrToStatementType(s : string) : TStatementType; override;
    function GetAsSQLText(Field : TField) : string; overload; override;
    function GetAsSQLText(Param : TParam) : string; overload; override;
    function GetHandle : pointer; override;

    Function AllocateCursorHandle : TSQLCursor; override;
    Procedure DeAllocateCursorHandle(var cursor : TSQLCursor); override;
    Function AllocateTransactionHandle : TSQLHandle; override;

    procedure PrepareStatement(cursor: TSQLCursor;ATransaction : TSQLTransaction;buf : string; AParams : TParams); override;
    procedure Execute(cursor: TSQLCursor;atransaction:tSQLtransaction; AParams : TParams); override;
    function Fetch(cursor : TSQLCursor) : boolean; override;
    procedure AddFieldDefs(cursor: TSQLCursor; FieldDefs : TfieldDefs); override;
    procedure UnPrepareStatement(cursor : TSQLCursor); override;

    procedure FreeFldBuffers(cursor : TSQLCursor); override;
    function LoadField(cursor : TSQLCursor;FieldDef : TfieldDef;buffer : pointer; out CreateBlob : boolean) : boolean; override;
    function RowsAffected(cursor: TSQLCursor): TRowsCount; override;
    function GetTransactionHandle(trans : TSQLHandle): pointer; override;
    function Commit(trans : TSQLHandle) : boolean; override;
    function RollBack(trans : TSQLHandle) : boolean; override;
    function StartdbTransaction(trans : TSQLHandle; aParams : string) : boolean; override;
    procedure CommitRetaining(trans : TSQLHandle); override;
    procedure RollBackRetaining(trans : TSQLHandle); override;
    procedure UpdateIndexDefs(IndexDefs : TIndexDefs;TableName : string); override;
    function GetSchemaInfoSQL(SchemaType : TSchemaType; SchemaObjectName, SchemaPattern : string) : string; override;
    procedure LoadBlobIntoBuffer(FieldDef: TFieldDef;ABlobBuf: PBufBlobField; cursor: TSQLCursor; ATransaction : TSQLTransaction); override;
    Property Proxy : TSQLConnection Read FProxy;
  Published
    Property ConnectorType : String Read FConnectorType Write SetConnectorType;
  end;

  TSQLConnectionClass = Class of TSQLConnection;

  { TConnectionDef }

  TConnectionDef = Class(TPersistent)
    Class Function TypeName : String; virtual;
    Class Function ConnectionClass : TSQLConnectionClass; virtual;
    Class Function Description : String; virtual;
    Procedure ApplyParams(Params : TStrings; AConnection : TSQLConnection); virtual;
  end;
  TConnectionDefClass = class of TConnectionDef;

Var
  GlobalDBLogHook : TDBLogNotifyEvent;

Procedure RegisterConnection(Def : TConnectionDefClass);
Procedure UnRegisterConnection(Def : TConnectionDefClass);
Procedure UnRegisterConnection(ConnectionName : String);
Function GetConnectionDef(ConnectorName : String) : TConnectionDef;
Procedure GetConnectionList(List : TSTrings);

const DefaultSQLFormatSettings : TFormatSettings = (
  CurrencyFormat: 1;
  NegCurrFormat: 5;
  ThousandSeparator: #0;
  DecimalSeparator: '.';
  CurrencyDecimals: 2;
  DateSeparator: '-';
  TimeSeparator: ':';
  ListSeparator: ' ';
  CurrencyString: '$';
  ShortDateFormat: 'yyyy-mm-dd';
  LongDateFormat: '';
  TimeAMString: '';
  TimePMString: '';
  ShortTimeFormat: 'hh:nn:ss';
  LongTimeFormat: 'hh:nn:ss.zzz';
  ShortMonthNames: ('','','','','','','','','','','','');
  LongMonthNames: ('','','','','','','','','','','','');
  ShortDayNames: ('','','','','','','');
  LongDayNames: ('','','','','','','');
  TwoDigitYearCenturyWindow: 50;
);

implementation

uses dbconst, strutils;


function TimeIntervalToString(Time: TDateTime): string;
var
  millisecond: word;
  second     : word;
  minute     : word;
  hour       : word;
begin
  DecodeTime(Time,hour,minute,second,millisecond);
  hour := hour + (trunc(Time) * 24);
  result := Format('%.2d:%.2d:%.2d.%.3d',[hour,minute,second,millisecond]);
end;

{ TSQLConnection }

function TSQLConnection.StrToStatementType(s : string) : TStatementType;

var T : TStatementType;

begin
  S:=Lowercase(s);
  for T:=stSelect to stRollback do
    if (S=StatementTokens[T]) then
      Exit(T);
  Result:=stUnknown;
end;

procedure TSQLConnection.SetTransaction(Value : TSQLTransaction);
begin
  if FTransaction<>value then
    begin
    if Assigned(FTransaction) and FTransaction.Active then
      DatabaseError(SErrAssTransaction);
    if Assigned(Value) then
      Value.Database := Self;
    FTransaction := Value;
    If Assigned(FTransaction) and (FTransaction.Database=Nil) then
      FTransaction.Database:=Self;
    end;
end;

procedure TSQLConnection.UpdateIndexDefs(IndexDefs : TIndexDefs;TableName : string);

begin
// Empty abstract
end;

procedure TSQLConnection.DoInternalConnect;
begin
  if (DatabaseName = '') then
    DatabaseError(SErrNoDatabaseName,self);
end;

procedure TSQLConnection.DoInternalDisconnect;
begin
end;

destructor TSQLConnection.Destroy;
begin
  inherited Destroy;
end;

procedure TSQLConnection.StartTransaction;
begin
  if not assigned(Transaction) then
    DatabaseError(SErrConnTransactionnSet)
  else
    Transaction.StartTransaction;
end;

procedure TSQLConnection.EndTransaction;
begin
  if not assigned(Transaction) then
    DatabaseError(SErrConnTransactionnSet)
  else
    Transaction.EndTransaction;
end;

Procedure TSQLConnection.ExecuteDirect(SQL: String);

begin
  ExecuteDirect(SQL,FTransaction);
end;

Procedure TSQLConnection.ExecuteDirect(SQL: String; ATransaction : TSQLTransaction);

var Cursor : TSQLCursor;

begin
  if not assigned(ATransaction) then
    DatabaseError(SErrTransactionnSet);

  if not Connected then Open;
  if not ATransaction.Active then ATransaction.StartTransaction;

  try
    SQL := TrimRight(SQL);
    if SQL = '' then
      DatabaseError(SErrNoStatement);

    Cursor := AllocateCursorHandle;
    Cursor.FStatementType := stUnknown;
    PrepareStatement(cursor,ATransaction,SQL,Nil);
    execute(cursor,ATransaction, Nil);
    UnPrepareStatement(Cursor);
  finally;
    DeAllocateCursorHandle(Cursor);
  end;
end;

function TSQLConnection.GetPort: cardinal;
begin
  result := StrToIntDef(Params.Values['Port'],0);
end;

procedure TSQLConnection.Setport(const AValue: cardinal);
begin
  if AValue<>0 then
    params.Values['Port']:=IntToStr(AValue)
  else with params do if IndexOfName('Port') > -1 then
    Delete(IndexOfName('Port'));
end;

procedure TSQLConnection.GetDBInfo(const ASchemaType : TSchemaType; const ASchemaObjectName, AReturnField : string; AList: TStrings);

var qry : TCustomSQLQuery;

begin
  if not assigned(Transaction) then
    DatabaseError(SErrConnTransactionnSet);

  qry := TCustomSQLQuery.Create(nil);
  qry.transaction := Transaction;
  qry.database := Self;
  with qry do
    begin
    ParseSQL := False;
    SetSchemaInfo(ASchemaType,ASchemaObjectName,'');
    open;
    AList.Clear;
    while not eof do
      begin
      AList.Append(trim(fieldbyname(AReturnField).asstring));
      Next;
      end;
    end;
  qry.free;
end;

function TSQLConnection.RowsAffected(cursor: TSQLCursor): TRowsCount;
begin
  Result := -1;
end;


constructor TSQLConnection.Create(AOwner: TComponent);
begin
  inherited Create(AOwner);
  FSQLFormatSettings:=DefaultSQLFormatSettings;
  FFieldNameQuoteChars:=DoubleQuotes;
end;

procedure TSQLConnection.GetTableNames(List: TStrings; SystemTables: Boolean);
begin
  if not systemtables then GetDBInfo(stTables,'','table_name',List)
    else GetDBInfo(stSysTables,'','table_name',List);
end;

procedure TSQLConnection.GetProcedureNames(List: TStrings);
begin
  GetDBInfo(stProcedures,'','proc_name',List);
end;

procedure TSQLConnection.GetFieldNames(const TableName: string; List: TStrings);
begin
  GetDBInfo(stColumns,TableName,'column_name',List);
end;

function TSQLConnection.GetAsSQLText(Field : TField) : string;

begin
  if (not assigned(field)) or field.IsNull then Result := 'Null'
  else case field.DataType of
    ftString   : Result := QuotedStr(Field.AsString);
    ftDate     : Result := '''' + FormatDateTime('yyyy-mm-dd',Field.AsDateTime,FSqlFormatSettings) + '''';
    ftDateTime : Result := '''' + FormatDateTime('yyyy-mm-dd hh:nn:ss.zzz',Field.AsDateTime,FSqlFormatSettings) + '''';
    ftTime     : Result := QuotedStr(TimeIntervalToString(Field.AsDateTime));
  else
    Result := field.asstring;
  end; {case}
end;

function TSQLConnection.GetAsSQLText(Param: TParam) : string;
begin
  if (not assigned(param)) or param.IsNull then Result := 'Null'
  else case param.DataType of
    ftGuid,
    ftMemo,
    ftFixedChar,
    ftString   : Result := QuotedStr(Param.AsString);
    ftDate     : Result := '''' + FormatDateTime('yyyy-mm-dd',Param.AsDateTime,FSQLFormatSettings) + '''';
    ftTime     : Result := QuotedStr(TimeIntervalToString(Param.AsDateTime));
    ftDateTime : Result := '''' + FormatDateTime('yyyy-mm-dd hh:nn:ss.zzz', Param.AsDateTime, FSQLFormatSettings) + '''';
    ftCurrency,
    ftBcd      : Result := CurrToStr(Param.AsCurrency, FSQLFormatSettings);
    ftFloat    : Result := FloatToStr(Param.AsFloat, FSQLFormatSettings);
    ftFMTBcd   : Result := stringreplace(Param.AsString, DefaultFormatSettings.DecimalSeparator, FSQLFormatSettings.DecimalSeparator, []);
  else
    Result := Param.asstring;
  end; {case}
end;


function TSQLConnection.GetHandle: pointer;
begin
  Result := nil;
end;

function TSQLConnection.LogEvent(EventType: TDBEventType): Boolean;
begin
  Result:=(Assigned(FOnLog) or Assigned(GlobalDBLogHook)) and (EventType in LogEvents);
end;

procedure TSQLConnection.Log(EventType: TDBEventType; const Msg: String);

Var
  M : String;

begin
  If LogEvent(EventType) then
    begin
    If Assigned(FonLog) then
      FOnLog(Self,EventType,Msg);
    If Assigned(GlobalDBLogHook) then
      begin
      If (Name<>'') then
        M:=Name+' : '+Msg
      else
        M:=ClassName+' : '+Msg;
      GlobalDBLogHook(Self,EventType,M);
      end;
    end;
end;

procedure TSQLConnection.FreeFldBuffers(cursor: TSQLCursor);
begin
  // empty
end;

function TSQLConnection.GetSchemaInfoSQL( SchemaType : TSchemaType; SchemaObjectName, SchemaPattern : string) : string;

begin
  DatabaseError(SMetadataUnavailable);
end;

procedure TSQLConnection.CreateDB;

begin
  DatabaseError(SNotSupported);
end;

procedure TSQLConnection.DropDB;

begin
  DatabaseError(SNotSupported);
end;

{ TSQLTransaction }
procedure TSQLTransaction.EndTransaction;

begin
  rollback;
end;

procedure TSQLTransaction.SetParams(const AValue: TStringList);
begin
  FParams.Assign(AValue);
end;

function TSQLTransaction.GetHandle: pointer;
begin
  Result := TSQLConnection(Database).GetTransactionHandle(FTrans);
end;

procedure TSQLTransaction.Commit;
begin
  if active then
    begin
    closedatasets;
    If LogEvent(detCommit) then
      Log(detCommit,SCommitting);
    if TSQLConnection(Database).commit(FTrans) then
      begin
      closeTrans;
      FreeAndNil(FTrans);
      end;
    end;
end;

procedure TSQLTransaction.CommitRetaining;
begin
  if active then
    begin
    If LogEvent(detCommit) then
      Log(detCommit,SCommitRetaining);
    TSQLConnection(Database).commitRetaining(FTrans);
    end;
end;

procedure TSQLTransaction.Rollback;
begin
  if active then
    begin
    closedatasets;
    If LogEvent(detRollback) then
      Log(detRollback,SRollingBack);
    if TSQLConnection(Database).RollBack(FTrans) then
      begin
      CloseTrans;
      FreeAndNil(FTrans);
      end;
    end;
end;

procedure TSQLTransaction.RollbackRetaining;
begin
  if active then
    begin
    If LogEvent(detRollback) then
      Log(detRollback,SRollBackRetaining);
    TSQLConnection(Database).RollBackRetaining(FTrans);
    end;
end;

procedure TSQLTransaction.StartTransaction;

var db : TSQLConnection;

begin
  if Active then
    DatabaseError(SErrTransAlreadyActive);

  db := TSQLConnection(Database);

  if Db = nil then
    DatabaseError(SErrDatabasenAssigned);

  if not Db.Connected then
    Db.Open;
  if not assigned(FTrans) then FTrans := Db.AllocateTransactionHandle;

  if Db.StartdbTransaction(FTrans,FParams.CommaText) then OpenTrans;
end;

constructor TSQLTransaction.Create(AOwner : TComponent);
begin
  inherited Create(AOwner);
  FParams := TStringList.Create;
end;

destructor TSQLTransaction.Destroy;
begin
  Rollback;
  FreeAndNil(FParams);
  inherited Destroy;
end;

Procedure TSQLTransaction.SetDatabase(Value : TDatabase);

begin
  If Value<>Database then
    begin
    if assigned(value) and not (Value is TSQLConnection) then
      DatabaseErrorFmt(SErrNotASQLConnection,[value.Name],self);
    CheckInactive;
    If Assigned(Database) then
      with TSQLConnection(DataBase) do
        if Transaction = self then Transaction := nil;
    inherited SetDatabase(Value);
    If Assigned(Database) and not (csLoading in ComponentState) then
      If (TSQLConnection(DataBase).Transaction=Nil) then
        TSQLConnection(DataBase).Transaction:=Self;
    end;
end;

function TSQLTransaction.LogEvent(EventType: TDBEventType): Boolean;
begin
  Result:=Assigned(Database) and TSQLConnection(Database).LogEvent(EventType);
end;

procedure TSQLTransaction.Log(EventType: TDBEventType; const Msg: String);

Var
  M : String;

begin
  If LogEVent(EventType) then
    begin
    If (Name<>'') then
      M:=Name+' : '+Msg
    else
      M:=Msg;
    TSQLConnection(Database).Log(EventType,M);
    end;
end;

{ TCustomSQLQuery }
procedure TCustomSQLQuery.OnChangeSQL(Sender : TObject);

var ConnOptions : TConnOptions;
    NewParams: TParams;

begin
  UnPrepare;
  FSchemaType:=stNoSchema;
  if (FSQL <> nil) then
    begin
    if assigned(DataBase) then
      ConnOptions := TSQLConnection(DataBase).ConnOptions
    else
      ConnOptions := [sqEscapeRepeat,sqEscapeSlash];
    //preserve existing param. values
    NewParams := TParams.Create(Self);
    try
      NewParams.ParseSQL(FSQL.Text, True, sqEscapeSlash in ConnOptions, sqEscapeRepeat in ConnOptions, psInterbase);
      NewParams.AssignValues(FParams);
      FParams.Assign(NewParams);
    finally
      NewParams.Free;
    end;
    If Assigned(FMasterLink) then
      FMasterLink.RefreshParamNames;
    end;
end;

function TCustomSQLQuery.ParamByName(Const AParamName : String) : TParam;

begin
  Result:=Params.ParamByName(AParamName);
end;

procedure TCustomSQLQuery.OnChangeModifySQL(Sender : TObject);

begin
  CheckInactive;
end;

Procedure TCustomSQLQuery.SetTransaction(Value : TDBTransaction);

begin
  UnPrepare;
  inherited;
  If (Transaction<>Nil) and (Database=Nil) then
    Database:=TSQLTransaction(Transaction).Database;
end;

procedure TCustomSQLQuery.SetDatabase(Value : TDatabase);

var db : tsqlconnection;

begin
  if (Database <> Value) then
    begin
    if assigned(value) and not (Value is TSQLConnection) then
      DatabaseErrorFmt(SErrNotASQLConnection,[value.Name],self);
    UnPrepare;
    if assigned(FCursor) then TSQLConnection(DataBase).DeAllocateCursorHandle(FCursor);
    db := TSQLConnection(Value);
    inherited setdatabase(value);
    if assigned(value) and (Transaction = nil) and (Assigned(db.Transaction)) then
      transaction := Db.Transaction;
    OnChangeSQL(Self);
    end;
end;

Function TCustomSQLQuery.IsPrepared : Boolean;

begin
  Result := Assigned(FCursor) and FCursor.FPrepared;
end;

Function TCustomSQLQuery.AddFilter(SQLstr : string) : string;

begin
  if (FWhereStartPos > 0) and (FWhereStopPos > 0) then
    begin
    system.insert('(',SQLstr,FWhereStartPos+1);
    system.insert(')',SQLstr,FWhereStopPos+1);
    end;

  if FWhereStartPos = 0 then
    SQLstr := SQLstr + ' where (' + Filter + ')'
  else if FWhereStopPos > 0 then
    system.insert(' and ('+ServerFilter+') ',SQLstr,FWhereStopPos+2)
  else
    system.insert(' where ('+ServerFilter+') ',SQLstr,FWhereStartPos);
  Result := SQLstr;
end;

procedure TCustomSQLQuery.ApplyFilter;

var S : String;

begin
  FreeFldBuffers;
  TSQLConnection(Database).UnPrepareStatement(FCursor);
  FIsEOF := False;
  inherited internalclose;

  s := FSQLBuf;

  if ServerFiltered then s := AddFilter(s);

  TSQLConnection(Database).PrepareStatement(Fcursor,(transaction as tsqltransaction),S,FParams);

  Execute;
  inherited InternalOpen;
  First;
end;

Procedure TCustomSQLQuery.SetActive (Value : Boolean);

begin
  inherited SetActive(Value);
// The query is UnPrepared, so that if a transaction closes all datasets
// they also get unprepared
  if not Value and IsPrepared then UnPrepare;
end;


procedure TCustomSQLQuery.SetServerFiltered(Value: Boolean);

begin
  if Value and not FParseSQL then DatabaseErrorFmt(SNoParseSQL,['Filtering ']);
  if (ServerFiltered <> Value) then
    begin
    FServerFiltered := Value;
    if active then ApplyFilter;
    end;
end;

procedure TCustomSQLQuery.SetServerFilterText(const Value: string);
begin
  if Value <> ServerFilter then
    begin
    FServerFilterText := Value;
    if active then ApplyFilter;
    end;
end;

procedure TCustomSQLQuery.Prepare;
var
  db     : tsqlconnection;
  sqltr  : tsqltransaction;
  StmType: TStatementType;

begin
  if not IsPrepared then
    begin
    db := TSQLConnection(Database);
    sqltr := (transaction as tsqltransaction);
    if not assigned(Db) then
      DatabaseError(SErrDatabasenAssigned);
    if not assigned(sqltr) then
      DatabaseError(SErrTransactionnSet);

    if not Db.Connected then db.Open;
    if not sqltr.Active then sqltr.StartTransaction;

    if FSchemaType=stNoSchema then
      FSQLBuf := TrimRight(FSQL.Text)
    else
      FSQLBuf := db.GetSchemaInfoSQL(FSchemaType, FSchemaObjectName, FSchemaPattern);

    if FSQLBuf = '' then
      DatabaseError(SErrNoStatement);

    StmType:=SQLParser(FSQLBuf);

    // There may no error occur between the allocation of the cursor and
    // the preparation of the cursor. Because internalclose (which is called in
    // case of an exception) assumes that allocated cursors are also prepared,
    // and thus calls unprepare.
    // A call to unprepare while the cursor is not prepared at all can lead to
    // unpredictable results.
    if not assigned(fcursor) then
      FCursor := Db.AllocateCursorHandle;
    FCursor.FStatementType:=StmType;
    FCursor.FSchemaType := FSchemaType;
    if ServerFiltered then
      begin
      If LogEvent(detprepare) then
        Log(detPrepare,AddFilter(FSQLBuf));
      Db.PrepareStatement(Fcursor,sqltr,AddFilter(FSQLBuf),FParams)
      end
    else
      begin
      If LogEvent(detprepare) then
        Log(detPrepare,FSQLBuf);
      Db.PrepareStatement(Fcursor,sqltr,FSQLBuf,FParams);
      end;
    if (FCursor.FStatementType in [stSelect,stExecProcedure]) then
      FCursor.FInitFieldDef := True;
    end;
end;

procedure TCustomSQLQuery.UnPrepare;

begin
  CheckInactive;
  if IsPrepared then with TSQLConnection(DataBase) do
    UnPrepareStatement(FCursor);
end;

procedure TCustomSQLQuery.FreeFldBuffers;
begin
  if assigned(FCursor) then TSQLConnection(Database).FreeFldBuffers(FCursor);
end;

function TCustomSQLQuery.GetServerIndexDefs: TServerIndexDefs;
begin
  Result := FServerIndexDefs;
end;

function TCustomSQLQuery.Fetch : boolean;
begin
  if not (Fcursor.FStatementType in [stSelect,stExecProcedure]) then
    Exit;

  if not FIsEof then FIsEOF := not TSQLConnection(Database).Fetch(Fcursor);
  Result := not FIsEOF;
end;

procedure TCustomSQLQuery.Execute;
begin
  If (FParams.Count>0) and Assigned(FMasterLink) then
    FMasterLink.CopyParamsFromMaster(False);
  If LogEvent(detExecute) then
    Log(detExecute,FSQLBuf);
  TSQLConnection(Database).execute(Fcursor,Transaction as tsqltransaction, FParams);
end;

function TCustomSQLQuery.LoadField(FieldDef : TFieldDef;buffer : pointer; out CreateBlob : boolean) : boolean;

begin
  result := TSQLConnection(Database).LoadField(FCursor,FieldDef,buffer, Createblob)
end;

function TCustomSQLQuery.RowsAffected: TRowsCount;
begin
  Result := -1;
  if not Assigned(Database) then Exit;
  //assert(Database is TSQLConnection);
  Result := TSQLConnection(Database).RowsAffected(FCursor);
end;

procedure TCustomSQLQuery.InternalAddRecord(Buffer: Pointer; AAppend: Boolean);
begin
  // not implemented - sql dataset
end;

procedure TCustomSQLQuery.InternalClose;
begin
  if not IsReadFromPacket then
    begin
    if StatementType in [stSelect,stExecProcedure] then FreeFldBuffers;
    // Database and FCursor could be nil, for example if the database is not assigned, and .open is called
    if (not IsPrepared) and (assigned(database)) and (assigned(FCursor)) then TSQLConnection(database).UnPrepareStatement(FCursor);
    end;
  if DefaultFields then
    DestroyFields;
  FIsEOF := False;
  if assigned(FUpdateQry) then FreeAndNil(FUpdateQry);
  if assigned(FInsertQry) then FreeAndNil(FInsertQry);
  if assigned(FDeleteQry) then FreeAndNil(FDeleteQry);
//  FRecordSize := 0;
  inherited internalclose;
end;

procedure TCustomSQLQuery.InternalInitFieldDefs;
begin
  if FLoadingFieldDefs then
    Exit;

  FLoadingFieldDefs := True;

  try
    FieldDefs.Clear;
    if not Assigned(Database) then DatabaseError(SErrDatabasenAssigned);
    TSQLConnection(Database).AddFieldDefs(fcursor,FieldDefs);
  finally
    FLoadingFieldDefs := False;
    if Assigned(FCursor) then FCursor.FInitFieldDef := false;
  end;
end;

function TCustomSQLQuery.SQLParser(const ASQL : string) : TStatementType;

type TParsePart = (ppStart,ppWith,ppSelect,ppFrom,ppWhere,ppGroup,ppOrder,ppComment,ppBogus);

Var
  PSQL,CurrentP,
  PhraseP, PStatementPart : pchar;
  S                       : string;
  ParsePart               : TParsePart;
  StrLength               : Integer;
  EndOfComment            : Boolean;
  BracketCount            : Integer;
  ConnOptions             : TConnOptions;
  FFromPart               : String;

begin
  PSQL:=Pchar(ASQL);
  ParsePart := ppStart;

  CurrentP := PSQL-1;
  PhraseP := PSQL;

  FWhereStartPos := 0;
  FWhereStopPos := 0;

  ConnOptions := TSQLConnection(DataBase).ConnOptions;
  FUpdateable := False;

  repeat
    begin
    inc(CurrentP);

    EndOfComment := SkipComments(CurrentP, sqEscapeSlash in ConnOptions, sqEscapeRepeat in ConnOptions);
    if EndOfcomment then dec(CurrentP);
    if EndOfComment and (ParsePart = ppStart) then PhraseP := CurrentP;

    // skip everything between bracket, since it could be a sub-select, and
    // further nothing between brackets could be interesting for the parser.
    if CurrentP^='(' then
      begin
      inc(currentp);
      BracketCount := 0;
      while (currentp^ <> #0) and ((currentp^ <> ')') or (BracketCount > 0 )) do
        begin
        if currentp^ = '(' then inc(bracketcount)
        else if currentp^ = ')' then dec(bracketcount);
        inc(currentp);
        end;
      EndOfComment := True;
      end;

    if EndOfComment or (CurrentP^ in [' ',#13,#10,#9,#0,';']) then
      begin
      if (CurrentP-PhraseP > 0) or (CurrentP^ in [';',#0]) then
        begin
        strLength := CurrentP-PhraseP;
        Setlength(S,strLength);
        if strLength > 0 then Move(PhraseP^,S[1],(strLength));
        s := uppercase(s);

        case ParsePart of
          ppStart  : begin
                     Result := TSQLConnection(Database).StrToStatementType(s);
                     case s of
                       'WITH'  : ParsePart := ppWith;
                       'SELECT': ParsePart := ppSelect;
                       else      break;
                     end;
                     if not FParseSQL then break;
                     PStatementPart := CurrentP;
                     end;
          ppWith   : begin
                     // WITH [RECURSIVE] CTE_name [ ( column_names ) ] AS ( CTE_query_definition ) [, ...]
                     //  { SELECT | INSERT | UPDATE | DELETE } ...
                     case s of
                       'SELECT': Result := stSelect;
                       'INSERT': Result := stInsert;
                       'UPDATE': Result := stUpdate;
                       'DELETE': Result := stDelete;
                     end;
                     if Result <> stUnknown then break;
                     end;
          ppSelect : begin
                     if s = 'FROM' then
                       begin
                       ParsePart := ppFrom;
                       PhraseP := CurrentP;
                       PStatementPart := CurrentP;
                       end;
                     end;
          ppFrom   : begin
                     if (s = 'WHERE') or (s = 'ORDER') or (s = 'GROUP') or (s = 'LIMIT') or (CurrentP^=#0) or (CurrentP^=';') then
                       begin
                       if (s = 'WHERE') then
                         begin
                         ParsePart := ppWhere;
                         StrLength := PhraseP-PStatementPart;
                         end
                       else if (s = 'GROUP') then
                         begin
                         ParsePart := ppGroup;
                         StrLength := PhraseP-PStatementPart;
                         end
                       else if (s = 'ORDER') then
                         begin
                         ParsePart := ppOrder;
                         StrLength := PhraseP-PStatementPart
                         end
                       else if (s = 'LIMIT') then
                         begin
                         ParsePart := ppBogus;
                         StrLength := PhraseP-PStatementPart
                         end
                       else
                         begin
                         ParsePart := ppBogus;
                         StrLength := CurrentP-PStatementPart;
                         end;
                       if Result = stSelect then
                         begin
                         Setlength(FFromPart,StrLength);
                         Move(PStatementPart^,FFromPart[1],(StrLength));
                         FFromPart := trim(FFromPart);

                         // Meta-data requests and are never updateable select-statements
                         // from more then one table are not updateable
                         if (FSchemaType=stNoSchema) and
                            (ExtractStrings([',',' '],[],pchar(FFromPart),nil) = 1) then
                           begin
                           FUpdateable := True;
                           FTableName := FFromPart;
                           end;
                         end;

                       FWhereStartPos := PStatementPart-PSQL+StrLength+1;
                       PStatementPart := CurrentP;
                       end;
                     end;
          ppWhere  : begin
                     if (s = 'ORDER') or (s = 'GROUP') or (s = 'LIMIT') or (CurrentP^=#0) or (CurrentP^=';') then
                       begin
                       ParsePart := ppBogus;
                       FWhereStartPos := PStatementPart-PSQL;
                       if (s = 'ORDER') or (s = 'GROUP') or (s = 'LIMIT') then
                         FWhereStopPos := PhraseP-PSQL+1
                       else
                         FWhereStopPos := CurrentP-PSQL+1;
                       end
                     else if (s = 'UNION') then
                       begin
                       ParsePart := ppBogus;
                       FUpdateable := False;
                       end;
                     end;
        end; {case}
        end;
      PhraseP := CurrentP+1;
      end
    end;
  until CurrentP^=#0;
end;

procedure TCustomSQLQuery.InternalOpen;

var tel, fieldc : integer;
    f           : TField;
    s           : string;
    IndexFields : TStrings;
    ReadFromFile: Boolean;
begin
  ReadFromFile:=IsReadFromPacket;
  if ReadFromFile then
    begin
    if not assigned(fcursor) then
      FCursor := TSQLConnection(Database).AllocateCursorHandle;
    FCursor.FStatementType:=stSelect;
    FUpdateable:=True;
    end
  else
    Prepare;
  if FCursor.FStatementType in [stSelect,stExecProcedure] then
    begin
    if not ReadFromFile then
      begin
      // Call UpdateServerIndexDefs before Execute, to avoid problems with connections
      // which do not allow processing multiple recordsets at a time. (Microsoft
      // calls this MARS, see bug 13241)
      if DefaultFields and FUpdateable and FusePrimaryKeyAsKey and (not IsUniDirectional) then
        UpdateServerIndexDefs;
      Execute;
      // InternalInitFieldDef is only called after a prepare. i.e. not twice if
      // a dataset is opened - closed - opened.
      if FCursor.FInitFieldDef then InternalInitFieldDefs;
      if DefaultFields then
        begin
        CreateFields;

        if FUpdateable and (not IsUniDirectional) then
          begin
          if FusePrimaryKeyAsKey then
            begin
            for tel := 0 to ServerIndexDefs.count-1 do
              begin
              if ixPrimary in ServerIndexDefs[tel].options then
                begin
                  IndexFields := TStringList.Create;
                  ExtractStrings([';'],[' '],pchar(ServerIndexDefs[tel].fields),IndexFields);
                  for fieldc := 0 to IndexFields.Count-1 do
                    begin
                    F := Findfield(IndexFields[fieldc]);
                    if F <> nil then
                      F.ProviderFlags := F.ProviderFlags + [pfInKey];
                    end;
                  IndexFields.Free;
                end;
              end;
            end;
          end;
        end
      else
        BindFields(True);
      end
    else
      BindFields(True);
    if not ReadOnly and not FUpdateable and (FSchemaType=stNoSchema) then
      begin
      if (trim(FDeleteSQL.Text) <> '') or (trim(FUpdateSQL.Text) <> '') or
         (trim(FInsertSQL.Text) <> '') then FUpdateable := True;
      end
    end
  else
    DatabaseError(SErrNoSelectStatement,Self);
  inherited InternalOpen;
end;

// public part

procedure TCustomSQLQuery.ExecSQL;
begin
  try
    Prepare;
    Execute;
  finally
    // FCursor has to be assigned, or else the prepare went wrong before PrepareStatment was
    // called, so UnPrepareStatement shoudn't be called either
    if (not IsPrepared) and (assigned(database)) and (assigned(FCursor)) then TSQLConnection(database).UnPrepareStatement(Fcursor);
  end;
end;

constructor TCustomSQLQuery.Create(AOwner : TComponent);
begin
  inherited Create(AOwner);
  FParams := TParams.create(self);
  FSQL := TStringList.Create;
  FSQL.OnChange := @OnChangeSQL;

  FUpdateSQL := TStringList.Create;
  FUpdateSQL.OnChange := @OnChangeModifySQL;
  FInsertSQL := TStringList.Create;
  FInsertSQL.OnChange := @OnChangeModifySQL;
  FDeleteSQL := TStringList.Create;
  FDeleteSQL.OnChange := @OnChangeModifySQL;

  FServerIndexDefs := TServerIndexDefs.Create(Self);

  FParseSQL := True;

  FServerFiltered := False;
  FServerFilterText := '';

  FSchemaType:=stNoSchema;
  FSchemaObjectName:='';
  FSchemaPattern:='';

// Delphi has upWhereAll as default, but since strings and oldvalue's don't work yet
// (variants) set it to upWhereKeyOnly
  FUpdateMode := upWhereKeyOnly;
  FUsePrimaryKeyAsKey := True;
end;

destructor TCustomSQLQuery.Destroy;
begin
  if Active then Close;
  UnPrepare;
  if assigned(FCursor) then TSQLConnection(Database).DeAllocateCursorHandle(FCursor);
  FreeAndNil(FMasterLink);
  FreeAndNil(FParams);
  FreeAndNil(FSQL);
  FreeAndNil(FInsertSQL);
  FreeAndNil(FDeleteSQL);
  FreeAndNil(FUpdateSQL);
  FServerIndexDefs.Free;
  inherited Destroy;
end;

procedure TCustomSQLQuery.SetReadOnly(AValue : Boolean);

begin
  CheckInactive;
  inherited SetReadOnly(AValue);
end;

procedure TCustomSQLQuery.SetParseSQL(AValue : Boolean);

begin
  CheckInactive;
  if not AValue then
    begin
    FServerFiltered := False;
    FParseSQL := False;
    end
  else
    FParseSQL := True;
end;

procedure TCustomSQLQuery.SetSQL(const AValue: TStringlist);
begin
  FSQL.Assign(AValue);
end;

procedure TCustomSQLQuery.SetUpdateSQL(const AValue: TStringlist);
begin
  FUpdateSQL.Assign(AValue);
end;

procedure TCustomSQLQuery.SetUsePrimaryKeyAsKey(AValue : Boolean);

begin
  if not Active then FusePrimaryKeyAsKey := AValue
  else
    begin
    // Just temporary, this should be possible in the future
    DatabaseError(SActiveDataset);
    end;
end;

Procedure TCustomSQLQuery.UpdateServerIndexDefs;

begin
  FServerIndexDefs.Clear;
  if assigned(DataBase) and (FTableName<>'') then
    TSQLConnection(DataBase).UpdateIndexDefs(ServerIndexDefs,FTableName);
end;

Procedure TCustomSQLQuery.ApplyRecUpdate(UpdateKind : TUpdateKind);

var FieldNamesQuoteChars : TQuoteChars;

  function InitialiseModifyQuery(var qry : TCustomSQLQuery): TCustomSQLQuery;

  begin
    if not assigned(qry) then
    begin
      qry := TCustomSQLQuery.Create(nil);
      qry.ParseSQL := False;
      qry.DataBase := Self.DataBase;
      qry.Transaction := Self.Transaction;
    end;
    Result:=qry;
  end;

  procedure UpdateWherePart(var sql_where : string;x : integer);

  begin
    if (pfInKey in Fields[x].ProviderFlags) or
       ((FUpdateMode = upWhereAll) and (pfInWhere in Fields[x].ProviderFlags)) or
       ((FUpdateMode = UpWhereChanged) and (pfInWhere in Fields[x].ProviderFlags) and (Fields[x].Value <> Fields[x].OldValue)) then
       if Fields[x].OldValue = NULL then
          sql_where := sql_where + FieldNamesQuoteChars[0] + Fields[x].FieldName + FieldNamesQuoteChars[1] + ' is null and '
       else
          sql_where := sql_where + '(' + FieldNamesQuoteChars[0] + Fields[x].FieldName + FieldNamesQuoteChars[1] + '= :"' + 'OLD_' + Fields[x].FieldName + '") and ';
  end;

  function ModifyRecQuery : string;

  var x          : integer;
      sql_set    : string;
      sql_where  : string;

  begin
    sql_set := '';
    sql_where := '';
    for x := 0 to Fields.Count -1 do
      begin
      UpdateWherePart(sql_where,x);

      if (pfInUpdate in Fields[x].ProviderFlags) then
        sql_set := sql_set +FieldNamesQuoteChars[0] + fields[x].FieldName + FieldNamesQuoteChars[1] +'=:"' + fields[x].FieldName + '",';
      end;

    if length(sql_set) = 0 then DatabaseErrorFmt(sNoUpdateFields,['update'],self);
    setlength(sql_set,length(sql_set)-1);
    if length(sql_where) = 0 then DatabaseErrorFmt(sNoWhereFields,['update'],self);
    setlength(sql_where,length(sql_where)-5);
    result := 'update ' + FTableName + ' set ' + sql_set + ' where ' + sql_where;

  end;

  function InsertRecQuery : string;

  var x          : integer;
      sql_fields : string;
      sql_values : string;

  begin
    sql_fields := '';
    sql_values := '';
    for x := 0 to Fields.Count -1 do
      begin
      if (not fields[x].IsNull) and (pfInUpdate in Fields[x].ProviderFlags) then
        begin
        sql_fields := sql_fields + FieldNamesQuoteChars[0] + fields[x].FieldName + FieldNamesQuoteChars[1] + ',';
        sql_values := sql_values + ':"' + fields[x].FieldName + '",';
        end;
      end;
    if length(sql_fields) = 0 then DatabaseErrorFmt(sNoUpdateFields,['insert'],self);
    setlength(sql_fields,length(sql_fields)-1);
    setlength(sql_values,length(sql_values)-1);

    result := 'insert into ' + FTableName + ' (' + sql_fields + ') values (' + sql_values + ')';
  end;

  function DeleteRecQuery : string;

  var x          : integer;
      sql_where  : string;

  begin
    sql_where := '';
    for x := 0 to Fields.Count -1 do
      UpdateWherePart(sql_where,x);

    if length(sql_where) = 0 then DatabaseErrorFmt(sNoWhereFields,['delete'],self);
    setlength(sql_where,length(sql_where)-5);

    result := 'delete from ' + FTableName + ' where ' + sql_where;
  end;

var qry : TCustomSQLQuery;
    s   : string;
    x   : integer;
    Fld : TField;

begin
  FieldNamesQuoteChars := TSQLConnection(DataBase).FieldNameQuoteChars;

  case UpdateKind of
    ukInsert : begin
               s := trim(FInsertSQL.Text);
               if s = '' then s := InsertRecQuery;
               qry := InitialiseModifyQuery(FInsertQry);
               end;
    ukModify : begin
               s := trim(FUpdateSQL.Text);
               if (s='') and (not assigned(FUpdateQry) or (UpdateMode<>upWhereKeyOnly)) then //first time or dynamic where part
                 s := ModifyRecQuery;
               qry := InitialiseModifyQuery(FUpdateQry);
               end;
    ukDelete : begin
               s := trim(FDeleteSQL.Text);
               if (s='') and (not assigned(FDeleteQry) or (UpdateMode<>upWhereKeyOnly)) then
                 s := DeleteRecQuery;
               qry := InitialiseModifyQuery(FDeleteQry);
               end;
  end;
  if (qry.SQL.Text<>s) and (s<>'') then qry.SQL.Text:=s; //assign only when changed, to avoid UnPrepare/Prepare
  assert(qry.sql.Text<>'');
  with qry do
    begin
    for x := 0 to Params.Count-1 do with params[x] do if sametext(leftstr(name,4),'OLD_') then
      begin
      Fld := self.FieldByName(copy(name,5,length(name)-4));
      AssignFieldValue(Fld,Fld.OldValue);
      end
    else
      begin
      Fld := self.FieldByName(name);
      AssignFieldValue(Fld,Fld.Value);
      end;
    execsql;
    end;
end;


Function TCustomSQLQuery.GetCanModify: Boolean;

begin
  // the test for assigned(FCursor) is needed for the case that the dataset isn't opened
  if assigned(FCursor) and (FCursor.FStatementType = stSelect) then
    Result:= FUpdateable and (not ReadOnly) and (not IsUniDirectional)
  else
    Result := False;
end;

procedure TCustomSQLQuery.SetUpdateMode(AValue : TUpdateMode);

begin
  FUpdateMode := AValue;
end;

procedure TCustomSQLQuery.SetSchemaInfo( ASchemaType : TSchemaType; ASchemaObjectName, ASchemaPattern : string);

begin
  FSchemaType:=ASchemaType;
  FSchemaObjectName:=ASchemaObjectName;
  FSchemaPattern:=ASchemaPattern;
end;

procedure TCustomSQLQuery.LoadBlobIntoBuffer(FieldDef: TFieldDef;
  ABlobBuf: PBufBlobField);
begin
  TSQLConnection(DataBase).LoadBlobIntoBuffer(FieldDef, ABlobBuf, FCursor,(Transaction as tsqltransaction));
end;

procedure TCustomSQLQuery.BeforeRefreshOpenCursor;
begin
  // This is only necessary because TIBConnection can not re-open a
  // prepared cursor. In fact this is wrong, but has never led to
  // problems because in SetActive(false) queries are always
  // unprepared. (which is also wrong, but has to be fixed later)
  if IsPrepared then with TSQLConnection(DataBase) do
    UnPrepareStatement(FCursor);
end;

function TCustomSQLQuery.LogEvent(EventType: TDBEventType): Boolean;
begin
  Result:=Assigned(Database) and TSQLConnection(Database).LogEvent(EventType);
end;

procedure TCustomSQLQuery.Log(EventType: TDBEventType; const Msg: String);

Var
  M : String;

begin
  If LogEvent(EventType) then
    begin
    M:=Msg;
    If (Name<>'') then
      M:=Name+' : '+M;
    TSQLConnection(Database).Log(EventType,M);
    end;
end;

function TCustomSQLQuery.GetStatementType : TStatementType;

begin
  if assigned(FCursor) then
    Result := FCursor.FStatementType
  else
    Result := stUnknown;
end;

procedure TCustomSQLQuery.SetDeleteSQL(const AValue: TStringlist);
begin
  FDeleteSQL.Assign(AValue);
end;

procedure TCustomSQLQuery.SetInsertSQL(const AValue: TStringlist);
begin
  FInsertSQL.Assign(AValue);
end;

Procedure TCustomSQLQuery.SetDataSource(AVAlue : TDatasource);

Var
  DS : TDatasource;

begin
  DS:=DataSource;
  If (AValue<>DS) then
    begin
    If Assigned(AValue) and (AValue.Dataset=Self) then
      DatabaseError(SErrCircularDataSourceReferenceNotAllowed,Self);
    If Assigned(DS) then
      DS.RemoveFreeNotification(Self);
    If Assigned(AValue) then
      begin
      AValue.FreeNotification(Self);
      If (FMasterLink=Nil) then
        FMasterLink:=TMasterParamsDataLink.Create(Self);
      FMasterLink.Datasource:=AValue;
      end
    else
      FreeAndNil(FMasterLink);
    end;
end;

Function TCustomSQLQuery.GetDataSource : TDatasource;

begin
  If Assigned(FMasterLink) then
    Result:=FMasterLink.DataSource
  else
    Result:=Nil;
end;

procedure TCustomSQLQuery.Notification(AComponent: TComponent; Operation: TOperation);

begin
  Inherited;
  If (Operation=opRemove) and (AComponent=DataSource) then
    DataSource:=Nil;
end;

{ TSQLScript }

procedure TSQLScript.ExecuteStatement(SQLStatement: TStrings;
  var StopExecution: Boolean);
begin
  fquery.SQL.assign(SQLStatement);
  fquery.ExecSQL;
end;

procedure TSQLScript.ExecuteDirective(Directive, Argument: String;
  var StopExecution: Boolean);
begin
  if assigned (FOnDirective) then
    FOnDirective (Self, Directive, Argument, StopExecution);
end;

procedure TSQLScript.ExecuteCommit;
begin
  if FTransaction is TSQLTransaction then
    TSQLTransaction(FTransaction).CommitRetaining
  else
    begin
    FTransaction.Active := false;
    FTransaction.Active := true;
    end;
end;

procedure TSQLScript.SetDatabase(Value: TDatabase);
begin
  FDatabase := Value;
end;

procedure TSQLScript.SetTransaction(Value: TDBTransaction);
begin
  FTransaction := Value;
end;

procedure TSQLScript.CheckDatabase;
begin
  If (FDatabase=Nil) then
    DatabaseError(SErrNoDatabaseAvailable,Self)
end;

constructor TSQLScript.Create(AOwner: TComponent);
begin
  inherited Create(AOwner);
  FQuery := TCustomSQLQuery.Create(nil);
end;

destructor TSQLScript.Destroy;
begin
  FQuery.Free;
  inherited Destroy;
end;

procedure TSQLScript.Execute;
begin
  FQuery.DataBase := FDatabase;
  FQuery.Transaction := FTransaction;
  inherited Execute;
end;

procedure TSQLScript.ExecuteScript;
begin
  Execute;
end;


{ Connection definitions }

Var
  ConnDefs : TStringList;

Procedure CheckDefs;

begin
  If (ConnDefs=Nil) then
    begin
    ConnDefs:=TStringList.Create;
    ConnDefs.Sorted:=True;
    ConnDefs.Duplicates:=dupError;
    end;
end;

Procedure DoneDefs;

Var
  I : Integer;


begin
  If Assigned(ConnDefs) then
    begin
    For I:=ConnDefs.Count-1 downto 0 do
      begin
      ConnDefs.Objects[i].Free;
      ConnDefs.Delete(I);
      end;
    FreeAndNil(ConnDefs);
    end;
end;


Function GetConnectionDef(ConnectorName : String) : TConnectionDef;

Var
  I : Integer;

begin
  CheckDefs;
  I:=ConnDefs.IndexOf(ConnectorName);
  If (I<>-1) then
    Result:=TConnectionDef(ConnDefs.Objects[i])
  else
    Result:=Nil;
end;

procedure RegisterConnection(Def: TConnectionDefClass);

Var
  I : Integer;

begin
  CheckDefs;
  I:=ConnDefs.IndexOf(Def.TypeName);
  If (I=-1) then
    ConnDefs.AddObject(Def.TypeName,Def.Create)
  else
    begin
    ConnDefs.Objects[I].Free;
    ConnDefs.Objects[I]:=Def.Create;
    end;
end;

procedure UnRegisterConnection(Def: TConnectionDefClass);
begin
  UnRegisterConnection(Def.TypeName);
end;

procedure UnRegisterConnection(ConnectionName: String);

Var
  I : Integer;

begin
  if (ConnDefs<>Nil) then
    begin
    I:=ConnDefs.IndexOf(ConnectionName);
    If (I<>-1) then
      begin
      ConnDefs.Objects[I].Free;
      ConnDefs.Delete(I);
      end;
    end;
end;

procedure GetConnectionList(List: TSTrings);
begin
  CheckDefs;
  List.Text:=ConnDefs.Text;
end;

{ TSQLConnector }

procedure TSQLConnector.SetConnectorType(const AValue: String);
begin
  if FConnectorType<>AValue then
    begin
    CheckDisconnected;
    If Assigned(FProxy) then
      FreeProxy;
    FConnectorType:=AValue;
    end;
end;

procedure TSQLConnector.SetTransaction(Value: TSQLTransaction);
begin
  inherited SetTransaction(Value);
  If Assigned(FProxy) and (FProxy.Transaction<>Value) then
    FProxy.FTransaction:=Value;
end;

procedure TSQLConnector.DoInternalConnect;

Var
  D : TConnectionDef;

begin
  inherited DoInternalConnect;
  CreateProxy;
  FProxy.CharSet:=Self.CharSet;
  FProxy.Role:=Self.Role;
  FProxy.DatabaseName:=Self.DatabaseName;
  FProxy.HostName:=Self.HostName;
  FProxy.UserName:=Self.UserName;
  FProxy.Password:=Self.Password;
  FProxy.FTransaction:=Self.Transaction;
  D:=GetConnectionDef(ConnectorType);
  D.ApplyParams(Params,FProxy);
  FProxy.Connected:=True;
end;

procedure TSQLConnector.DoInternalDisconnect;
begin
  FProxy.Connected:=False;
  inherited DoInternalDisconnect;
end;

procedure TSQLConnector.CheckProxy;
begin
  If (FProxy=Nil) then
    CreateProxy;
end;

procedure TSQLConnector.CreateProxy;

Var
  D : TConnectionDef;

begin
  D:=GetConnectionDef(ConnectorType);
  If (D=Nil) then
    DatabaseErrorFmt(SErrUnknownConnectorType,[ConnectorType],Self);
  FProxy:=D.ConnectionClass.Create(Self);
  FFieldNameQuoteChars := FProxy.FieldNameQuoteChars;
end;

procedure TSQLConnector.FreeProxy;
begin
  FProxy.Connected:=False;
  FreeAndNil(FProxy);
end;

function TSQLConnector.StrToStatementType(s: string): TStatementType;
begin
  CheckProxy;
  Result:=FProxy.StrToStatementType(s);
end;

function TSQLConnector.GetAsSQLText(Field: TField): string;
begin
  CheckProxy;
  Result:=FProxy.GetAsSQLText(Field);
end;

function TSQLConnector.GetAsSQLText(Param: TParam): string;
begin
  CheckProxy;
  Result:=FProxy.GetAsSQLText(Param);
end;

function TSQLConnector.GetHandle: pointer;
begin
  CheckProxy;
  Result:=FProxy.GetHandle;
end;

function TSQLConnector.AllocateCursorHandle: TSQLCursor;
begin
  CheckProxy;
  Result:=FProxy.AllocateCursorHandle;
end;

procedure TSQLConnector.DeAllocateCursorHandle(var cursor: TSQLCursor);
begin
  CheckProxy;
  FProxy.DeAllocateCursorHandle(cursor);
end;

function TSQLConnector.AllocateTransactionHandle: TSQLHandle;
begin
  CheckProxy;
  Result:=FProxy.AllocateTransactionHandle;
end;

procedure TSQLConnector.PrepareStatement(cursor: TSQLCursor;
  ATransaction: TSQLTransaction; buf: string; AParams: TParams);
begin
  CheckProxy;
  FProxy.PrepareStatement(cursor, ATransaction, buf, AParams);
end;

procedure TSQLConnector.Execute(cursor: TSQLCursor;
  atransaction: tSQLtransaction; AParams: TParams);
begin
  CheckProxy;
  FProxy.Execute(cursor, atransaction, AParams);
end;

function TSQLConnector.Fetch(cursor: TSQLCursor): boolean;
begin
  CheckProxy;
  Result:=FProxy.Fetch(cursor);
end;

procedure TSQLConnector.AddFieldDefs(cursor: TSQLCursor; FieldDefs: TfieldDefs
  );
begin
  CheckProxy;
  FProxy.AddFieldDefs(cursor, FieldDefs);
end;

procedure TSQLConnector.UnPrepareStatement(cursor: TSQLCursor);
begin
  CheckProxy;
  FProxy.UnPrepareStatement(cursor);
end;

procedure TSQLConnector.FreeFldBuffers(cursor: TSQLCursor);
begin
  CheckProxy;
  FProxy.FreeFldBuffers(cursor);
end;

function TSQLConnector.LoadField(cursor: TSQLCursor; FieldDef: TfieldDef;
  buffer: pointer; out CreateBlob: boolean): boolean;
begin
  CheckProxy;
  Result:=FProxy.LoadField(cursor, FieldDef, buffer, CreateBlob);
end;

function TSQLConnector.RowsAffected(cursor: TSQLCursor): TRowsCount;
begin
  CheckProxy;
  Result := FProxy.RowsAffected(cursor);
end;

function TSQLConnector.GetTransactionHandle(trans: TSQLHandle): pointer;
begin
  CheckProxy;
  Result:=FProxy.GetTransactionHandle(trans);
end;

function TSQLConnector.Commit(trans: TSQLHandle): boolean;
begin
  CheckProxy;
  Result:=FProxy.Commit(trans);
end;

function TSQLConnector.RollBack(trans: TSQLHandle): boolean;
begin
  CheckProxy;
  Result:=FProxy.RollBack(trans);
end;

function TSQLConnector.StartdbTransaction(trans: TSQLHandle; aParams: string
  ): boolean;
begin
  CheckProxy;
  Result:=FProxy.StartdbTransaction(trans, aParams);
end;

procedure TSQLConnector.CommitRetaining(trans: TSQLHandle);
begin
  CheckProxy;
  FProxy.CommitRetaining(trans);
end;

procedure TSQLConnector.RollBackRetaining(trans: TSQLHandle);
begin
  CheckProxy;
  FProxy.RollBackRetaining(trans);
end;

procedure TSQLConnector.UpdateIndexDefs(IndexDefs: TIndexDefs;
  TableName: string);
begin
  CheckProxy;
  FProxy.UpdateIndexDefs(IndexDefs, TableName);
end;

function TSQLConnector.GetSchemaInfoSQL(SchemaType: TSchemaType;
  SchemaObjectName, SchemaPattern: string): string;
begin
  CheckProxy;
  Result:=FProxy.GetSchemaInfoSQL(SchemaType, SchemaObjectName, SchemaPattern
    );
end;

procedure TSQLConnector.LoadBlobIntoBuffer(FieldDef: TFieldDef;
  ABlobBuf: PBufBlobField; cursor: TSQLCursor; ATransaction: TSQLTransaction);
begin
  CheckProxy;
  FProxy.LoadBlobIntoBuffer(FieldDef, ABlobBuf, cursor, ATransaction);
end;


{ TConnectionDef }


class function TConnectionDef.TypeName: String;
begin
  Result:='';
end;

class function TConnectionDef.ConnectionClass: TSQLConnectionClass;
begin
  Result:=Nil;
end;

class function TConnectionDef.Description: String;
begin
  Result:='';
end;

procedure TConnectionDef.ApplyParams(Params: TStrings;
  AConnection: TSQLConnection);
begin
  AConnection.Params.Assign(Params);
end;

{ TServerIndexDefs }

constructor TServerIndexDefs.create(ADataset: TDataset);
begin
  if not (ADataset is TCustomSQLQuery) then
    DatabaseErrorFmt(SErrNotASQLQuery,[ADataset.Name]);
  inherited create(ADataset);
end;

procedure TServerIndexDefs.Update;
begin
  if (not updated) and assigned(Dataset) then
    begin
    TCustomSQLQuery(Dataset).UpdateServerIndexDefs;
    updated := True;
    end;
end;

Initialization

Finalization
  DoneDefs;
end.
