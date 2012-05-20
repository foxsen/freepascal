unit IBConnection;

{$mode objfpc}{$H+}

{$Define LinkDynamically}

interface

uses
  Classes, SysUtils, sqldb, db, dbconst, bufdataset,
{$IfDef LinkDynamically}
  ibase60dyn;
{$Else}
  ibase60;
{$EndIf}

const
  DEFDIALECT = 3;
  MAXBLOBSEGMENTSIZE = 65535; //Maximum number of bytes that fit in a blob segment.

type

  EIBDatabaseError = class(EDatabaseError)
    public
      GDSErrorCode : Longint;
  end;

  { TIBCursor }

  TIBCursor = Class(TSQLCursor)
    protected
    Status               : array [0..19] of ISC_STATUS;
    Statement            : pointer;
    SQLDA                : PXSQLDA;
    in_SQLDA             : PXSQLDA;
    ParamBinding         : array of integer;
    FieldBinding         : array of integer;
  end;

  TIBTrans = Class(TSQLHandle)
    protected
    TransactionHandle   : pointer;
    TPB                 : string;                // Transaction parameter buffer
    Status              : array [0..19] of ISC_STATUS;
  end;

  { TIBConnection }

  TIBConnection = class (TSQLConnection)
  private
    FSQLDatabaseHandle   : pointer;
    FStatus              : array [0..19] of ISC_STATUS;
    FDialect             : integer;
    FDBDialect           : integer;
    FBLobSegmentSize     : word; //required for backward compatibilty; not used

    procedure ConnectFB;
    function GetDialect: integer;
    procedure AllocSQLDA(var aSQLDA : PXSQLDA;Count : integer);
    procedure TranslateFldType(SQLType, SQLSubType, SQLLen, SQLScale : integer;
      var TrType : TFieldType; var TrLen : word);
    // conversion methods
    procedure GetDateTime(CurrBuff, Buffer : pointer; AType : integer);
    procedure SetDateTime(CurrBuff: pointer; PTime : TDateTime; AType : integer);
    procedure GetFloat(CurrBuff, Buffer : pointer; Size : Byte);
    procedure SetFloat(CurrBuff: pointer; Dbl: Double; Size: integer);
    procedure CheckError(ProcName : string; Status : PISC_STATUS);
    procedure SetParameters(cursor : TSQLCursor; aTransation : TSQLTransaction; AParams : TParams);
    procedure FreeSQLDABuffer(var aSQLDA : PXSQLDA);
    function  IsDialectStored: boolean;
  protected
    procedure DoConnect; override;
    procedure DoInternalConnect; override;
    procedure DoInternalDisconnect; override;
    function GetHandle : pointer; override;

    Function AllocateCursorHandle : TSQLCursor; override;
    Procedure DeAllocateCursorHandle(var cursor : TSQLCursor); override;
    Function AllocateTransactionHandle : TSQLHandle; override;

    procedure PrepareStatement(cursor: TSQLCursor;ATransaction : TSQLTransaction;buf : string; AParams : TParams); override;
    procedure UnPrepareStatement(cursor : TSQLCursor); override;
    procedure FreeFldBuffers(cursor : TSQLCursor); override;
    procedure Execute(cursor: TSQLCursor;atransaction:tSQLtransaction; AParams : TParams); override;
    procedure AddFieldDefs(cursor: TSQLCursor;FieldDefs : TfieldDefs); override;
    function Fetch(cursor : TSQLCursor) : boolean; override;
    function LoadField(cursor : TSQLCursor;FieldDef : TfieldDef;buffer : pointer; out CreateBlob : boolean) : boolean; override;
    function GetBlobSize(blobHandle : TIsc_Blob_Handle) : LongInt;
    function GetTransactionHandle(trans : TSQLHandle): pointer; override;
    function Commit(trans : TSQLHandle) : boolean; override;
    function RollBack(trans : TSQLHandle) : boolean; override;
    function StartdbTransaction(trans : TSQLHandle; AParams : string) : boolean; override;
    procedure CommitRetaining(trans : TSQLHandle); override;
    procedure RollBackRetaining(trans : TSQLHandle); override;
    procedure UpdateIndexDefs(IndexDefs : TIndexDefs;TableName : string); override;
    function GetSchemaInfoSQL(SchemaType : TSchemaType; SchemaObjectName, SchemaPattern : string) : string; override;
    procedure LoadBlobIntoBuffer(FieldDef: TFieldDef;ABlobBuf: PBufBlobField; cursor: TSQLCursor; ATransaction : TSQLTransaction); override;
    function RowsAffected(cursor: TSQLCursor): TRowsCount; override;
  public
    constructor Create(AOwner : TComponent); override;
    procedure CreateDB; override;
    procedure DropDB; override;
    //Segment size is not used in the code; property kept for backward compatibility
    property BlobSegmentSize : word read FBlobSegmentSize write FBlobSegmentSize; deprecated;
    function GetDBDialect: integer;
  published
    property DatabaseName;
    property Dialect : integer read GetDialect write FDialect stored IsDialectStored default DEFDIALECT;
    property KeepConnection;
    property LoginPrompt;
    property Params;
    property OnLogin;
  end;
  
  { TIBConnectionDef }
  
  TIBConnectionDef = Class(TConnectionDef)
    Class Function TypeName : String; override;
    Class Function ConnectionClass : TSQLConnectionClass; override;
    Class Function Description : String; override;
  end;
                  
implementation

uses
  strutils, FmtBCD;

type
  TTm = packed record
    tm_sec : longint;
    tm_min : longint;
    tm_hour : longint;
    tm_mday : longint;
    tm_mon : longint;
    tm_year : longint;
    tm_wday : longint;
    tm_yday : longint;
    tm_isdst : longint;
    __tm_gmtoff : longint;
    __tm_zone : Pchar;
  end;

procedure TIBConnection.CheckError(ProcName : string; Status : PISC_STATUS);
var
  buf : array [0..1023] of char;
  Msg : string;
  E   : EIBDatabaseError;
  Err : longint;
  
begin
  if ((Status[0] = 1) and (Status[1] <> 0)) then
  begin
    Err := Status[1];
    msg := '';
    while isc_interprete(Buf, @Status) > 0 do
      Msg := Msg + LineEnding +' -' + StrPas(Buf);
    E := EIBDatabaseError.CreateFmt('%s : %s : %s',[self.Name,ProcName,Msg]);
    E.GDSErrorCode := Err;
    Raise E;
  end;
end;


constructor TIBConnection.Create(AOwner : TComponent);

begin
  inherited;
  FConnOptions := FConnOptions + [sqSupportParams] + [sqEscapeRepeat];
  FBLobSegmentSize := 65535; //Shows we're using the maximum segment size
  FDialect := -1;
  FDBDialect := -1;
end;


function TIBConnection.GetTransactionHandle(trans : TSQLHandle): pointer;
begin
  Result := (trans as TIBtrans).TransactionHandle;
end;

function TIBConnection.Commit(trans : TSQLHandle) : boolean;
begin
  result := false;
  with (trans as TIBTrans) do
    if isc_commit_transaction(@Status[0], @TransactionHandle) <> 0 then
      CheckError('Commit', Status)
    else result := true;
end;

function TIBConnection.RollBack(trans : TSQLHandle) : boolean;
begin
  result := false;
  if isc_rollback_transaction(@TIBTrans(trans).Status[0], @TIBTrans(trans).TransactionHandle) <> 0 then
    CheckError('Rollback', TIBTrans(trans).Status)
  else result := true;
end;

function TIBConnection.StartDBTransaction(trans : TSQLHandle;AParams : String) : boolean;
var
  DBHandle : pointer;
  tr       : TIBTrans;
  i        : integer;
  s        : string;
begin
  result := false;

  DBHandle := GetHandle;
  tr := trans as TIBtrans;
  with tr do
    begin
    TPB := chr(isc_tpb_version3);

    i := 1;
    s := ExtractSubStr(AParams,i,stdWordDelims);
    while s <> '' do
      begin
      if s='isc_tpb_write' then TPB := TPB + chr(isc_tpb_write)
      else if s='isc_tpb_read' then TPB := TPB + chr(isc_tpb_read)
      else if s='isc_tpb_consistency' then TPB := TPB + chr(isc_tpb_consistency)
      else if s='isc_tpb_concurrency' then TPB := TPB + chr(isc_tpb_concurrency)
      else if s='isc_tpb_read_committed' then TPB := TPB + chr(isc_tpb_read_committed)
      else if s='isc_tpb_rec_version' then TPB := TPB + chr(isc_tpb_rec_version)
      else if s='isc_tpb_no_rec_version' then TPB := TPB + chr(isc_tpb_no_rec_version)
      else if s='isc_tpb_wait' then TPB := TPB + chr(isc_tpb_wait)
      else if s='isc_tpb_nowait' then TPB := TPB + chr(isc_tpb_nowait)
      else if s='isc_tpb_shared' then TPB := TPB + chr(isc_tpb_shared)
      else if s='isc_tpb_protected' then TPB := TPB + chr(isc_tpb_protected)
      else if s='isc_tpb_exclusive' then TPB := TPB + chr(isc_tpb_exclusive)
      else if s='isc_tpb_lock_read' then TPB := TPB + chr(isc_tpb_lock_read)
      else if s='isc_tpb_lock_write' then TPB := TPB + chr(isc_tpb_lock_write)
      else if s='isc_tpb_verb_time' then TPB := TPB + chr(isc_tpb_verb_time)
      else if s='isc_tpb_commit_time' then TPB := TPB + chr(isc_tpb_commit_time)
      else if s='isc_tpb_ignore_limbo' then TPB := TPB + chr(isc_tpb_ignore_limbo)
      else if s='isc_tpb_autocommit' then TPB := TPB + chr(isc_tpb_autocommit)
      else if s='isc_tpb_restart_requests' then TPB := TPB + chr(isc_tpb_restart_requests)
      else if s='isc_tpb_no_auto_undo' then TPB := TPB + chr(isc_tpb_no_auto_undo);
      s := ExtractSubStr(AParams,i,stdWordDelims);

      end;

    TransactionHandle := nil;

    if isc_start_transaction(@Status[0], @TransactionHandle, 1,
       [@DBHandle, Length(TPB), @TPB[1]]) <> 0 then
      CheckError('StartTransaction',Status)
    else Result := True;
    end;
end;


procedure TIBConnection.CommitRetaining(trans : TSQLHandle);
begin
  with trans as TIBtrans do
    if isc_commit_retaining(@Status[0], @TransactionHandle) <> 0 then
      CheckError('CommitRetaining', Status);
end;

procedure TIBConnection.RollBackRetaining(trans : TSQLHandle);
begin
  with trans as TIBtrans do
    if isc_rollback_retaining(@Status[0], @TransactionHandle) <> 0 then
      CheckError('RollBackRetaining', Status);
end;
procedure TIBConnection.DropDB;

begin
  CheckDisConnected;

{$IfDef LinkDynamically}
  InitialiseIBase60;
{$EndIf}

  ConnectFB;

  if isc_drop_database(@FStatus[0], @FSQLDatabaseHandle) <> 0 then
    CheckError('DropDB', FStatus);

{$IfDef LinkDynamically}
  ReleaseIBase60;
{$EndIf}
end;

procedure TIBConnection.CreateDB;

var ASQLDatabaseHandle,
    ASQLTransactionHandle : pointer;
    CreateSQL : String;
    pagesize : String;
begin
  CheckDisConnected;
{$IfDef LinkDynamically}
  InitialiseIBase60;
{$EndIf}
  ASQLDatabaseHandle := nil;
  ASQLTransactionHandle := nil;

  CreateSQL := 'CREATE DATABASE ';
  if HostName <> '' then CreateSQL := CreateSQL + ''''+ HostName+':'+DatabaseName + ''''
    else CreateSQL := CreateSQL + '''' + DatabaseName + '''';
  if UserName <> '' then
    CreateSQL := CreateSQL + ' USER ''' + Username + '''';
  if Password <> '' then
    CreateSQL := CreateSQL + ' PASSWORD ''' + Password + '''';
  pagesize := params.Values['PAGE_SIZE'];
  if pagesize <> '' then
    CreateSQL := CreateSQL + ' PAGE_SIZE '+pagesize;
  if CharSet <> '' then
    CreateSQL := CreateSQL + ' DEFAULT CHARACTER SET ' + CharSet;

  if isc_dsql_execute_immediate(@FStatus[0],@ASQLDatabaseHandle,@ASQLTransactionHandle,length(CreateSQL),@CreateSQL[1],Dialect,nil) <> 0 then
    CheckError('CreateDB', FStatus);

  if isc_detach_database(@FStatus[0], @ASQLDatabaseHandle) <> 0 then
    CheckError('CreateDB', FStatus);
{$IfDef LinkDynamically}
  ReleaseIBase60;
{$EndIf}
end;

procedure TIBConnection.DoInternalConnect;

begin
{$IfDef LinkDynamically}
  InitialiseIBase60;
{$EndIf}
  inherited dointernalconnect;

  ConnectFB;
end;

procedure TIBConnection.DoInternalDisconnect;
begin
  FDialect := -1;
  FDBDialect := -1;
  if not Connected then
  begin
    FSQLDatabaseHandle := nil;
    Exit;
  end;

  if isc_detach_database(@FStatus[0], @FSQLDatabaseHandle) <> 0 then
    CheckError('Close', FStatus);
{$IfDef LinkDynamically}
  ReleaseIBase60;
{$EndIf}
end;


function TIBConnection.GetDBDialect: integer;
var
  x : integer;
  Len : integer;
  Buffer : array [0..1] of byte;
  ResBuf : array [0..39] of byte;
begin
  result := -1;
  if Connected then
    begin
    Buffer[0] := isc_info_db_sql_dialect;
    Buffer[1] := isc_info_end;
    if isc_database_info(@FStatus[0], @FSQLDatabaseHandle, Length(Buffer),
      pchar(@Buffer[0]), SizeOf(ResBuf), pchar(@ResBuf[0])) <> 0 then
        CheckError('SetDBDialect', FStatus);
    x := 0;
    while x < 40 do
      case ResBuf[x] of
        isc_info_db_sql_dialect :
          begin
          Inc(x);
          Len := isc_vax_integer(pchar(@ResBuf[x]), 2);
          Inc(x, 2);
          Result := isc_vax_integer(pchar(@ResBuf[x]), Len);
          Inc(x, Len);
          end;
        isc_info_end : Break;
      else
        inc(x);
      end;
    end;
end;

procedure TIBConnection.ConnectFB;
var
  ADatabaseName: String;
  DPB: string;
begin
  DPB := chr(isc_dpb_version1);
  if (UserName <> '') then
  begin
    DPB := DPB + chr(isc_dpb_user_name) + chr(Length(UserName)) + UserName;
    if (Password <> '') then
      DPB := DPB + chr(isc_dpb_password) + chr(Length(Password)) + Password;
  end;
  if (Role <> '') then
     DPB := DPB + chr(isc_dpb_sql_role_name) + chr(Length(Role)) + Role;
  if Length(CharSet) > 0 then
    DPB := DPB + Chr(isc_dpb_lc_ctype) + Chr(Length(CharSet)) + CharSet;

  FSQLDatabaseHandle := nil;
  if HostName <> '' then ADatabaseName := HostName+':'+DatabaseName
    else ADatabaseName := DatabaseName;
  if isc_attach_database(@FStatus[0], Length(ADatabaseName), @ADatabaseName[1],
    @FSQLDatabaseHandle,
         Length(DPB), @DPB[1]) <> 0 then
    CheckError('DoInternalConnect', FStatus);
end;

function TIBConnection.GetDialect: integer;
begin
  if FDialect = -1 then
  begin
    if FDBDialect = -1 then
      Result := DEFDIALECT
    else
      Result := FDBDialect;
  end else
    Result := FDialect;
end;

procedure TIBConnection.AllocSQLDA(var aSQLDA : PXSQLDA;Count : integer);

begin
  FreeSQLDABuffer(aSQLDA);

  if count > -1 then
    begin
    reAllocMem(aSQLDA, XSQLDA_Length(Count));
    { Zero out the memory block to avoid problems with exceptions within the
      constructor of this class. }
    FillChar(aSQLDA^, XSQLDA_Length(Count), 0);

    aSQLDA^.Version := sqlda_version1;
    aSQLDA^.SQLN := Count;
    end
  else
    reAllocMem(aSQLDA,0);
end;

procedure TIBConnection.TranslateFldType(SQLType, SQLSubType, SQLLen, SQLScale : integer;
           var TrType : TFieldType; var TrLen : word);
begin
  TrLen := 0;
  if SQLScale < 0 then
    begin
    TrLen := abs(SQLScale);
    if (TrLen <= MaxBCDScale) then //Note: NUMERIC(18,3) or (17,2) must be mapped to ftFmtBCD, but we do not know Precision
      TrType := ftBCD
    else
      TrType := ftFMTBcd;
    end
  else case (SQLType and not 1) of
    SQL_VARYING :
      begin
        TrType := ftString;
        TrLen := SQLLen;
      end;
    SQL_TEXT :
      begin
        TrType := ftFixedChar;
        TrLen := SQLLen;
      end;
    SQL_TYPE_DATE :
      TrType := ftDate;
    SQL_TYPE_TIME :
        TrType := ftTime;
    SQL_TIMESTAMP :
        TrType := ftDateTime;
    SQL_ARRAY :
      begin
        TrType := ftArray;
        TrLen := SQLLen;
      end;
    SQL_BLOB :
      begin
        if SQLSubType = 1 then
           TrType := ftMemo
        else
           TrType := ftBlob;
        TrLen := SQLLen;
      end;
    SQL_SHORT :
        TrType := ftSmallint;
    SQL_LONG :
        TrType := ftInteger;
    SQL_INT64 :
        TrType := ftLargeInt;
    SQL_DOUBLE :
        TrType := ftFloat;
    SQL_FLOAT :
        TrType := ftFloat;
    else
        TrType := ftUnknown;
  end;
end;

Function TIBConnection.AllocateCursorHandle : TSQLCursor;

var curs : TIBCursor;

begin
  curs := TIBCursor.create;
  curs.sqlda := nil;
  curs.statement := nil;
  curs.FPrepared := False;
  AllocSQLDA(curs.SQLDA,0);
  result := curs;
end;

procedure TIBConnection.DeAllocateCursorHandle(var cursor : TSQLCursor);

begin
  if assigned(cursor) then with cursor as TIBCursor do
    begin
    AllocSQLDA(SQLDA,-1);
    AllocSQLDA(in_SQLDA,-1);
    end;
  FreeAndNil(cursor);
end;

Function TIBConnection.AllocateTransactionHandle : TSQLHandle;

begin
  result := TIBTrans.create;
end;

procedure TIBConnection.PrepareStatement(cursor: TSQLCursor;ATransaction : TSQLTransaction;buf : string; AParams : TParams);

var dh    : pointer;
    tr    : pointer;
    x     : Smallint;
    info_request   : string;
    resbuf         : array[0..7] of byte;
    blockSize      : integer;
    IBStatementType: integer;

begin
  with cursor as TIBcursor do
    begin
    dh := GetHandle;
    if isc_dsql_allocate_statement(@Status[0], @dh, @Statement) <> 0 then
      CheckError('PrepareStatement', Status);
    tr := aTransaction.Handle;
    
    if assigned(AParams) and (AParams.count > 0) then
      buf := AParams.ParseSQL(buf,false,sqEscapeSlash in ConnOptions, sqEscapeRepeat in ConnOptions,psInterbase,paramBinding);

    if isc_dsql_prepare(@Status[0], @tr, @Statement, 0, @Buf[1], Dialect, nil) <> 0 then
      CheckError('PrepareStatement', Status);
    if assigned(AParams) and (AParams.count > 0) then
      begin
      AllocSQLDA(in_SQLDA,Length(ParamBinding));
      if isc_dsql_describe_bind(@Status[0], @Statement, 1, in_SQLDA) <> 0 then
        CheckError('PrepareStatement', Status);
      if in_SQLDA^.SQLD > in_SQLDA^.SQLN then
        DatabaseError(SParameterCountIncorrect,self);
      {$push}
      {$R-}
      for x := 0 to in_SQLDA^.SQLD - 1 do with in_SQLDA^.SQLVar[x] do
        begin
        if ((SQLType and not 1) = SQL_VARYING) then
          SQLData := AllocMem(in_SQLDA^.SQLVar[x].SQLLen+2)
        else
          SQLData := AllocMem(in_SQLDA^.SQLVar[x].SQLLen);
        // Always force the creation of slqind for parameters. It could be
        // that a database-trigger takes care of inserting null-values, so
        // it should always be possible to pass null-parameters. If that fails,
        // the database-server will generate the appropiate error.
        sqltype := sqltype or 1;
        new(sqlind);
        end;
      {$pop}
      end
    else
      AllocSQLDA(in_SQLDA,0);

    // Get the statement type from firebird/interbase
    info_request := chr(isc_info_sql_stmt_type);
    if isc_dsql_sql_info(@Status[0],@Statement,Length(info_request), @info_request[1],sizeof(resbuf),@resbuf) <> 0 then
      CheckError('PrepareStatement', Status);
    assert(resbuf[0]=isc_info_sql_stmt_type);
    BlockSize:=isc_vax_integer(@resbuf[1],2);
    IBStatementType:=isc_vax_integer(@resbuf[3],blockSize);
    assert(resbuf[3+blockSize]=isc_info_end);
    // If the statementtype is isc_info_sql_stmt_exec_procedure then
    // override the statement type derrived by parsing the query.
    // This to recognize statements like 'insert into .. returning' correctly
    if IBStatementType = isc_info_sql_stmt_exec_procedure then
      FStatementType := stExecProcedure;

    if FStatementType in [stSelect,stExecProcedure] then
      begin
      if isc_dsql_describe(@Status[0], @Statement, 1, SQLDA) <> 0 then
        CheckError('PrepareSelect', Status);
      if SQLDA^.SQLD > SQLDA^.SQLN then
        begin
        AllocSQLDA(SQLDA,SQLDA^.SQLD);
        if isc_dsql_describe(@Status[0], @Statement, 1, SQLDA) <> 0 then
          CheckError('PrepareSelect', Status);
        end;
      {$push}
      {$R-}
      for x := 0 to SQLDA^.SQLD - 1 do with SQLDA^.SQLVar[x] do
        begin
        if ((SQLType and not 1) = SQL_VARYING) then
          SQLData := AllocMem(SQLDA^.SQLVar[x].SQLLen+2)
        else
          SQLData := AllocMem(SQLDA^.SQLVar[x].SQLLen);
        if (SQLType and 1) = 1 then New(SQLInd);
        end;
      {$pop}
      end;
    FPrepared := True;
    end;
end;

procedure TIBConnection.UnPrepareStatement(cursor : TSQLCursor);

begin
  with cursor as TIBcursor do
    if assigned(Statement) Then
      begin
        if isc_dsql_free_statement(@Status[0], @Statement, DSQL_Drop) <> 0 then
          CheckError('FreeStatement', Status);
        Statement := nil;
        FPrepared := False;
      end;
end;

procedure TIBConnection.FreeSQLDABuffer(var aSQLDA : PXSQLDA);

var x : Smallint;

begin
{$push}
{$R-}
  if assigned(aSQLDA) then
    for x := 0 to aSQLDA^.SQLN - 1 do
      begin
      reAllocMem(aSQLDA^.SQLVar[x].SQLData,0);
      if assigned(aSQLDA^.SQLVar[x].sqlind) then
        begin
        Dispose(aSQLDA^.SQLVar[x].sqlind);
        aSQLDA^.SQLVar[x].sqlind := nil;
        end
        
      end;
{$pop}
end;

function TIBConnection.IsDialectStored: boolean;
begin
  result := (FDialect<>-1);
end;

procedure TIBConnection.DoConnect;
const NoQuotes: TQuoteChars = (' ',' ');
begin
  inherited DoConnect;
  FDBDialect := GetDBDialect;
  if Dialect < 3 then
    FieldNameQuoteChars := NoQuotes
  else
    FieldNameQuoteChars := DoubleQuotes;
end;

procedure TIBConnection.FreeFldBuffers(cursor : TSQLCursor);

begin
  with cursor as TIBCursor do
    begin
    FreeSQLDABuffer(SQLDA);
    FreeSQLDABuffer(in_SQLDA);
    SetLength(FieldBinding,0);
    end;
end;

procedure TIBConnection.Execute(cursor: TSQLCursor;atransaction:tSQLtransaction; AParams : TParams);
var tr : pointer;
    out_SQLDA : PXSQLDA;
begin
  tr := aTransaction.Handle;
  if Assigned(APArams) and (AParams.count > 0) then SetParameters(cursor, atransaction, AParams);
  with cursor as TIBCursor do
  begin
    if FStatementType = stExecProcedure then
      out_SQLDA := SQLDA
    else
      out_SQLDA := nil;
    if isc_dsql_execute2(@Status[0], @tr, @Statement, 1, in_SQLDA, out_SQLDA) <> 0 then
      CheckError('Execute', Status);
  end;
end;


procedure TIBConnection.AddFieldDefs(cursor: TSQLCursor;FieldDefs : TfieldDefs);
var
  x         : integer;
  TransLen  : word;
  TransType : TFieldType;
  FD        : TFieldDef;

begin
  {$push}
  {$R-}
  with cursor as TIBCursor do
    begin
    setlength(FieldBinding,SQLDA^.SQLD);
    for x := 0 to SQLDA^.SQLD - 1 do
      begin
      TranslateFldType(SQLDA^.SQLVar[x].SQLType, SQLDA^.SQLVar[x].sqlsubtype, SQLDA^.SQLVar[x].SQLLen, SQLDA^.SQLVar[x].SQLScale,
        TransType, TransLen);

      FD := TFieldDef.Create(FieldDefs, FieldDefs.MakeNameUnique(SQLDA^.SQLVar[x].AliasName), TransType,
         TransLen, (SQLDA^.SQLVar[x].sqltype and 1)=0, (x + 1));
      if TransType in [ftBCD, ftFmtBCD] then
        case (SQLDA^.SQLVar[x].sqltype and not 1) of
          SQL_SHORT : FD.precision := 4;
          SQL_LONG  : FD.precision := 9;
          SQL_DOUBLE,
          SQL_INT64 : FD.precision := 18;
          else FD.precision := SQLDA^.SQLVar[x].SQLLen;
        end;
//      FD.DisplayName := SQLDA^.SQLVar[x].AliasName;
      FieldBinding[FD.FieldNo-1] := x;
      end;
    end;
  {$pop}
end;

function TIBConnection.GetHandle: pointer;
begin
  Result := FSQLDatabaseHandle;
end;

function TIBConnection.Fetch(cursor : TSQLCursor) : boolean;
var
  retcode : integer;
begin
  with cursor as TIBCursor do
  begin
    if FStatementType = stExecProcedure then
      //it is not recommended fetch from non-select statement, i.e. statement which have no cursor
      //starting from Firebird 2.5 it leads to error 'Invalid cursor reference'
      if SQLDA^.SQLD = 0 then
        retcode := 100 //no more rows to retrieve
      else
      begin
        retcode := 0;
        SQLDA^.SQLD := 0; //hack: mark after first fetch
      end
    else
      retcode := isc_dsql_fetch(@Status[0], @Statement, 1, SQLDA);
    if (retcode <> 0) and (retcode <> 100) then
      CheckError('Fetch', Status);
  end;
  Result := (retcode = 0);
end;

function IntPower10(e: integer): double;
const PreComputedPower10: array[0..9] of integer = (1,10,100,1000,10000,100000,1000000,10000000,100000000,1000000000);
var n: integer;
begin
  n := abs(e); //exponent can't be greater than 18
  if n <= 9 then
    Result := PreComputedPower10[n]
  else
    Result := PreComputedPower10[9] * PreComputedPower10[n-9];
  if e < 0 then
    Result := 1 / Result;
end;

procedure TIBConnection.SetParameters(cursor : TSQLCursor; aTransation : TSQLTransaction; AParams : TParams);

var ParNr,SQLVarNr : integer;
    s               : string;
    i               : integer;
    si              : smallint;
    li              : LargeInt;
    currbuff        : pchar;
    w               : word;

    TransactionHandle : pointer;
    blobId            : ISC_QUAD;
    blobHandle        : Isc_blob_Handle;
    BlobSize,
    BlobBytesWritten  : longint;
    
  procedure SetBlobParam;

  begin
    {$push}
    {$R-}
    with cursor as TIBCursor do
      begin
      TransactionHandle := aTransation.Handle;
      blobhandle := FB_API_NULLHANDLE;
      if isc_create_blob(@FStatus[0], @FSQLDatabaseHandle, @TransactionHandle, @blobHandle, @blobId) <> 0 then
       CheckError('TIBConnection.CreateBlobStream', FStatus);

      s := AParams[ParNr].AsString;
      BlobSize := length(s);

      BlobBytesWritten := 0;
      i := 0;

      // Write in segments of MAXBLOBSEGMENTSIZE, as that is the fastest.
      // We ignore BlobSegmentSize property.
      while BlobBytesWritten < (BlobSize-MAXBLOBSEGMENTSIZE) do
        begin
        isc_put_segment(@FStatus[0], @blobHandle, MAXBLOBSEGMENTSIZE, @s[(i*MAXBLOBSEGMENTSIZE)+1]);
        inc(BlobBytesWritten,MAXBLOBSEGMENTSIZE);
        inc(i);
        end;
      if BlobBytesWritten <> BlobSize then
        isc_put_segment(@FStatus[0], @blobHandle, BlobSize-BlobBytesWritten, @s[(i*MAXBLOBSEGMENTSIZE)+1]);

      if isc_close_blob(@FStatus[0], @blobHandle) <> 0 then
        CheckError('TIBConnection.CreateBlobStream isc_close_blob', FStatus);
      Move(blobId, in_sqlda^.SQLvar[SQLVarNr].SQLData^, in_SQLDA^.SQLVar[SQLVarNr].SQLLen);
      end;
      {$pop}
  end;

var
  // This should be a pointer, because the ORIGINAL variables must
  // be modified.
  VSQLVar: ^XSQLVAR;

begin
  {$push}
  {$R-}
  with cursor as TIBCursor do for SQLVarNr := 0 to High(ParamBinding){AParams.count-1} do
    begin
    ParNr := ParamBinding[SQLVarNr];
    VSQLVar := @in_sqlda^.SQLvar[SQLVarNr];
    if AParams[ParNr].IsNull then
      VSQLVar^.SQLInd^ := -1
    else
      begin
      VSQLVar^.SQLInd^ := 0;

      case (VSQLVar^.sqltype and not 1) of
        SQL_LONG :
          begin
            if VSQLVar^.sqlscale = 0 then
              i := AParams[ParNr].AsInteger
            else
              i := Round(AParams[ParNr].AsCurrency * IntPower10(-VSQLVar^.sqlscale));
            Move(i, VSQLVar^.SQLData^, VSQLVar^.SQLLen);
          end;
        SQL_SHORT :
          begin
            if VSQLVar^.sqlscale = 0 then
              si := AParams[ParNr].AsSmallint
            else
              si := Round(AParams[ParNr].AsCurrency * IntPower10(-VSQLVar^.sqlscale));
            i := si;
            Move(i, VSQLVar^.SQLData^, VSQLVar^.SQLLen);
          end;
        SQL_BLOB :
          SetBlobParam;
        SQL_VARYING, SQL_TEXT :
          begin
          s := AParams[ParNr].AsString;
          w := length(s); // a word is enough, since the max-length of a string in interbase is 32k
          if ((VSQLVar^.SQLType and not 1) = SQL_VARYING) then
            begin
            VSQLVar^.SQLLen := w;
            ReAllocMem(VSQLVar^.SQLData, VSQLVar^.SQLLen+2);
            CurrBuff := VSQLVar^.SQLData;
            move(w,CurrBuff^,sizeof(w));
            inc(CurrBuff,2);
            end
          else
            begin
            // The buffer-length is always VSQLVar^.sqllen, nothing more, nothing less
            // so fill the complete buffer with valid data. Adding #0 will lead
            // to problems, because the #0 will be seen as a part of the (binary) string
            CurrBuff := VSQLVar^.SQLData;
            w := VSQLVar^.sqllen;
            s := PadRight(s,w);
            end;
          Move(s[1], CurrBuff^, w);
          end;
        SQL_TYPE_DATE, SQL_TYPE_TIME, SQL_TIMESTAMP :
          SetDateTime(VSQLVar^.SQLData, AParams[ParNr].AsDateTime, VSQLVar^.SQLType);
        SQL_INT64:
          begin
            if VSQLVar^.sqlscale = 0 then
              li := AParams[ParNr].AsLargeInt
            else if AParams[ParNr].DataType = ftFMTBcd then
              li := AParams[ParNr].AsFMTBCD * IntPower10(-VSQLVar^.sqlscale)
            else
              li := Round(AParams[ParNr].AsCurrency * IntPower10(-VSQLVar^.sqlscale));
            Move(li, VSQLVar^.SQLData^, VSQLVar^.SQLLen);
          end;
        SQL_DOUBLE, SQL_FLOAT:
          SetFloat(VSQLVar^.SQLData, AParams[ParNr].AsFloat, VSQLVar^.SQLLen);
      else
        DatabaseErrorFmt(SUnsupportedParameter,[Fieldtypenames[AParams[ParNr].DataType]],self);
      end {case}
      end;
    end;
{$pop}
end;

function TIBConnection.LoadField(cursor : TSQLCursor;FieldDef : TfieldDef;buffer : pointer; out CreateBlob : boolean) : boolean;

var
  x          : integer;
  VarcharLen : word;
  CurrBuff     : pchar;
  c            : currency;
  AFmtBcd      : tBCD;

  function BcdDivPower10(Dividend: largeint; e: integer): TBCD;
  var d: double;
  begin
    d := Dividend / IntPower10(e);
    Result := StrToBCD( FloatToStr(d) );
  end;

begin
  CreateBlob := False;
  with cursor as TIBCursor do
    begin
    {$push}
    {$R-}
    x := FieldBinding[FieldDef.FieldNo-1];

    // Joost, 5 jan 2006: I disabled the following, since it's useful for
    // debugging, but it also slows things down. In principle things can only go
    // wrong when FieldDefs is changed while the dataset is opened. A user just
    // shoudn't do that. ;) (The same is done in PQConnection)

    // if SQLDA^.SQLVar[x].AliasName <> FieldDef.Name then
    // DatabaseErrorFmt(SFieldNotFound,[FieldDef.Name],self);
    if assigned(SQLDA^.SQLVar[x].SQLInd) and (SQLDA^.SQLVar[x].SQLInd^ = -1) then
      result := false
    else
      begin

      with SQLDA^.SQLVar[x] do
        if ((SQLType and not 1) = SQL_VARYING) then
          begin
          Move(SQLData^, VarcharLen, 2);
          CurrBuff := SQLData + 2;
          end
        else
          begin
          CurrBuff := SQLData;
          VarCharLen := FieldDef.Size;
          end;

      Result := true;
      case FieldDef.DataType of
        ftBCD :
          begin
            case SQLDA^.SQLVar[x].SQLLen of
              2 : c := PSmallint(CurrBuff)^ / IntPower10(-SQLDA^.SQLVar[x].SQLScale);
              4 : c := PLongint(CurrBuff)^  / IntPower10(-SQLDA^.SQLVar[x].SQLScale);
              8 : if Dialect < 3 then
                    c := PDouble(CurrBuff)^
                  else
                    c := PLargeint(CurrBuff)^ / IntPower10(-SQLDA^.SQLVar[x].SQLScale);
              else
                Result := False; // Just to be sure, in principle this will never happen
            end; {case}
            Move(c, buffer^ , sizeof(c));
          end;
        ftFMTBcd :
          begin
            case SQLDA^.SQLVar[x].SQLLen of
              2 : AFmtBcd := BcdDivPower10(PSmallint(CurrBuff)^, -SQLDA^.SQLVar[x].SQLScale);
              4 : AFmtBcd := BcdDivPower10(PLongint(CurrBuff)^,  -SQLDA^.SQLVar[x].SQLScale);
              8 : if Dialect < 3 then
                    AFmtBcd := PDouble(CurrBuff)^
                  else
                    AFmtBcd := BcdDivPower10(PLargeint(CurrBuff)^, -SQLDA^.SQLVar[x].SQLScale);
              else
                Result := False; // Just to be sure, in principle this will never happen
            end; {case}
            Move(AFmtBcd, buffer^ , sizeof(AFmtBcd));
          end;
        ftInteger :
          begin
            FillByte(buffer^,sizeof(Longint),0);
            Move(CurrBuff^, Buffer^, SQLDA^.SQLVar[x].SQLLen);
          end;
        ftLargeint :
          begin
            FillByte(buffer^,sizeof(LargeInt),0);
            Move(CurrBuff^, Buffer^, SQLDA^.SQLVar[x].SQLLen);
          end;
        ftSmallint :
          begin
            FillByte(buffer^,sizeof(Smallint),0);
            Move(CurrBuff^, Buffer^, SQLDA^.SQLVar[x].SQLLen);
          end;
        ftDate, ftTime, ftDateTime:
          GetDateTime(CurrBuff, Buffer, SQLDA^.SQLVar[x].SQLType);
        ftString, ftFixedChar  :
          begin
            Move(CurrBuff^, Buffer^, VarCharLen);
            PChar(Buffer + VarCharLen)^ := #0;
          end;
        ftFloat   :
          GetFloat(CurrBuff, Buffer, SQLDA^.SQLVar[x].SQLLen);
        ftBlob,
        ftMemo :
          begin  // load the BlobIb in field's buffer
            FillByte(buffer^,sizeof(TBufBlobField),0);
            Move(CurrBuff^, Buffer^, SQLDA^.SQLVar[x].SQLLen);
          end;

        else
          begin
            result := false;
            databaseerrorfmt(SUnsupportedFieldType, [Fieldtypenames[FieldDef.DataType], Self]);
          end
      end;  { case }
      end; { if/else }
      {$pop}
    end; { with cursor }
end;

{$DEFINE SUPPORT_MSECS}
{$IFDEF SUPPORT_MSECS}
const
  IBDateOffset = 15018; //an offset from 17 Nov 1858.
  IBSecsCount  = SecsPerDay * 10000; //count of 1/10000 seconds since midnight.
{$ENDIF}

procedure TIBConnection.GetDateTime(CurrBuff, Buffer : pointer; AType : integer);
var
  {$IFNDEF SUPPORT_MSECS}
  CTime : TTm;          // C struct time
  STime : TSystemTime;  // System time
  {$ENDIF}
  PTime : TDateTime;    // Pascal time
begin
  case (AType and not 1) of
    SQL_TYPE_DATE :
      {$IFNDEF SUPPORT_MSECS}
      isc_decode_sql_date(PISC_DATE(CurrBuff), @CTime);
      {$ELSE}
      PTime := PISC_DATE(CurrBuff)^ - IBDateOffset;
      {$ENDIF}
    SQL_TYPE_TIME :
      {$IFNDEF SUPPORT_MSECS}
      isc_decode_sql_time(PISC_TIME(CurrBuff), @CTime);
      {$ELSE}
      PTime :=  PISC_TIME(CurrBuff)^ / IBSecsCount;
      {$ENDIF}
    SQL_TIMESTAMP :
      begin
      {$IFNDEF SUPPORT_MSECS}
      isc_decode_timestamp(PISC_TIMESTAMP(CurrBuff), @CTime);
      {$ELSE}
      PTime := ComposeDateTime(
                  PISC_TIMESTAMP(CurrBuff)^.timestamp_date - IBDateOffset,
                  PISC_TIMESTAMP(CurrBuff)^.timestamp_time / IBSecsCount
               );
      {$ENDIF}
      end
  else
    Raise EIBDatabaseError.CreateFmt('Invalid parameter type for date Decode : %d',[(AType and not 1)]);
  end;

  {$IFNDEF SUPPORT_MSECS}
  STime.Year        := CTime.tm_year + 1900;
  STime.Month       := CTime.tm_mon + 1;
  STime.Day         := CTime.tm_mday;
  STime.Hour        := CTime.tm_hour;
  STime.Minute      := CTime.tm_min;
  STime.Second      := CTime.tm_sec;
  STime.Millisecond := 0;

  PTime := SystemTimeToDateTime(STime);
  {$ENDIF}
  Move(PTime, Buffer^, SizeOf(PTime));
end;

procedure TIBConnection.SetDateTime(CurrBuff: pointer; PTime : TDateTime; AType : integer);
{$IFNDEF SUPPORT_MSECS}
var
  CTime : TTm;          // C struct time
  STime : TSystemTime;  // System time
{$ENDIF}
begin
  {$IFNDEF SUPPORT_MSECS}
  DateTimeToSystemTime(PTime,STime);
  
  CTime.tm_year := STime.Year - 1900;
  CTime.tm_mon  := STime.Month -1;
  CTime.tm_mday := STime.Day;
  CTime.tm_hour := STime.Hour;
  CTime.tm_min  := STime.Minute;
  CTime.tm_sec  := STime.Second;
  {$ENDIF}
  case (AType and not 1) of
    SQL_TYPE_DATE :
      {$IFNDEF SUPPORT_MSECS}
      isc_encode_sql_date(@CTime, PISC_DATE(CurrBuff));
      {$ELSE}
      PISC_DATE(CurrBuff)^ := Trunc(PTime) + IBDateOffset;
      {$ENDIF}
    SQL_TYPE_TIME :
      {$IFNDEF SUPPORT_MSECS}
      isc_encode_sql_time(@CTime, PISC_TIME(CurrBuff));
      {$ELSE}
      PISC_TIME(CurrBuff)^ := Trunc(abs(Frac(PTime)) * IBSecsCount);
      {$ENDIF}
    SQL_TIMESTAMP :
      begin
      {$IFNDEF SUPPORT_MSECS}
      isc_encode_timestamp(@CTime, PISC_TIMESTAMP(CurrBuff));
      {$ELSE}
      PISC_TIMESTAMP(CurrBuff)^.timestamp_date := Trunc(PTime) + IBDateOffset;
      PISC_TIMESTAMP(CurrBuff)^.timestamp_time := Trunc(abs(Frac(PTime)) * IBSecsCount);
      {$ENDIF}
      end
  else
    Raise EIBDatabaseError.CreateFmt('Invalid parameter type for date encode : %d',[(AType and not 1)]);
  end;
end;

function TIBConnection.GetSchemaInfoSQL(SchemaType : TSchemaType; SchemaObjectName, SchemaPattern : string) : string;

var s : string;

begin
  case SchemaType of
    stTables     : s := 'select '+
                          'rdb$relation_id          as recno, '+
                          '''' + DatabaseName + ''' as catalog_name, '+
                          '''''                     as schema_name, '+
                          'rdb$relation_name        as table_name, '+
                          '0                        as table_type '+
                        'from '+
                          'rdb$relations '+
                        'where '+
                          '(rdb$system_flag = 0 or rdb$system_flag is null) ' + // and rdb$view_blr is null
                        'order by rdb$relation_name';

    stSysTables  : s := 'select '+
                          'rdb$relation_id          as recno, '+
                          '''' + DatabaseName + ''' as catalog_name, '+
                          '''''                     as schema_name, '+
                          'rdb$relation_name        as table_name, '+
                          '0                        as table_type '+
                        'from '+
                          'rdb$relations '+
                        'where '+
                          '(rdb$system_flag > 0) ' + // and rdb$view_blr is null
                        'order by rdb$relation_name';

    stProcedures : s := 'select '+
                           'rdb$procedure_id        as recno, '+
                          '''' + DatabaseName + ''' as catalog_name, '+
                          '''''                     as schema_name, '+
                          'rdb$procedure_name       as proc_name, '+
                          '0                        as proc_type, '+
                          'rdb$procedure_inputs     as in_params, '+
                          'rdb$procedure_outputs    as out_params '+
                        'from '+
                          'rdb$procedures '+
                        'WHERE '+
                          '(rdb$system_flag = 0 or rdb$system_flag is null)';
    stColumns    : s := 'select '+
                           'rdb$field_id            as recno, '+
                          '''' + DatabaseName + ''' as catalog_name, '+
                          '''''                     as schema_name, '+
                          'rdb$relation_name        as table_name, '+
                          'rdb$field_name           as column_name, '+
                          'rdb$field_position       as column_position, '+
                          '0                        as column_type, '+
                          '0                        as column_datatype, '+
                          '''''                     as column_typename, '+
                          '0                        as column_subtype, '+
                          '0                        as column_precision, '+
                          '0                        as column_scale, '+
                          '0                        as column_length, '+
                          '0                        as column_nullable '+
                        'from '+
                          'rdb$relation_fields '+
                        'WHERE '+
                          '(rdb$system_flag = 0 or rdb$system_flag is null) and (rdb$relation_name = ''' + Uppercase(SchemaObjectName) + ''') ' +
                        'order by rdb$field_name';
  else
    DatabaseError(SMetadataUnavailable)
  end; {case}
  result := s;
end;


procedure TIBConnection.UpdateIndexDefs(IndexDefs : TIndexDefs;TableName : string);

var qry : TSQLQuery;

begin
  if not assigned(Transaction) then
    DatabaseError(SErrConnTransactionnSet);

  qry := tsqlquery.Create(nil);
  qry.transaction := Transaction;
  qry.database := Self;
  with qry do
    begin
    ReadOnly := True;
    sql.clear;
    sql.add('select '+
              'ind.rdb$index_name, '+
              'ind.rdb$relation_name, '+
              'ind.rdb$unique_flag, '+
              'ind_seg.rdb$field_name, '+
              'rel_con.rdb$constraint_type, '+
              'ind.rdb$index_type '+
            'from '+
              'rdb$index_segments ind_seg, '+
              'rdb$indices ind '+
             'left outer join '+
              'rdb$relation_constraints rel_con '+
             'on '+
              'rel_con.rdb$index_name = ind.rdb$index_name '+
            'where '+
              '(ind_seg.rdb$index_name = ind.rdb$index_name) and '+
              '(ind.rdb$relation_name=''' +  UpperCase(TableName) +''') '+
            'order by '+
              'ind.rdb$index_name;');
    open;
    end;
  while not qry.eof do with IndexDefs.AddIndexDef do
    begin
    Name := trim(qry.fields[0].asstring);
    Fields := trim(qry.Fields[3].asstring);
    If qry.fields[4].asstring = 'PRIMARY KEY' then options := options + [ixPrimary];
    If qry.fields[2].asinteger = 1 then options := options + [ixUnique];
    If qry.fields[5].asInteger = 1 then options:=options+[ixDescending];
    qry.next;
    while (name = trim(qry.fields[0].asstring)) and (not qry.eof) do
      begin
      Fields := Fields + ';' + trim(qry.Fields[3].asstring);
      qry.next;
      end;
    end;
  qry.close;
  qry.free;
end;

procedure TIBConnection.SetFloat(CurrBuff: pointer; Dbl: Double; Size: integer);

var
  Ext : extended;
  Sin : single;
begin
  case Size of
    4 :
      begin
        Sin := Dbl;
        Move(Sin, CurrBuff^, 4);
      end;
    8 :
      begin
        Move(Dbl, CurrBuff^, 8);
      end;
    10:
      begin
        Ext := Dbl;
        Move(Ext, CurrBuff^, 10);
      end;
  else
    Raise EIBDatabaseError.CreateFmt('Invalid float size for float encode : %d',[Size]);
  end;
end;

procedure TIBConnection.GetFloat(CurrBuff, Buffer : pointer; Size : byte);
var
  Ext : extended;
  Dbl : double;
  Sin : single;
begin
  case Size of
    4 :
      begin
        Move(CurrBuff^, Sin, 4);
        Dbl := Sin;
      end;
    8 :
      begin
        Move(CurrBuff^, Dbl, 8);
      end;
    10:
      begin
        Move(CurrBuff^, Ext, 10);
        Dbl := double(Ext);
      end;
  else
    Raise EIBDatabaseError.CreateFmt('Invalid float size for float Decode : %d',[Size]);
  end;
  Move(Dbl, Buffer^, 8);
end;

function TIBConnection.GetBlobSize(blobHandle: TIsc_Blob_Handle): LongInt;
var
  iscInfoBlobTotalLength : byte;
  blobInfo : array[0..50] of byte;

begin
  iscInfoBlobTotalLength:=isc_info_blob_total_length;
  if isc_blob_info(@Fstatus[0], @blobHandle, sizeof(iscInfoBlobTotalLength), pchar(@iscInfoBlobTotalLength), sizeof(blobInfo) - 2, pchar(@blobInfo[0])) <> 0 then
    CheckError('isc_blob_info', FStatus);
  if blobInfo[0]  = iscInfoBlobTotalLength then
    begin
      result :=  isc_vax_integer(pchar(@blobInfo[3]), isc_vax_integer(pchar(@blobInfo[1]), 2));
    end
  else
     CheckError('isc_blob_info', FStatus);
end;

procedure TIBConnection.LoadBlobIntoBuffer(FieldDef: TFieldDef;ABlobBuf: PBufBlobField; cursor: TSQLCursor; ATransaction : TSQLTransaction);
const
  isc_segstr_eof = 335544367; // It's not defined in ibase60 but in ibase40. Would it be better to define in ibase60?

var
  blobHandle : Isc_blob_Handle;
  blobSegment : pointer;
  blobSegLen : word;
  blobSize: LongInt;
  TransactionHandle : pointer;
  blobId : PISC_QUAD;
  ptr : Pointer;
begin
  blobId := PISC_QUAD(@(ABlobBuf^.ConnBlobBuffer));

  TransactionHandle := Atransaction.Handle;
  blobHandle := FB_API_NULLHANDLE;

  if isc_open_blob(@FStatus[0], @FSQLDatabaseHandle, @TransactionHandle, @blobHandle, blobId) <> 0 then
    CheckError('TIBConnection.CreateBlobStream', FStatus);

  blobSize := GetBlobSize(blobHandle);

  //For performance, read as much as we can, regardless of any segment size set in database.
  blobSegment := AllocMem(MAXBLOBSEGMENTSIZE);

  with ABlobBuf^.BlobBuffer^ do
    begin
    Size := 0;
    // Test for Size is a workaround for Win64 Firebird embedded crashing in isc_get_segment when entire blob is read.
    while (Size < blobSize) and (isc_get_segment(@FStatus[0], @blobHandle, @blobSegLen, MAXBLOBSEGMENTSIZE, blobSegment) = 0) do
      begin
      ReAllocMem(Buffer,Size+blobSegLen);
      ptr := Buffer+Size;
      move(blobSegment^,ptr^,blobSegLen);
      inc(Size,blobSegLen);
      end;

   freemem(blobSegment);

    // Throwing the proper error on failure is more important than closing the blob:
    // Test for Size is another workaround.
    if (Size = blobSize) or (FStatus[1] = isc_segstr_eof) then
      begin
        if isc_close_blob(@FStatus[0], @blobHandle) <> 0 then
          CheckError('TIBConnection.CreateBlobStream isc_close_blob', FStatus);
      end
    else
      CheckError('TIBConnection.CreateBlobStream isc_get_segment', FStatus);
    end;
end;

function TIBConnection.RowsAffected(cursor: TSQLCursor): TRowsCount;

var info_request       : string;
    resbuf             : array[0..63] of byte;
    i                  : integer;
    BlockSize,
    subBlockSize       : integer;
    SelectedRows,
    InsertedRows       : integer;
    
begin
  SelectedRows:=-1;
  InsertedRows:=-1;

  if assigned(cursor) then with cursor as TIBCursor do
   if assigned(statement) then
    begin
    info_request := chr(isc_info_sql_records);
    if isc_dsql_sql_info(@Status[0],@Statement,Length(info_request), @info_request[1],sizeof(resbuf),@resbuf) <> 0 then
      CheckError('RowsAffected', Status);

    i := 0;
    while not (byte(resbuf[i]) in [isc_info_end,isc_info_truncated]) do
      begin
      BlockSize:=isc_vax_integer(@resbuf[i+1],2);
      if resbuf[i]=isc_info_sql_records then
        begin
        inc(i,3);
        BlockSize:=BlockSize+i;
        while (resbuf[i] <> isc_info_end) and (i < BlockSize) do
          begin
          subBlockSize:=isc_vax_integer(@resbuf[i+1],2);
          if resbuf[i] = isc_info_req_select_count then
            SelectedRows := isc_vax_integer(@resbuf[i+3],subBlockSize)
          else if resbuf[i] = isc_info_req_insert_count then
            InsertedRows := isc_vax_integer(@resbuf[i+3],subBlockSize);
          inc(i,subBlockSize+3);
          end;
        end
      else
        inc(i,BlockSize+3);
      end;
    end;
  if SelectedRows>0 then result:=SelectedRows
  else Result:=InsertedRows;
end;

{ TIBConnectionDef }

class function TIBConnectionDef.TypeName: String;
begin
  Result:='Firebird';
end;
  
class function TIBConnectionDef.ConnectionClass: TSQLConnectionClass;
begin
  Result:=TIBConnection;
end;
    
class function TIBConnectionDef.Description: String;
begin
  Result:='Connect to Firebird/Interbase directly via the client library';
end;

initialization
  RegisterConnection(TIBConnectionDef);

finalization
  UnRegisterConnection(TIBConnectionDef);
end.
