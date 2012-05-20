{
    This file is part of the Free Pascal run time library.
    Copyright (c) 1999-2009 by the Free Pascal development team

    TWebApplication class.

    See the file COPYING.FPC, included in this distribution,
    for details about the copyright.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

 **********************************************************************}
{ $define CGIDEBUG}
{$mode objfpc}
{$H+}

unit custweb;

Interface

uses
  CustApp,Classes,SysUtils, httpdefs, fphttp, eventlog;

Const
  CGIVarCount = 36;

Type
  TCGIVarArray = Array[1..CGIVarCount] of String;

Const
  CgiVarNames : TCGIVarArray =
   ({ 1  } 'AUTH_TYPE',
    { 2  } 'CONTENT_LENGTH',
    { 3  } 'CONTENT_TYPE',
    { 4  } 'GATEWAY_INTERFACE',
    { 5  } 'PATH_INFO',
    { 6  } 'PATH_TRANSLATED',
    { 7  } 'QUERY_STRING',
    { 8  } 'REMOTE_ADDR',
    { 9  } 'REMOTE_HOST',
    { 10 } 'REMOTE_IDENT',
    { 11 } 'REMOTE_USER',
    { 12 } 'REQUEST_METHOD',
    { 13 } 'SCRIPT_NAME',
    { 14 } 'SERVER_NAME',
    { 15 } 'SERVER_PORT',
    { 16 } 'SERVER_PROTOCOL',
    { 17 } 'SERVER_SOFTWARE',
    { 18 } 'HTTP_ACCEPT',
    { 19 } 'HTTP_ACCEPT_CHARSET',
    { 20 } 'HTTP_ACCEPT_ENCODING',
    { 21 } 'HTTP_IF_MODIFIED_SINCE',
    { 22 } 'HTTP_REFERER',
    { 23 } 'HTTP_USER_AGENT',
    { 24 } 'HTTP_COOKIE',
     // Additional Apache vars
    { 25 } 'HTTP_CONNECTION',
    { 26 } 'HTTP_ACCEPT_LANGUAGE',
    { 27 } 'HTTP_HOST',
    { 28 } 'SERVER_SIGNATURE',
    { 29 } 'SERVER_ADDR',
    { 30 } 'DOCUMENT_ROOT',
    { 31 } 'SERVER_ADMIN',
    { 32 } 'SCRIPT_FILENAME',
    { 33 } 'REMOTE_PORT',
    { 34 } 'REQUEST_URI',
    { 35 } 'CONTENT',
    { 36 } 'HTTP_X_REQUESTED_WITH'
    );

Type

  { TCustomWebApplication }

  TGetModuleEvent = Procedure (Sender : TObject; ARequest : TRequest;
                               Var ModuleClass : TCustomHTTPModuleClass) of object;
  TOnShowRequestException = procedure(AResponse: TResponse; AnException: Exception; var handled: boolean);
  TLogEvent = Procedure (EventType: TEventType; const Msg: String) of object;
  TInitModuleEvent = Procedure (Sender : TObject; Module: TCustomHTTPModule) of object;

  { TWebHandler }

  TWebHandler = class(TComponent)
  private
    FDefaultModuleName: String;
    FOnIdle: TNotifyEvent;
    FOnInitModule: TInitModuleEvent;
    FOnUnknownRequestEncoding: TOnUnknownEncodingEvent;
    FTerminated: boolean;
    FAdministrator: String;
    FAllowDefaultModule: Boolean;
    FApplicationURL: String;
    FEmail: String;
    FModuleVar: String;
    FOnGetModule: TGetModuleEvent;
    FOnShowRequestException: TOnShowRequestException;
    FHandleGetOnPost : Boolean;
    FRedirectOnError : Boolean;
    FRedirectOnErrorURL : String;
    FTitle: string;
    FOnTerminate : TNotifyEvent;
    FOnLog : TLogEvent;
    FPreferModuleName : Boolean;
  protected
    procedure Terminate;
    Function GetModuleName(Arequest : TRequest) : string;
    function WaitForRequest(out ARequest : TRequest; out AResponse : TResponse) : boolean; virtual; abstract;
    procedure EndRequest(ARequest : TRequest;AResponse : TResponse); virtual;
    function FindModule(ModuleClass : TCustomHTTPModuleClass): TCustomHTTPModule;
    Procedure SetBaseURL(AModule : TCustomHTTPModule; Const AModuleName : String; ARequest : TRequest); virtual;
    function GetApplicationURL(ARequest : TRequest): String; virtual;
    procedure ShowRequestException(R: TResponse; E: Exception); virtual;
    Procedure InitRequest(ARequest : TRequest); virtual;
    Procedure InitResponse(AResponse : TResponse); virtual;
    Function GetEmail : String; virtual;
    Function GetAdministrator : String; virtual;
    property Terminated: boolean read FTerminated;
  Public
    constructor Create(AOwner: TComponent); override;
    Procedure Run; virtual;
    Procedure Log(EventType : TEventType; Const Msg : String);
    Procedure DoHandleRequest(ARequest : TRequest; AResponse : TResponse);
    Procedure HandleRequest(ARequest : TRequest; AResponse : TResponse); virtual;
    Property HandleGetOnPost : Boolean Read FHandleGetOnPost Write FHandleGetOnPost;
    Property RedirectOnError : boolean Read FRedirectOnError Write FRedirectOnError;
    Property RedirectOnErrorURL : string Read FRedirectOnErrorURL Write FRedirectOnErrorURL;
    Property ApplicationURL : String Read FApplicationURL Write FApplicationURL;
    Property AllowDefaultModule : Boolean Read FAllowDefaultModule Write FAllowDefaultModule;
    Property DefaultModuleName : String Read FDefaultModuleName Write FDefaultModuleName;
    Property ModuleVariable : String Read FModuleVar Write FModuleVar;
    Property OnGetModule : TGetModuleEvent Read FOnGetModule Write FOnGetModule;
    Property Email : String Read GetEmail Write FEmail;
    property Title: string read FTitle write FTitle;
    Property Administrator : String Read GetAdministrator Write FAdministrator;
    property OnShowRequestException: TOnShowRequestException read FOnShowRequestException write FOnShowRequestException;
    property OnIdle: TNotifyEvent read FOnIdle write FOnIdle;
    Property OnLog : TLogEvent Read FOnLog Write FOnLog;
    Property OnUnknownRequestEncoding : TOnUnknownEncodingEvent Read FOnUnknownRequestEncoding Write FOnUnknownRequestEncoding;
    Property OnInitModule: TInitModuleEvent Read FOnInitModule write FOnInitModule;
    Property PreferModuleName : Boolean Read FPreferModuleName Write FPreferModuleName;
  end;

  TCustomWebApplication = Class(TCustomApplication)
  Private
    FEventLog: TEventLog;
    FWebHandler: TWebHandler;
    function GetAdministrator: String;
    function GetAllowDefaultModule: Boolean;
    function GetApplicationURL: String;
    function GetDefaultModuleName: String;
    function GetEmail: String;
    function GetEventLog: TEventLog;
    function GetHandleGetOnPost: Boolean;
    function GetModuleVar: String;
    function GetOnGetModule: TGetModuleEvent;
    function GetOnShowRequestException: TOnShowRequestException;
    function GetOnUnknownRequestEncoding: TOnUnknownEncodingEvent;
    function GetRedirectOnError: boolean;
    function GetRedirectOnErrorURL: string;
    function GetPreferModuleName: boolean;
    procedure SetAdministrator(const AValue: String);
    procedure SetAllowDefaultModule(const AValue: Boolean);
    procedure SetApplicationURL(const AValue: String);
    procedure SetDefaultModuleName(AValue: String);
    procedure SetEmail(const AValue: String);
    procedure SetHandleGetOnPost(const AValue: Boolean);
    procedure SetModuleVar(const AValue: String);
    procedure SetOnGetModule(const AValue: TGetModuleEvent);
    procedure SetOnShowRequestException(const AValue: TOnShowRequestException);
    procedure SetOnUnknownRequestEncoding(AValue: TOnUnknownEncodingEvent);
    procedure SetRedirectOnError(const AValue: boolean);
    procedure SetRedirectOnErrorURL(const AValue: string);
    procedure SetPreferModuleName(const AValue: boolean);
    procedure DoOnTerminate(Sender : TObject);
  protected
    Procedure DoRun; override;
    function InitializeWebHandler: TWebHandler; virtual; abstract;
    Procedure DoLog(EventType: TEventType; const Msg: String); override;
    procedure SetTitle(const AValue: string); override;
    property WebHandler: TWebHandler read FWebHandler write FWebHandler;
  Public
    constructor Create(AOwner: TComponent); override;
    destructor Destroy; override;
    Procedure CreateForm(AClass : TComponentClass; out Reference);
    Procedure Initialize; override;
    procedure Terminate; override;
    Property HandleGetOnPost : Boolean Read GetHandleGetOnPost Write SetHandleGetOnPost;
    Property RedirectOnError : boolean Read GetRedirectOnError Write SetRedirectOnError;
    Property RedirectOnErrorURL : string Read GetRedirectOnErrorURL Write SetRedirectOnErrorURL;
    Property ApplicationURL : String Read GetApplicationURL Write SetApplicationURL;
    Property AllowDefaultModule : Boolean Read GetAllowDefaultModule Write SetAllowDefaultModule;
    Property DefaultModuleName : String Read GetDefaultModuleName Write SetDefaultModuleName;
    Property ModuleVariable : String Read GetModuleVar Write SetModuleVar;
    Property OnGetModule : TGetModuleEvent Read GetOnGetModule Write SetOnGetModule;
    Property Email : String Read GetEmail Write SetEmail;
    Property Administrator : String Read GetAdministrator Write SetAdministrator;
    property OnShowRequestException: TOnShowRequestException read GetOnShowRequestException write SetOnShowRequestException;
    Property OnUnknownRequestEncoding : TOnUnknownEncodingEvent Read GetOnUnknownRequestEncoding Write SetOnUnknownRequestEncoding;
    Property EventLog: TEventLog read GetEventLog;
    Property PreferModuleName : Boolean Read GetPreferModuleName Write SetPreferModuleName;
  end;

  EFPWebError = Class(Exception);

procedure ExceptionToHTML(S: TStrings; const E: Exception; const Title, Email, Administrator: string);

Implementation

{$ifdef CGIDEBUG}
uses
  dbugintf;
{$endif}

resourcestring
  SErrNoModuleNameForRequest = 'Could not determine HTTP module name for request';
  SErrNoModuleForRequest = 'Could not determine HTTP module for request "%s"';
  SModuleError = 'Module Error';
  SAppEncounteredError = 'The application encountered the following error:';
  SError = 'Error: ';
  SNotify = 'Notify: ';

procedure ExceptionToHTML(S: TStrings; const E: Exception; const Title, Email, Administrator: string);
var
  FrameNumber: Integer;
  Frames: PPointer;
  FrameCount: integer;
  TheEmail: String;
begin
  With S do
    begin
    Add('<html><head><title>'+Title+': '+SModuleError+'</title></head>'+LineEnding);
    Add('<body>');
    Add('<center><hr><h1>'+Title+': ERROR</h1><hr></center><br><br>');
    Add(SAppEncounteredError+'<br>');
    Add('<ul>');
    Add('<li>'+SError+' <b>'+E.Message+'</b>');
    Add('<li> Stack trace:<br>');
    Add(BackTraceStrFunc(ExceptAddr)+'<br>');
    FrameCount:=ExceptFrameCount;
    Frames:=ExceptFrames;
    for FrameNumber := 0 to FrameCount-1 do
      Add(BackTraceStrFunc(Frames[FrameNumber])+'<br>');
    Add('</ul><hr>');
    TheEmail:=Email;
    If (TheEmail<>'') then
      Add('<h5><p><i>'+SNotify+Administrator+': <a href="mailto:'+TheEmail+'">'+TheEmail+'</a></i></p></h5>');
    Add('</body></html>');
    end;
end;

procedure TWebHandler.Run;
var ARequest : TRequest;
    AResponse : TResponse;
begin
  while not FTerminated do
    begin
    if WaitForRequest(ARequest,AResponse) then
      DoHandleRequest(ARequest,AResponse);
    if assigned(OnIdle) then
      OnIdle(Self);
    end;
end;

procedure TWebHandler.Log(EventType: TEventType; const Msg: String);
begin
  If Assigned(FOnLog) then
    FOnLog(EventType,Msg);
end;

procedure TWebHandler.ShowRequestException(R: TResponse; E: Exception);
Var
 S : TStrings;
 handled: boolean;

begin
  if R.ContentSent then exit;
  if assigned(OnShowRequestException) then
    begin
    handled:=false;
    OnShowRequestException(R,E,Handled);
    if handled then exit;
    end;
  If RedirectOnError and not R.HeadersSent then
    begin
    R.SendRedirect(format(RedirectOnErrorURL,[HTTPEncode(E.Message)]));
    R.SendContent;
    Exit;
    end;
  If (not R.HeadersSent) then
    begin
    R.Code:=500;
    R.CodeText:='Application error '+E.ClassName;
    R.ContentType:='text/html';
    end;
  If (R.ContentType='text/html') then
    begin
    S:=TStringList.Create;
    Try
      ExceptionToHTML(S, E, Title, Email, Administrator);
      R.Content:=S.Text;
      R.SendContent;
    Finally
      FreeAndNil(S);
    end;
    end;
end;

procedure TWebHandler.InitRequest(ARequest: TRequest);
begin
  ARequest.OnUnknownEncoding:=Self.OnUnknownRequestEncoding;
end;

procedure TWebHandler.InitResponse(AResponse: TResponse);
begin
  // Do nothing
end;

function TWebHandler.GetEmail: String;
begin
  Result := FEmail;
end;

function TWebHandler.GetAdministrator: String;
begin
  Result := FAdministrator;
end;

procedure TWebHandler.HandleRequest(ARequest: TRequest; AResponse: TResponse);
Var
  MC : TCustomHTTPModuleClass;
  M  : TCustomHTTPModule;
  MN : String;
  MI : TModuleItem;

begin
  try
    MC:=Nil;
    M:=NIL;
    MI:=Nil;
    If (OnGetModule<>Nil) then
      OnGetModule(Self,ARequest,MC);
    If (MC=Nil) then
      begin
      MN:=GetModuleName(ARequest);
      MI:=ModuleFactory.FindModule(MN);
      if (MI=Nil) then
        Raise EFPWebError.CreateFmt(SErrNoModuleForRequest,[MN]);
      MC:=MI.ModuleClass;
      end;
    M:=FindModule(MC); // Check if a module exists already
    If (M=Nil) then
      if assigned(MI) and Mi.SkipStreaming then
        M:=MC.CreateNew(Self)
      else
        M:=MC.Create(Self);
    SetBaseURL(M,MN,ARequest);
    if (OnInitModule<>Nil) then
      OnInitModule(Self,M);
    M.DoAfterInitModule(ARequest);
    if M.Kind=wkOneShot then
      begin
      try
        M.HandleRequest(ARequest,AResponse);
      finally
        M.Free;
      end;
      end
    else
      M.HandleRequest(ARequest,AResponse);
  except
    On E : Exception do
      ShowRequestException(AResponse,E);
  end;
end;

function TWebHandler.GetApplicationURL(ARequest: TRequest): String;
begin
  Result:=FApplicationURL;
  If (Result='') then
    Result:=ARequest.ScriptName;
end;

procedure TWebHandler.Terminate;
begin
  FTerminated := true;
  If Assigned(FOnTerminate) then 
    FOnTerminate(Self);
end;

function TWebHandler.GetModuleName(Arequest: TRequest): string;

   Function GetDefaultModuleName : String;

   begin
      if (DefaultModuleName<>'') then
        Result:=DefaultModuleName
      else if (ModuleFactory.Count=1) then
        Result:=ModuleFactory[0].ModuleName;
   end;

var
  S : String;
  I : Integer;

begin
  If (FModuleVar<>'') then
    Result:=ARequest.QueryFields.Values[FModuleVar];//Module name from query parameter using the FModuleVar as parameter name (default is 'Module')
  If (Result='') then
    begin
    S:=ARequest.PathInfo;
    If (Length(S)>0) and (S[1]='/') then  
      Delete(S,1,1);                      //Delete the leading '/' if exists
    I:=Length(S);
    If (I>0) and (S[I]='/') then
      Delete(S,I,1);                      //Delete the trailing '/' if exists
    I:=Pos('/',S);
    if (I>0) or PreferModuleName then
      Result:=ARequest.GetNextPathInfo;
    end;
  If (Result='') then
    begin
    if Not AllowDefaultModule then
      Raise EFPWebError.Create(SErrNoModuleNameForRequest);
    Result:=GetDefaultModuleName
    end;
end;

procedure TWebHandler.EndRequest(ARequest: TRequest; AResponse: TResponse);
begin
  AResponse.Free;
  ARequest.Free;
end;

function TWebHandler.FindModule(ModuleClass: TCustomHTTPModuleClass): TCustomHTTPModule;
Var
  I : Integer;
begin
  I:=ComponentCount-1;
  While (I>=0) and (Not ((Components[i] is ModuleClass) and (TCustomHTTPModule(Components[i]).Kind<>wkOneShot))) do
    Dec(i);
  if (I>=0) then
    Result:=Components[i] as TCustomHTTPModule
  else
    Result:=Nil;
end;

procedure TWebHandler.SetBaseURL(AModule: TCustomHTTPModule;
  Const AModuleName : String; ARequest: TRequest);

Var
  S,P : String;

begin
  S:=IncludeHTTPPathDelimiter(GetApplicationURL(ARequest));
  P:=IncludeHTTPPathDelimiter(ARequest.ReturnedPathInfo);
  If (P='') or (P='/') then
    P:=IncludeHTTPPathDelimiter(AModuleName);
  if (Length(P)>0) and (P[1]='/') then
    Delete(P,1,1);
{$ifdef CGIDEBUG}
  senddebug(Format('SetBaseURL : "%s" "%s"',[S,P]));
{$endif CGIDEBUG}
  AModule.BaseURL:=S+P;
end;

procedure TWebHandler.DoHandleRequest(ARequest: TRequest; AResponse: TResponse);
begin
  HandleRequest(ARequest,AResponse);
  If Not AResponse.ContentSent then
    AResponse.SendContent;
  EndRequest(ARequest,AResponse);
end;

constructor TWebHandler.Create(AOwner:TComponent);
begin
  inherited Create(AOwner);
  FModuleVar:='Module'; // Do not localize
  FAllowDefaultModule:=True;
  FHandleGetOnPost := True;
  FRedirectOnError := False;
  FRedirectOnErrorURL := '';
end;

{ TCustomWebApplication }

function TCustomWebApplication.GetAdministrator: String;
begin
  result := FWebHandler.Administrator;
end;

function TCustomWebApplication.GetAllowDefaultModule: Boolean;
begin
  result := FWebHandler.AllowDefaultModule;
end;

function TCustomWebApplication.GetApplicationURL: String;
begin
  result := FWebHandler.ApplicationURL;
end;

function TCustomWebApplication.GetDefaultModuleName: String;
begin
  Result:=FWebHandler.DefaultModuleName;
end;

function TCustomWebApplication.GetEmail: String;
begin
  result := FWebHandler.Email;
end;

function TCustomWebApplication.GetEventLog: TEventLog;
begin
  if not assigned(FEventLog) then
    begin
    FEventLog := TEventLog.Create(Nil);
    FEventLog.Name:=Self.Name+'Logger';
    FEventLog.Identification:=Title;
    FEventLog.RegisterMessageFile(ParamStr(0));
    FEventLog.LogType:=ltSystem;
    FEventLog.Active:=True;
    end;
  Result := FEventLog;
end;

function TCustomWebApplication.GetHandleGetOnPost: Boolean;
begin
  result := FWebHandler.HandleGetOnPost;
end;

function TCustomWebApplication.GetModuleVar: String;
begin
  result := FWebHandler.ModuleVariable;
end;

function TCustomWebApplication.GetOnGetModule: TGetModuleEvent;
begin
  result := FWebHandler.OnGetModule;
end;

function TCustomWebApplication.GetOnShowRequestException: TOnShowRequestException;
begin
  result := FWebHandler.OnShowRequestException;
end;

function TCustomWebApplication.GetOnUnknownRequestEncoding: TOnUnknownEncodingEvent;
begin
  Result := FWebHandler.OnUnknownRequestEncoding
end;

function TCustomWebApplication.GetRedirectOnError: boolean;
begin
  result := FWebHandler.RedirectOnError;
end;

function TCustomWebApplication.GetPreferModuleName: boolean;
begin
  result := FWebHandler.PreferModuleName;
end;

function TCustomWebApplication.GetRedirectOnErrorURL: string;
begin
  result := FWebHandler.RedirectOnErrorURL;
end;

procedure TCustomWebApplication.SetAdministrator(const AValue: String);
begin
  FWebHandler.Administrator := AValue;
end;

procedure TCustomWebApplication.SetAllowDefaultModule(const AValue: Boolean);
begin
  FWebHandler.AllowDefaultModule := AValue;
end;

procedure TCustomWebApplication.SetApplicationURL(const AValue: String);
begin
  FWebHandler.ApplicationURL := AValue;
end;

procedure TCustomWebApplication.SetDefaultModuleName(AValue: String);
begin
  FWebHandler.DefaultModuleName:=AValue;
end;

procedure TCustomWebApplication.SetEmail(const AValue: String);
begin
  FWebHandler.Email := AValue;
end;

procedure TCustomWebApplication.SetHandleGetOnPost(const AValue: Boolean);
begin
  FWebHandler.HandleGetOnPost := AValue;
end;

procedure TCustomWebApplication.SetModuleVar(const AValue: String);
begin
  FWebHandler.ModuleVariable := AValue;
end;

procedure TCustomWebApplication.SetOnGetModule(const AValue: TGetModuleEvent);
begin
  FWebHandler.OnGetModule := AValue;
end;

procedure TCustomWebApplication.SetOnShowRequestException(const AValue: TOnShowRequestException);
begin
  FWebHandler.OnShowRequestException := AValue;
end;

procedure TCustomWebApplication.SetOnUnknownRequestEncoding(
  AValue: TOnUnknownEncodingEvent);
begin
  FWebHandler.OnUnknownRequestEncoding:=AValue;
end;

procedure TCustomWebApplication.SetRedirectOnError(const AValue: boolean);
begin
  FWebHandler.RedirectOnError := AValue;
end;

procedure TCustomWebApplication.SetPreferModuleName(const AValue: boolean);
begin
  FWebHandler.PreferModuleName := AValue;
end;

procedure TCustomWebApplication.SetRedirectOnErrorURL(const AValue: string);
begin
  FWebHandler.RedirectOnErrorURL :=AValue;
end;

procedure TCustomWebApplication.DoRun;
begin
  FWebHandler.Run;
end;

procedure TCustomWebApplication.SetTitle(const AValue: string);
begin
  inherited SetTitle(AValue);
  FWebHandler.Title := Title;
end;

constructor TCustomWebApplication.Create(AOwner: TComponent);
begin
  Inherited Create(AOwner);
  FWebHandler := InitializeWebHandler;
  FWebHandler.FOnTerminate:=@DoOnTerminate;
  FWebHandler.FOnLog:=@Log;
end;

procedure TCustomWebApplication.DoOnTerminate(Sender : TObject);
begin
  If Not Terminated then
    Terminate;
end;

destructor TCustomWebApplication.Destroy;
begin
  FWebHandler.Free;
  if assigned(FEventLog) then
    FEventLog.Free;
end;

procedure TCustomWebApplication.CreateForm(AClass: TComponentClass; out Reference);
begin
  TComponent(Reference):=AClass.Create(FWebHandler);
end;

procedure TCustomWebApplication.Initialize;
begin
  StopOnException:=True;
  Inherited;
end;

procedure TCustomWebApplication.DoLog(EventType: TEventType; const Msg: String);
begin
  EventLog.log(EventType,Msg);
end;

Procedure TCustomWebApplication.Terminate;

begin
  Inherited;
  If Not Webhandler.FTerminated then
    WebHandler.Terminate;
end;


end.

