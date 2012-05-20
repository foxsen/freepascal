{
    This file is part of the Free Pascal run time library.
    Copyright (c) 1999-2009 by the Free Pascal development team

    THTTPApplication class.

    See the file COPYING.FPC, included in this distribution,
    for details about the copyright.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

 **********************************************************************}
{ $define CGIDEBUG}
{$mode objfpc}
{$H+}

unit custhttpapp;

Interface

uses
  Classes, SysUtils, httpdefs, custweb, ssockets,  fphttpserver;

Type
  TCustomHTTPApplication = Class;
  TFPHTTPServerHandler = Class;

  { TEmbeddedHttpServer }

  TEmbeddedHttpServer = Class(TFPCustomHttpServer)
  Private
    FWebHandler: TFPHTTPServerHandler;
  protected
    Procedure InitRequest(ARequest : TFPHTTPConnectionRequest); virtual;
    Procedure InitResponse(AResponse : TFPHTTPConnectionResponse); virtual;
    Property WebHandler : TFPHTTPServerHandler Read FWebHandler;
    Property Active;
  end;

  { TFCgiHandler }

  { TFPHTTPServerHandler }

  TFPHTTPServerHandler = class(TWebHandler)
    procedure HTTPHandleRequest(Sender: TObject;
      var ARequest: TFPHTTPConnectionRequest;
      var AResponse: TFPHTTPConnectionResponse);
  Private
    FServer: TEmbeddedHTTPServer;
    function GetAllowConnect: TConnectQuery;
    function GetPort: Word;
    function GetQueueSize: Word;
    function GetThreaded: Boolean;
    procedure SetOnAllowConnect(const AValue: TConnectQuery);
    procedure SetPort(const AValue: Word);
    procedure SetQueueSize(const AValue: Word);
    procedure SetThreaded(const AValue: Boolean);
  protected
    Procedure InitRequest(ARequest : TRequest); override;
    Procedure InitResponse(AResponse : TResponse); override;
    function WaitForRequest(out ARequest : TRequest; out AResponse : TResponse) : boolean; override;
    Function CreateServer : TEmbeddedHttpServer; virtual;
    Property HTTPServer : TEmbeddedHttpServer Read FServer;
  Public
    Procedure Run; override;
    constructor Create(AOwner: TComponent); override;
    destructor Destroy; override;
    // Port to listen on.
    Property Port : Word Read GetPort Write SetPort Default 80;
    // Max connections on queue (for Listen call)
    Property QueueSize : Word Read GetQueueSize Write SetQueueSize Default 5;
    // Called when deciding whether to accept a connection.
    Property OnAllowConnect : TConnectQuery Read GetAllowConnect Write SetOnAllowConnect;
    // Use a thread to handle a connection ?
    property Threaded : Boolean read GetThreaded Write SetThreaded;
  end;

  { TCustomHTTPApplication }

  TCustomHTTPApplication = Class(TCustomWebApplication)
  private
    function GetAllowConnect: TConnectQuery;
    function GetPort: Word;
    function GetQueueSize: Word;
    function GetThreaded: Boolean;
    procedure SetOnAllowConnect(const AValue: TConnectQuery);
    procedure SetPort(const AValue: Word);
    procedure SetQueueSize(const AValue: Word);
    procedure SetThreaded(const AValue: Boolean);
  protected
    function InitializeWebHandler: TWebHandler; override;
    Function HTTPHandler : TFPHTTPServerHandler;
  Public
    Property Port : Word Read GetPort Write SetPort Default 80;
    // Max connections on queue (for Listen call)
    Property QueueSize : Word Read GetQueueSize Write SetQueueSize Default 5;
    // Called when deciding whether to accept a connection.
    Property OnAllowConnect : TConnectQuery Read GetAllowConnect Write SetOnAllowConnect;
    // Use a thread to handle a connection ?
    property Threaded : Boolean read GetThreaded Write SetThreaded;
  end;

ResourceString
  SNoInputHandle    = 'Failed to open input-handle passed from server. Socket Error: %d';
  SNoSocket         = 'Failed to open socket. Socket Error: %d';
  SBindFailed       = 'Failed to bind to port %d. Socket Error: %d';
  SListenFailed     = 'Failed to listen to port %d. Socket Error: %d';
  SErrReadingSocket = 'Failed to read data from socket. Error: %d';
  SErrReadingHeader = 'Failed to read FastCGI header. Read only %d bytes';
  SErrWritingSocket = 'Failed to write data to socket. Error: %d';

Implementation

{ TEmbeddedHttpServer }

procedure TEmbeddedHttpServer.InitRequest(ARequest: TFPHTTPConnectionRequest);
begin
  WebHandler.InitRequest(ARequest);
end;

procedure TEmbeddedHttpServer.InitResponse(AResponse: TFPHTTPConnectionResponse
  );
begin
  WebHandler.InitResponse(AResponse);
end;

{$ifdef CGIDEBUG}
uses
  dbugintf;
{$endif}

{ TCustomHTTPApplication }

function TCustomHTTPApplication.GetAllowConnect: TConnectQuery;
begin
  Result:=HTTPHandler.OnAllowConnect;
end;

function TCustomHTTPApplication.GetPort: Word;
begin
  Result:=HTTPHandler.Port;
end;

function TCustomHTTPApplication.GetQueueSize: Word;
begin
  Result:=HTTPHandler.QueueSize;
end;

function TCustomHTTPApplication.GetThreaded: Boolean;
begin
  Result:=HTTPHandler.Threaded;
end;

procedure TCustomHTTPApplication.SetOnAllowConnect(const AValue: TConnectQuery);
begin
  HTTPHandler.OnAllowConnect:=AValue;
end;

procedure TCustomHTTPApplication.SetPort(const AValue: Word);
begin
  HTTPHandler.Port:=Avalue;
end;

procedure TCustomHTTPApplication.SetQueueSize(const AValue: Word);
begin
  HTTPHandler.QueueSize:=Avalue;
end;

procedure TCustomHTTPApplication.SetThreaded(const AValue: Boolean);
begin
  HTTPHandler.Threaded:=Avalue;
end;

function TCustomHTTPApplication.InitializeWebHandler: TWebHandler;
begin
  Result:=TFPHTTPServerHandler.Create(Self);
end;

function TCustomHTTPApplication.HTTPHandler: TFPHTTPServerHandler;
begin
  Result:=Webhandler as TFPHTTPServerHandler;
end;

{ TFPHTTPServerHandler }

procedure TFPHTTPServerHandler.HTTPHandleRequest(Sender: TObject;
  var ARequest: TFPHTTPConnectionRequest;
  var AResponse: TFPHTTPConnectionResponse);
begin
  // Exceptions are handled by (Do)HandleRequest. It also frees the response/request
  DoHandleRequest(ARequest,AResponse);
  ARequest:=Nil;
  AResponse:=Nil;
  If Terminated then
    FServer.Active:=False;
  if Assigned(OnIdle) then
    OnIdle(Self);
end;

function TFPHTTPServerHandler.GetAllowConnect: TConnectQuery;
begin
  Result:=FServer.OnAllowConnect;
end;

function TFPHTTPServerHandler.GetPort: Word;
begin
  Result:=FServer.Port;
end;

function TFPHTTPServerHandler.GetQueueSize: Word;
begin
  Result:=FServer.QueueSize;
end;

function TFPHTTPServerHandler.GetThreaded: Boolean;
begin
  Result:=FServer.Threaded;
end;

procedure TFPHTTPServerHandler.SetOnAllowConnect(const AValue: TConnectQuery);
begin
  FServer.OnAllowConnect:=Avalue
end;

procedure TFPHTTPServerHandler.SetPort(const AValue: Word);
begin
  FServer.Port:=Avalue
end;

procedure TFPHTTPServerHandler.SetQueueSize(const AValue: Word);
begin
  FServer.QueueSize:=Avalue
end;

procedure TFPHTTPServerHandler.SetThreaded(const AValue: Boolean);
begin
  FServer.Threaded:=AValue;
end;

procedure TFPHTTPServerHandler.InitRequest(ARequest: TRequest);
begin
  inherited InitRequest(ARequest);
end;

procedure TFPHTTPServerHandler.InitResponse(AResponse: TResponse);
begin
  inherited InitResponse(AResponse);
end;

function TFPHTTPServerHandler.WaitForRequest(out ARequest: TRequest;
  out AResponse: TResponse): boolean;
begin
  Result:=False;
  ARequest:=Nil;
  AResponse:=Nil;
end;

function TFPHTTPServerHandler.CreateServer: TEmbeddedHttpServer;
begin
  Result:=TEmbeddedHttpServer.Create(Self);
end;

procedure TFPHTTPServerHandler.Run;
begin
  Fserver.Active:=True;
end;

constructor TFPHTTPServerHandler.Create(AOwner: TComponent);
begin
  inherited Create(AOwner);
  FServer:=CreateServer;
  FServer.FWebHandler:=Self;
  FServer.OnRequest:=@HTTPHandleRequest;
end;

destructor TFPHTTPServerHandler.Destroy;
begin
  FServer.Active:=False;
  FreeAndNil(FServer);
  inherited Destroy;

end;


end.
