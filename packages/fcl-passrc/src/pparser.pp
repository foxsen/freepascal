{
    This file is part of the Free Component Library

    Pascal source parser
    Copyright (c) 2000-2005 by
      Areca Systems GmbH / Sebastian Guenther, sg@freepascal.org

    See the file COPYING.FPC, included in this distribution,
    for details about the copyright.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

 **********************************************************************}

{$mode objfpc}
{$h+}

unit PParser;

interface

uses SysUtils, Classes, PasTree, PScanner;

resourcestring
  SErrNoSourceGiven = 'No source file specified';
  SErrMultipleSourceFiles = 'Please specify only one source file';
  SParserError = 'Error';
  SParserErrorAtToken = '%s at token "%s" in file %s at line %d column %d';
  SParserUngetTokenError = 'Internal error: Cannot unget more tokens, history buffer is full';
  SParserExpectTokenError = 'Expected "%s"';
  SParserExpectVisibility = 'Expected visibility specifier';
  SParserStrangeVisibility = 'Strange strict visibility encountered : "%s"';
  SParserExpectToken2Error = 'Expected "%s" or "%s"';
  SParserExpectedCommaRBracket = 'Expected "," or ")"';
  SParserExpectedCommaSemicolon = 'Expected "," or ";"';
  SParserExpectedCommaColon = 'Expected "," or ":"';
  SParserExpectedLBracketColon = 'Expected "(" or ":"';
  SParserExpectedLBracketSemicolon = 'Expected "(" or ";"';
  SParserExpectedColonSemicolon = 'Expected ":" or ";"';
  SParserExpectedSemiColonEnd = 'Expected ";" or "End"';
  SParserExpectedConstVarID = 'Expected "const", "var" or identifier';
  SParserExpectedColonID = 'Expected ":" or identifier';
  SParserSyntaxError = 'Syntax error';
  SParserTypeSyntaxError = 'Syntax error in type';
  SParserArrayTypeSyntaxError = 'Syntax error in array type';
  SParserInterfaceTokenError = 'Invalid token in interface section of unit';
  SParserImplementationTokenError = 'Invalid token in implementation section of unit';
  SParserInvalidTypeDef = 'Invalid type definition';
  SParserExpectedIdentifier = 'Identifier expected';
  SParserNotAProcToken = 'Not a procedure or function token';
  SRangeExpressionExpected = 'Range expression expected';

  SLogStartImplementation = 'Start parsing implementation section.';
  SLogStartInterface = 'Start parsing interface section';

type
  TPasParserLogHandler = Procedure (Sender : TObject; Const Msg : String) of object;
  TPParserLogEvent = (pleInterface,pleImplementation);
  TPParserLogEvents = set of TPParserLogEvent;

  { TPasTreeContainer }

  TPasTreeContainer = class
  private
    FOnLog: TPasParserLogHandler;
    FPParserLogEvents: TPParserLogEvents;
    FScannerLogEvents: TPScannerLogEvents;
  protected
    FPackage: TPasPackage;
    FInterfaceOnly : Boolean;
  public
    function CreateElement(AClass: TPTreeElement; const AName: String;
      AParent: TPasElement; const ASourceFilename: String;
      ASourceLinenumber: Integer): TPasElement;overload;
    function CreateElement(AClass: TPTreeElement; const AName: String;
      AParent: TPasElement; AVisibility: TPasMemberVisibility;
      const ASourceFilename: String; ASourceLinenumber: Integer): TPasElement;overload;
      virtual; abstract;
    function CreateFunctionType(const AName, AResultName: String; AParent: TPasElement;
      UseParentAsResultParent: Boolean; const ASourceFilename: String;
      ASourceLinenumber: Integer): TPasFunctionType;
    function FindElement(const AName: String): TPasElement; virtual; abstract;
    function FindModule(const AName: String): TPasModule; virtual;
    property Package: TPasPackage read FPackage;
    property InterfaceOnly : Boolean Read FInterfaceOnly Write FInterFaceOnly;
    Property ScannerLogEvents : TPScannerLogEvents Read FScannerLogEvents Write FScannerLogEvents;
    Property ParserLogEvents : TPParserLogEvents Read FPParserLogEvents Write FPParserLogEvents;
    Property OnLog : TPasParserLogHandler Read FOnLog Write FOnLog;
  end;

  EParserError = class(Exception)
  private
    FFilename: String;
    FRow, FColumn: Integer;
  public
    constructor Create(const AReason, AFilename: String;
      ARow, AColumn: Integer);
    property Filename: String read FFilename;
    property Row: Integer read FRow;
    property Column: Integer read FColumn;
  end;

  TProcType = (ptProcedure, ptFunction, ptOperator, ptConstructor, ptDestructor,
               ptClassProcedure, ptClassFunction);


  TExprKind = (ek_Normal, ek_PropertyIndex);

  { TPasParser }

  TPasParser = class
  private
    FCurModule: TPasModule;
    FFileResolver: TBaseFileResolver;
    FLogEvents: TPParserLogEvents;
    FOnLog: TPasParserLogHandler;
    FOptions: TPOptions;
    FScanner: TPascalScanner;
    FEngine: TPasTreeContainer;
    FCurToken: TToken;
    FCurTokenString: String;
    // UngetToken support:
    FTokenBuffer: array[0..1] of TToken;
    FTokenStringBuffer: array[0..1] of String;
    FTokenBufferIndex: Integer; // current index in FTokenBuffer
    FTokenBufferSize: Integer; // maximum valid index in FTokenBuffer
    function CheckOverloadList(AList: TFPList; AName: String; out OldMember: TPasElement): TPasOverloadedProc;
    procedure DumpCurToken(Const Msg : String);
    function GetVariableModifiers(Parent: TPasElement): string;
    function GetVariableValueAndLocation(Parent : TPasElement; out Value, Location: String): Boolean;
    procedure ParseVarList(Parent: TPasElement; VarList: TFPList; AVisibility: TPasMemberVisibility; Full: Boolean);
  protected
    function LogEvent(E : TPParserLogEvent) : Boolean; inline;
    Procedure DoLog(Const Msg : String; SkipSourceInfo : Boolean = False);overload;
    Procedure DoLog(Const Fmt : String; Args : Array of const;SkipSourceInfo : Boolean = False);overload;
    function GetProcTypeFromToken(tk: TToken; IsClass: Boolean=False ): TProcType;
    procedure ParseRecordFieldList(ARec: TPasRecordType; AEndToken: TToken);
    procedure ParseRecordVariantParts(ARec: TPasRecordType; AEndToken: TToken);
    function GetProcedureClass(ProcType : TProcType): TPTreeElement;
    procedure ParseClassFields(AType: TPasClassType; const AVisibility: TPasMemberVisibility; IsClassMember: Boolean);
    procedure ParseClassMembers(AType: TPasClassType);
    procedure ProcessMethod(AType: TPasClassType; IsClass : Boolean; AVisibility : TPasMemberVisibility);
    procedure ReadGenericArguments(List : TFPList;Parent : TPasElement; IsSpecialize : Boolean);
    function CheckProcedureArgs(Parent: TPasElement; Args: TFPList; Mandatory: Boolean): boolean;
    function CheckVisibility(S: String; out AVisibility: TPasMemberVisibility): Boolean;
    procedure ParseExc(const Msg: String);
    function OpLevel(t: TToken): Integer;
    Function TokenToExprOp (AToken : TToken) : TExprOpCode;
    function CreateElement(AClass: TPTreeElement; const AName: String; AParent: TPasElement): TPasElement;overload;
    function CreateElement(AClass: TPTreeElement; const AName: String; AParent: TPasElement; AVisibility: TPasMemberVisibility): TPasElement;overload;
    function CreateFunctionType(const AName, AResultName: String; AParent: TPasElement;
             UseParentAsResultParent: Boolean): TPasFunctionType;
    Function IsCurTokenHint(out AHint : TPasMemberHint) : Boolean; overload;
    Function IsCurTokenHint: Boolean; overload;
    Function TokenIsCallingConvention(Context : TPasProcedureType; S : String; out CC : TCallingConvention) : Boolean; virtual;
    Function TokenIsProcedureModifier(Context : TPasProcedureType; S : String; Out Pm : TProcedureModifier) : Boolean; virtual;
    Function CheckHint(Element : TPasElement; ExpectSemiColon : Boolean) : TPasMemberHints;
    function ParseParams(AParent : TPasElement;paramskind: TPasExprKind): TParamsExpr;
    function ParseExpIdent(AParent : TPasElement): TPasExpr;
    procedure DoParseClassType(AType: TPasClassType; SourceFileName: String; SourceLineNumber: Integer);
    function DoParseExpression(Aparent : TPaselement;InitExpr: TPasExpr=nil): TPasExpr;
    function DoParseConstValueExpression(AParent : TPasElement): TPasExpr;
    function CheckPackMode: TPackMode;
    // Overload handling
    procedure AddProcOrFunction(Decs: TPasDeclarations; AProc: TPasProcedure);
    function  CheckIfOverloaded(AParent: TPasElement; const AName: String): TPasElement;
  public
    constructor Create(AScanner: TPascalScanner; AFileResolver: TBaseFileResolver;  AEngine: TPasTreeContainer);
    // General parsing routines
    function CurTokenName: String;
    function CurTokenText: String;
    procedure NextToken; // read next non whitespace, non space
    procedure UngetToken;
    procedure ExpectToken(tk: TToken);
    function ExpectIdentifier: String;
    Function CurTokenIsIdentifier(Const S : String) : Boolean;
    // Expression parsing
    function isEndOfExp: Boolean;
    function ParseExpression(AParent : TPaselement; Kind: TExprKind=ek_Normal): String;
    // Type declarations
    function ParseComplexType(Parent : TPasElement = Nil): TPasType;
    function ParseTypeDecl(Parent: TPasElement): TPasType;
    function ParseType(Parent: TPasElement; Const TypeName : String = '';Full : Boolean = False): TPasType;
    function ParseProcedureType(Parent: TPasElement; const TypeName: String; const PT: TProcType): TPasProcedureType;
    function ParseStringType(Parent: TPasElement; const TypeName: String): TPasAliasType;
    function ParseSimpleType(Parent: TPasElement; Const TypeName: String; IsFull : Boolean = False): TPasType;
    function ParseAliasType(Parent: TPasElement; Const TypeName: String; Prefix: String ): TPasTypeAliasType;
    function ParsePointerType(Parent: TPasElement; Const TypeName: String): TPasPointerType;
    Function ParseArrayType(Parent : TPasElement; Const TypeName : String; PackMode : TPackMode) : TPasArrayType;
    Function ParseFileType(Parent : TPasElement; Const TypeName  : String) : TPasFileType;
    Function ParseRecordDecl(Parent: TPasElement; Const TypeName : string; const Packmode : TPackMode = pmNone) : TPasRecordType;
    function ParseEnumType(Parent: TPasElement; const TypeName: String): TPasEnumType;
    function ParseSetType(Parent: TPasElement; const TypeName: String ): TPasSetType;
    function ParseSpecializeType(Parent: TPasElement; Const TypeName: String): TPasClassType;
    Function ParseClassDecl(Parent: TPasElement; const AClassName: String;   AObjKind: TPasObjKind; PackMode : TPackMode= pmNone): TPasType;
    Function ParseProperty(Parent : TPasElement; Const AName : String; AVisibility : TPasMemberVisibility; IsClass : Boolean) : TPasProperty;
    function ParseRangeType(AParent: TPasElement; Const TypeName: String; Full : Boolean = True): TPasRangeType;
    // Constant declarations
    function ParseConstDecl(Parent: TPasElement): TPasConst;
    function ParseResourcestringDecl(Parent: TPasElement): TPasResString;
    // Variable handling. This includes parts of records
    procedure ParseVarDecl(Parent: TPasElement; List: TFPList);
    procedure ParseInlineVarDecl(Parent: TPasElement; List: TFPList;  AVisibility : TPasMemberVisibility  = visDefault; ClosingBrace: Boolean = False);
    // Main scope parsing
    procedure ParseMain(var Module: TPasModule);
    procedure ParseUnit(var Module: TPasModule);
    procedure ParseProgram(var Module: TPasModule);
    procedure ParseUsesList(ASection: TPasSection);
    procedure ParseInterface;
    procedure ParseImplementation;
    procedure ParseInitialization;
    procedure ParseFinalization;
    procedure ParseDeclarations(Declarations: TPasDeclarations);
    procedure ParseStatement(Parent: TPasImplBlock;  out NewImplElement: TPasImplElement);
    procedure ParseLabels(AParent: TPasElement);
    procedure ParseProcBeginBlock(Parent: TProcedureBody);
    // Function/Procedure declaration
    function  ParseProcedureOrFunctionDecl(Parent: TPasElement; ProcType: TProcType;AVisibility : TPasMemberVisibility = VisDefault): TPasProcedure;
    procedure ParseArgList(Parent: TPasElement; Args: TFPList; EndToken: TToken);
    procedure ParseProcedureOrFunctionHeader(Parent: TPasElement; Element: TPasProcedureType; ProcType: TProcType; OfObjectPossible: Boolean);
    procedure ParseProcedureBody(Parent: TPasElement);
    // Properties for external access
    property FileResolver: TBaseFileResolver read FFileResolver;
    property Scanner: TPascalScanner read FScanner;
    property Engine: TPasTreeContainer read FEngine;
    property CurToken: TToken read FCurToken;
    property CurTokenString: String read FCurTokenString;
    Property Options : TPOptions Read FOptions Write FOptions;
    Property CurModule : TPasModule Read FCurModule;
    Property LogEvents : TPParserLogEvents Read FLogEvents Write FLogEvents;
    Property OnLog : TPasParserLogHandler Read FOnLog Write FOnLog;
  end;

function ParseSource(AEngine: TPasTreeContainer;
                     const FPCCommandLine, OSTarget, CPUTarget: String;
                     UseStreams  : Boolean = False): TPasModule;
Function IsHintToken(T : String; Out AHint : TPasMemberHint) : boolean;
Function IsModifier(S : String; Out Pm : TProcedureModifier) : Boolean;
Function IsCallingConvention(S : String; out CC : TCallingConvention) : Boolean;

implementation

var
  IsIdentStart: array[char] of boolean;

const
  WhitespaceTokensToIgnore = [tkWhitespace, tkComment, tkLineEnding, tkTab];

type
  TDeclType = (declNone, declConst, declResourcestring, declType, declVar, declThreadvar, declProperty);

Function IsHintToken(T : String; Out AHint : TPasMemberHint) : boolean;

Const
   MemberHintTokens : Array[TPasMemberHint] of string =
     ('deprecated','library','platform','experimental','unimplemented');
Var
  I : TPasMemberHint;

begin
  t:=LowerCase(t);
  Result:=False;
  For I:=Low(TPasMemberHint) to High(TPasMemberHint) do
    begin
    result:=(t=MemberHintTokens[i]);
    if Result then
      begin
      aHint:=I;
      exit;
      end;
    end;
end;


Function IsCallingConvention(S : String; out CC : TCallingConvention) : Boolean;

Var
  CCNames : Array[TCallingConvention] of String
         = ('','register','pascal','cdecl','stdcall','oldfpccall','safecall');
Var
  C : TCallingConvention;

begin
  S:=Lowercase(s);
  Result:=False;
  for C:=Low(TCallingConvention) to High(TCallingConvention) do
    begin
    Result:=(CCNames[c]<>'') and (s=CCnames[c]);
    If Result then
      begin
      CC:=C;
      exit;
      end;
    end;
end;


Function IsModifier(S : String; Out Pm : TProcedureModifier) : Boolean;

Const
  ModifierNames : Array[TProcedureModifier] of string
                = ('virtual', 'dynamic','abstract', 'override',
                   'exported', 'overload', 'message', 'reintroduce',
                   'static','inline','assembler','varargs',
                   'compilerproc','external','forward');

Var
  P : TProcedureModifier;

begin
  S:=LowerCase(S);
  Result:=False;
  For P:=Low(TProcedureModifier) to High(TProcedureModifier) do
    begin
    Result:=s=ModifierNames[P];
    If Result then
      begin
      PM:=P;
      exit;
      end;
    end;
end;

function ParseSource(AEngine: TPasTreeContainer;
  const FPCCommandLine, OSTarget, CPUTarget: String;
  UseStreams  : Boolean = False): TPasModule;
var
  FileResolver: TFileResolver;
  Parser: TPasParser;
  Start, CurPos: PChar;
  Filename: String;
  Scanner: TPascalScanner;

  procedure ProcessCmdLinePart;
  var
    l: Integer;
    s: String;
  begin
    l := CurPos - Start;
    SetLength(s, l);
    if l > 0 then
      Move(Start^, s[1], l)
    else
      exit;
    if (s[1] = '-') and (length(s)>1) then
    begin
      case s[2] of
        'd': // -d define
          Scanner.AddDefine(UpperCase(Copy(s, 3, Length(s))));
        'F': // -F
          if (length(s)>2) and (s[3] = 'i') then // -Fi include path
            FileResolver.AddIncludePath(Copy(s, 4, Length(s)));
        'I': // -I include path
          FileResolver.AddIncludePath(Copy(s, 3, Length(s)));
        'S': // -S mode
          if  (length(s)>2) and (s[3]='d') then
            begin // -Sd mode delphi
              Parser.Options:=Parser.Options+[po_delphi];
            end;
      end;
    end else
      if Filename <> '' then
        raise Exception.Create(SErrMultipleSourceFiles)
      else
        Filename := s;
  end;

var
  s: String;
begin
  Result := nil;
  FileResolver := nil;
  Scanner := nil;
  Parser := nil;
  try
    FileResolver := TFileResolver.Create;
    FileResolver.UseStreams:=UseStreams;
    Scanner := TPascalScanner.Create(FileResolver);
    Scanner.AddDefine('FPK');
    Scanner.AddDefine('FPC');
    SCanner.LogEvents:=AEngine.ScannerLogEvents;
    SCanner.OnLog:=AEngine.Onlog;

    // TargetOS
    s := UpperCase(OSTarget);
    Scanner.AddDefine(s);
    if s = 'LINUX' then
      Scanner.AddDefine('UNIX')
    else if s = 'FREEBSD' then
    begin
      Scanner.AddDefine('BSD');
      Scanner.AddDefine('UNIX');
    end else if s = 'NETBSD' then
    begin
      Scanner.AddDefine('BSD');
      Scanner.AddDefine('UNIX');
    end else if s = 'SUNOS' then
    begin
      Scanner.AddDefine('SOLARIS');
      Scanner.AddDefine('UNIX');
    end else if s = 'GO32V2' then
      Scanner.AddDefine('DPMI')
    else if s = 'BEOS' then
      Scanner.AddDefine('UNIX')
    else if s = 'QNX' then
      Scanner.AddDefine('UNIX');

    // TargetCPU
    s := UpperCase(CPUTarget);
    Scanner.AddDefine('CPU'+s);
    if (s='x86_64') then
      Scanner.AddDefine('CPU64')
    else
      Scanner.AddDefine('CPU32');

    Parser := TPasParser.Create(Scanner, FileResolver, AEngine);
    Filename := '';
    Parser.LogEvents:=AEngine.ParserLogEvents;
    Parser.OnLog:=AEngine.Onlog;

    if FPCCommandLine<>'' then
      begin
        Start := @FPCCommandLine[1];
        CurPos := Start;
        while CurPos[0] <> #0 do
        begin
          if CurPos[0] = ' ' then
          begin
            ProcessCmdLinePart;
            Start := CurPos + 1;
          end;
          Inc(CurPos);
        end;
        ProcessCmdLinePart;
      end;

    if Filename = '' then
      raise Exception.Create(SErrNoSourceGiven);
    FileResolver.AddIncludePath(ExtractFilePath(FileName));
    Scanner.OpenFile(Filename);
    Parser.ParseMain(Result);
  finally
    Parser.Free;
    Scanner.Free;
    FileResolver.Free;
  end;
end;

{ ---------------------------------------------------------------------
  TPasTreeContainer
  ---------------------------------------------------------------------}

function TPasTreeContainer.CreateElement(AClass: TPTreeElement;
  const AName: String; AParent: TPasElement; const ASourceFilename: String;
  ASourceLinenumber: Integer): TPasElement;
begin
  Result := CreateElement(AClass, AName, AParent, visDefault, ASourceFilename,
    ASourceLinenumber);
end;

function TPasTreeContainer.CreateFunctionType(const AName, AResultName: String;
  AParent: TPasElement; UseParentAsResultParent: Boolean;
  const ASourceFilename: String; ASourceLinenumber: Integer): TPasFunctionType;
var
  ResultParent: TPasElement;
begin
  Result := TPasFunctionType(CreateElement(TPasFunctionType, AName, AParent,
    ASourceFilename, ASourceLinenumber));

  if UseParentAsResultParent then
    ResultParent := AParent
  else
    ResultParent := Result;

  TPasFunctionType(Result).ResultEl :=
    TPasResultElement(CreateElement(TPasResultElement, AResultName, ResultParent,
    ASourceFilename, ASourceLinenumber));
end;

function TPasTreeContainer.FindModule(const AName: String): TPasModule;
begin
  Result := nil;
end;

{ ---------------------------------------------------------------------
  EParserError
  ---------------------------------------------------------------------}

constructor EParserError.Create(const AReason, AFilename: String;
  ARow, AColumn: Integer);
begin
  inherited Create(AReason);
  FFilename := AFilename;
  FRow := ARow;
  FColumn := AColumn;
end;

{ ---------------------------------------------------------------------
  TPasParser
  ---------------------------------------------------------------------}

procedure TPasParser.ParseExc(const Msg: String);
begin
  raise EParserError.Create(Format(SParserErrorAtToken, [Msg, CurTokenName, Scanner.CurFilename, Scanner.CurRow, Scanner.CurColumn])
    {$ifdef addlocation}+' ('+inttostr(scanner.currow)+' '+inttostr(scanner.curcolumn)+')'{$endif},
    Scanner.CurFilename, Scanner.CurRow, Scanner.CurColumn);
end;

constructor TPasParser.Create(AScanner: TPascalScanner;
  AFileResolver: TBaseFileResolver; AEngine: TPasTreeContainer);
begin
  inherited Create;
  FScanner := AScanner;
  FFileResolver := AFileResolver;
  FEngine := AEngine;
end;

function TPasParser.CurTokenName: String;
begin
  if CurToken = tkIdentifier then
    Result := 'Identifier ' + FCurTokenString
  else
    Result := TokenInfos[CurToken];
end;

function TPasParser.CurTokenText: String;
begin
  case CurToken of
    tkIdentifier, tkString, tkNumber, tkChar:
      Result := FCurTokenString;
    else
      Result := TokenInfos[CurToken];
  end;
end;

procedure TPasParser.NextToken;
begin
  if FTokenBufferIndex < FTokenBufferSize then
  begin
    // Get token from buffer
    FCurToken := FTokenBuffer[FTokenBufferIndex];
    FCurTokenString := FTokenStringBuffer[FTokenBufferIndex];
    Inc(FTokenBufferIndex);
    //writeln('TPasParser.NextToken From Buf ',CurTokenText,' id=',FTokenBufferIndex);
  end else
  begin
    { We have to fetch a new token. But first check, wether there is space left
      in the token buffer.}
    if FTokenBufferSize = 2 then
    begin
      FTokenBuffer[0] := FTokenBuffer[1];
      FTokenStringBuffer[0] := FTokenStringBuffer[1];
      Dec(FTokenBufferSize);
      Dec(FTokenBufferIndex);
    end;
    // Fetch new token
    try
      repeat
        FCurToken := Scanner.FetchToken;
      until not (FCurToken in WhitespaceTokensToIgnore);
    except
      on e: EScannerError do
        raise EParserError.Create(e.Message,
          Scanner.CurFilename, Scanner.CurRow, Scanner.CurColumn);
    end;
    FCurTokenString := Scanner.CurTokenString;
    FTokenBuffer[FTokenBufferSize] := FCurToken;
    FTokenStringBuffer[FTokenBufferSize] := FCurTokenString;
    Inc(FTokenBufferSize);
    Inc(FTokenBufferIndex);
    //writeln('TPasParser.NextToken New ',CurTokenText,' id=',FTokenBufferIndex);
  end;
end;

procedure TPasParser.UngetToken;

begin
  if FTokenBufferIndex = 0 then
    ParseExc(SParserUngetTokenError)
  else begin
    Dec(FTokenBufferIndex);
    if FTokenBufferIndex>0 then
    begin
      FCurToken := FTokenBuffer[FTokenBufferIndex-1];
      FCurTokenString := FTokenStringBuffer[FTokenBufferIndex-1];
    end else begin
      FCurToken := tkWhitespace;
      FCurTokenString := '';
    end;
    //writeln('TPasParser.UngetToken ',CurTokenText,' id=',FTokenBufferIndex);
  end;
end;


procedure TPasParser.ExpectToken(tk: TToken);
begin
  NextToken;
  if CurToken <> tk then
    ParseExc(Format(SParserExpectTokenError, [TokenInfos[tk]]));
end;

function TPasParser.ExpectIdentifier: String;
begin
  ExpectToken(tkIdentifier);
  Result := CurTokenString;
end;

function TPasParser.CurTokenIsIdentifier(Const S: String): Boolean;
begin
  Result:=(Curtoken=tkidentifier) and (CompareText(S,CurtokenText)=0);
end;


Function TPasParser.IsCurTokenHint(out AHint : TPasMemberHint) : Boolean;
Var
  T : string;
begin
  Result:=CurToken=tklibrary;
  if Result then
    AHint:=hLibrary
  else if (CurToken=tkIdentifier) then
    Result:=IsHintToken(CurTokenString,ahint);
end;

Function TPasParser.IsCurTokenHint: Boolean;
var
  dummy : TPasMemberHint;
begin
  Result:=IsCurTokenHint(dummy);
end;

function TPasParser.TokenIsCallingConvention(Context: TPasProcedureType; S: String;
  out CC: TCallingConvention): Boolean;
begin
  Result:=IsCallingConvention(S,CC);
end;

function TPasParser.TokenIsProcedureModifier(Context: TPasProcedureType;
  S: String; out Pm: TProcedureModifier): Boolean;
begin
  Result:=IsModifier(S,PM);
end;


Function TPasParser.CheckHint(Element : TPasElement; ExpectSemiColon : Boolean) : TPasMemberHints;

Var
  Found : Boolean;
  h : TPasMemberHint;
  
begin
  Result:=[];
  Repeat
    NextToken;
    Found:=IsCurTokenHint(h);
    If Found then
      Include(Result,h)
  Until Not Found;
  UnGetToken;
  If Assigned(Element) then
    Element.Hints:=Result;
  if ExpectSemiColon then
    ExpectToken(tkSemiColon);
end;

Function TPasParser.CheckPackMode :  TPackMode;

begin
  NextToken;
  Case CurToken of
    tkPacked    : Result:=pmPacked;
    tkbitpacked : Result:=pmBitPacked;
  else
    result:=pmNone;
  end;
  if (Result<>pmNone) then
     begin
     NextToken;
     if Not (CurToken in [tkArray, tkRecord, tkObject, tkClass]) then
       ParseExc(Format(SParserExpectTokenError,['ARRAY, RECORD, OBJECT or CLASS']))
     end;
end;

Function IsSimpleTypeToken(Var AName : String) : Boolean;

Const
   SimpleTypeCount = 15;
   SimpleTypeNames : Array[1..SimpleTypeCount] of string =
     ('byte','boolean','char','integer','int64','longint','longword','double',
      'shortint','smallint','string','word','qword','cardinal','widechar');
   SimpleTypeCaseNames : Array[1..SimpleTypeCount] of string =
     ('Byte','Boolean','Char','Integer','Int64','LongInt','LongWord','Double',
     'ShortInt','SmallInt','String','Word','QWord','Cardinal','WideChar');

Var
  S : String;
  I : Integer;

begin
  S:=LowerCase(AName);
  I:=SimpleTypeCount;
  While (I>0) and (s<>SimpleTypeNames[i]) do
    Dec(I);
  Result:=(I>0);
  if Result Then
    AName:=SimpleTypeCaseNames[I];
end;

function TPasParser.ParseStringType(Parent : TPasElement; Const TypeName : String) : TPasAliasType;

Var
  S : String;

begin
  Result := TPasAliasType(CreateElement(TPasAliasType, TypeName, Parent));
  try
    NextToken;
    if CurToken=tkSquaredBraceOpen then
      begin
      S:='';
      NextToken;
      While Not (Curtoken in [tkSquaredBraceClose,tkEOF]) do
        begin
        S:=S+CurTokenString;
        NextToken;
        end;
      end
    else
      UngetToken;
    Result.DestType:=TPasStringType(CreateElement(TPasStringType,'string',Nil));
    TPasStringType(Result.DestType).LengthExpr:=S;
  except
    FreeAndNil(Result);
    Raise;
  end;
end;

function TPasParser.ParseSimpleType(Parent: TPasElement; Const TypeName : String; IsFull : Boolean = False): TPasType;

Type
  TSimpleTypeKind = (stkAlias,stkString,stkRange);

Var
  Ref: TPasElement;
  K : TSimpleTypeKind;
  Name,Prefix : String;
  E,SS : Boolean;
begin
  Name := CurTokenString;
  NextToken;
  if CurToken=tkDot then
    begin
    ExpectIdentifier;
    Prefix:=Name;
    Name := Name+'.'+CurTokenString;
    NextToken;
    end;
  // Current token is first token after identifier.
  if IsFull then
    begin
    if (CurToken=tkSemicolon) or isCurTokenHint then // Type A = B;
      K:=stkAlias
    else if (CurToken=tkSquaredBraceOpen) then // Type A = String[12];
      K:=stkString
    else // Type A = A..B;
      K:=stkRange;
    UnGetToken;
    end
  else
    begin // Type A = B;
    UnGetToken;
    K:=stkAlias;
    if (LowerCase(Name)='string') then
      K:=stkString;
    end;
  Case K of
    stkString:
      begin
      Result:=ParseStringType(Parent,TypeName);
      end;
    stkRange:
      begin
      UnGetToken;
      Result:=ParseRangeType(Parent,TypeName,False);
      end;
    stkAlias:
      begin
      Ref:=Nil;
      SS:=isSimpleTypeToken(Name);
      if not SS then
        Ref:=Engine.FindElement(Name);
      if (Ref=Nil) then
        Ref:=TPasUnresolvedTypeRef(CreateElement(TPasUnresolvedTypeRef,Name,Nil))
      else
        Ref.AddRef;
      if isFull then
        begin
        Result := TPasAliasType(CreateElement(TPasAliasType, TypeName, Parent));
        TPasAliasType(Result).DestType:=Ref as TPasType;
        end
      else
        Result:=Ref as TPasType
      end;
  end;
end;

// On entry, we're on the TYPE token
function TPasParser.ParseAliasType(Parent: TPasElement; Const TypeName: String;
  Prefix: String): TPasTypeAliasType;
begin
  Result := TPasTypeAliasType(CreateElement(TPasTypeAliasType, TypeName, Parent));
  try
    Result.DestType := ParseType(nil,'');
  except
    FreeAndNil(Result);
    raise;
  end;
end;

function TPasParser.ParsePointerType(Parent : TPasElement; Const TypeName : String) : TPasPointerType;

begin
  Result := TPasPointerType(CreateElement(TPasPointerType, TypeName, Parent));
  Try
    TPasPointerType(Result).DestType := ParseType(nil);
  except
    FreeAndNil(Result);
    Raise;
  end;
end;

function TPasParser.ParseEnumType(Parent : TPasElement; Const TypeName : String) : TPasEnumType;

Var
  EnumValue: TPasEnumValue;

begin
  Result := TPasEnumType(CreateElement(TPasEnumType, TypeName, Parent));
  try
    while True do
      begin
      NextToken;
      EnumValue := TPasEnumValue(CreateElement(TPasEnumValue, CurTokenString, Result));
      Result.Values.Add(EnumValue);
      NextToken;
      if CurToken = tkBraceClose then
        break
      else if CurToken in [tkEqual,tkAssign] then
        begin
        EnumValue.AssignedValue:=ParseExpression(Result);
        NextToken;
        if CurToken = tkBraceClose then
          Break
        else if not (CurToken=tkComma) then
          ParseExc(SParserExpectedCommaRBracket);
        end
      else if not (CurToken=tkComma) then
        ParseExc(SParserExpectedCommaRBracket)
      end;
  except
    FreeAndNil(Result);
    Raise;
  end;
end;

function TPasParser.ParseSetType(Parent: TPasElement; Const TypeName : String): TPasSetType;

begin
  Result := TPasSetType(CreateElement(TPasSetType, TypeName, Parent));
  try
    ExpectToken(tkOf);
    Result.EnumType := ParseType(Result);
  except
    Result.Free;
    raise;
  end;
end;

function TPasParser.ParseType(Parent: TPasElement; Const TypeName : String = ''; Full : Boolean =  False): TPasType;

Const
  // These types are allowed only when full type declarations
  FullTypeTokens = [tkGeneric,tkSpecialize,tkClass,tkInterface,tkType];
  // Parsing of these types already takes care of hints
  NoHintTokens = [tkClass,tkObject,tkInterface,tkProcedure,tkFunction];
var
  Name, s: String;
  PM : TPackMode;
  CH : Boolean; // Check hint ?
begin
  Result := nil;
  Pm:=CheckPackMode;
  if Full then
    CH:=Not (CurToken in NoHintTokens)
  else
    begin
    CH:=False;
    if (CurToken in FullTypeTokens) then
      ParseExc('Type '+CurtokenText+' not allowed here');
    end;
  Try
    case CurToken of
      // types only allowed when full
      tkObject: Result := ParseClassDecl(Parent, TypeName, okObject,PM);
      tkInterface: Result := ParseClassDecl(Parent, TypeName, okInterface);
      tkSpecialize: Result:=ParseSpecializeType(Parent,TypeName);
      tkClass: Result := ParseClassDecl(Parent, TypeName, okClass, PM);
      tkType: Result:=ParseAliasType(Parent,TypeName,'');
      // Always allowed
      tkIdentifier: Result:=ParseSimpleType(Parent,TypeName,Full);
      tkCaret: Result:=ParsePointerType(Parent,TypeName);
      tkFile: Result:=ParseFileType(Parent,TypeName);
      tkArray: Result:=ParseArrayType(Parent,TypeName,pm);
      tkBraceOpen: Result:=ParseEnumType(Parent,TypeName);
      tkSet: Result:=ParseSetType(Parent,TypeName);
      tkProcedure: Result:=ParseProcedureType(Parent,TypeName,ptProcedure);
      tkFunction: Result:=ParseProcedureType(Parent,TypeName,ptFunction);
      tkRecord: Result := ParseRecordDecl(Parent,TypeName,PM);
    else
      UngetToken;
      Result:=ParseRangeType(Parent,TypeName,Full);
    end;
    if CH then
      CheckHint(Result,True);
  Except
    FreeAndNil(Result);
    Raise;
  end;
end;

function TPasParser.ParseComplexType(Parent : TPasElement = Nil): TPasType;
begin
  NextToken;
  case CurToken of
    tkProcedure:
      begin
        Result := TPasProcedureType(CreateElement(TPasProcedureType, '', Parent));
        ParseProcedureOrFunctionHeader(Result, TPasProcedureType(Result), ptProcedure, True);
        if CurToken = tkSemicolon then
          UngetToken;        // Unget semicolon
      end;
    tkFunction:
      begin
        Result := CreateFunctionType('', 'Result', Parent, False);
        ParseProcedureOrFunctionHeader(Result, TPasFunctionType(Result), ptFunction, True);
        if CurToken = tkSemicolon then
          UngetToken;        // Unget semicolon
      end;
  else
    UngetToken;
    Result := ParseType(Parent);
  end;
end;

Function TPasParser.ParseArrayType(Parent : TPasElement; Const TypeName : String; PackMode : TPackMode) : TPasArrayType;

Var
  S : String;

begin
  Result := TPasArrayType(CreateElement(TPasArrayType, TypeName, Parent));
  try
    Result.PackMode:=PackMode;
    NextToken;
    S:='';
    case CurToken of
      tkSquaredBraceOpen:
        begin
          repeat
            NextToken;
            if CurToken<>tkSquaredBraceClose then
              S:=S+CurTokenText;
          until CurToken = tkSquaredBraceClose;
          Result.IndexRange:=S;
          ExpectToken(tkOf);
          Result.ElType := ParseType(nil);
        end;
      tkOf:
        begin
          NextToken;
          if CurToken = tkConst then
          else
          begin
            UngetToken;
              Result.ElType := ParseType(nil);
          end
        end
      else
        ParseExc(SParserArrayTypeSyntaxError);
    end;
  except
    FreeAndNil(Result);
    Raise;
  end;
end;

Function TPasParser.ParseFileType(Parent : TPasElement; Const TypeName  : String) : TPasFileType;


begin
  Result:=TPasFileType(CreateElement(TPasFileType, TypeName, Parent));
  NextToken;
  If CurToken=tkOf then
    Result.ElType := ParseType(nil)
  else 
   ungettoken;
end;

function TPasParser.isEndOfExp:Boolean;
const
  EndExprToken = [
    tkEOF, tkBraceClose, tkSquaredBraceClose, tkSemicolon, tkComma, tkColon,
    tkdo, tkdownto, tkelse, tkend, tkof, tkthen, tkto
  ];
begin
  Result:=(CurToken in EndExprToken) or IsCurTokenHint;
end;

function TPasParser.ParseParams(AParent: TPasElement;paramskind: TPasExprKind): TParamsExpr;
var
  params  : TParamsExpr;
  p       : TPasExpr;
  PClose  : TToken;
begin
  Result:=nil;
  if paramskind in [pekArrayParams, pekSet] then begin
    if CurToken<>tkSquaredBraceOpen then Exit;
    PClose:=tkSquaredBraceClose;
  end else begin
    if CurToken<>tkBraceOpen then Exit;
    PClose:=tkBraceClose;
  end;

  params:=TParamsExpr.Create(AParent,paramskind);
  try
    NextToken;
    if not isEndOfExp then begin
      repeat
        p:=DoParseExpression(AParent);
        if not Assigned(p) then Exit; // bad param syntax
        params.AddParam(p);

        if not (CurToken in [tkComma, PClose]) then begin
          Exit;
        end;

        if CurToken = tkComma then begin
          NextToken;
          if CurToken = PClose then begin
            //ErrorExpected(parser, 'identifier');
            Exit;
          end;
        end;
      until CurToken=PClose;
    end;
    NextToken;
    Result:=params;
  finally
    if not Assigned(Result) then params.Free;
  end;
end;

Function TPasParser.TokenToExprOp (AToken : TToken) : TExprOpCode;

begin
  Case AToken of
    tkMul                   : Result:=eopMultiply;
    tkPlus                  : Result:=eopAdd;
    tkMinus                 : Result:=eopSubtract;
    tkDivision              : Result:=eopDivide;
    tkLessThan              : Result:=eopLessThan;
    tkEqual                 : Result:=eopEqual;
    tkGreaterThan           : Result:=eopGreaterThan;
    tkAt                    : Result:=eopAddress;
    tkNotEqual              : Result:=eopNotEqual;
    tkLessEqualThan         : Result:=eopLessthanEqual;
    tkGreaterEqualThan      : Result:=eopGreaterThanEqual;
    tkPower                 : Result:=eopPower;
    tkSymmetricalDifference : Result:=eopSymmetricalDifference;                                                                                              
    tkIs                    : Result:=eopIs;
    tkAs                    : Result:=eopAs;
    tkSHR                   : Result:=eopSHR;
    tkSHL                   : Result:=eopSHL;
    tkAnd                   : Result:=eopAnd;
    tkOr                    : Result:=eopOR;
    tkXor                   : Result:=eopXOR;
    tkMod                   : Result:=eopMod;
    tkDiv                   : Result:=eopDiv;
    tkNot                   : Result:=eopNot;
    tkIn                    : Result:=eopIn;
    tkDot                   : Result:=eopSubIdent;
    tkCaret                 : Result:=eopDeref;
  else
    ParseExc(format('Not an operand: (%d : %s)',[AToken,TokenInfos[AToken]]));
  end;
end;
 
function TPasParser.ParseExpIdent(AParent : TPasElement):TPasExpr;
var
  x       : TPasExpr;
  prm     : TParamsExpr;
  u       : TUnaryExpr;
  b       : TBinaryExpr;
  optk    : TToken;
begin
  Result:=nil;
  case CurToken of
    tkString:           x:=TPrimitiveExpr.Create(AParent,pekString, CurTokenString);
    tkChar:             x:=TPrimitiveExpr.Create(AParent,pekString, CurTokenText);
    tkNumber:           x:=TPrimitiveExpr.Create(AParent,pekNumber, CurTokenString);
    tkIdentifier:       x:=TPrimitiveExpr.Create(AParent,pekIdent, CurTokenText);
    tkfalse, tktrue:    x:=TBoolConstExpr.Create(Aparent,pekBoolConst, CurToken=tktrue);
    tknil:              x:=TNilExpr.Create(Aparent);
    tkSquaredBraceOpen: x:=ParseParams(AParent,pekSet);
    tkinherited: begin
      //inherited; inherited function
      x:=TInheritedExpr.Create(AParent);
      NextToken;
      if (length(CurTokenText)>0) and (CurTokenText[1] in ['A'..'_']) then begin
        b:=TBinaryExpr.Create(AParent,x, DoParseExpression(AParent), eopNone);
        if not Assigned(b.right) then
          begin
          B.Free;
          Exit; // error
          end;
        x:=b;
        UngetToken;
      end
       else UngetToken;
    end;
    tkself: begin
      //x:=TPrimitiveExpr.Create(AParent,pekString, CurTokenText); //function(self);
      x:=TSelfExpr.Create(AParent);
      NextToken;
      if CurToken = tkDot then begin // self.Write(EscapeText(AText));
        optk:=CurToken;
        NextToken;
        b:=TBinaryExpr.Create(AParent,x, ParseExpIdent(AParent), TokenToExprOp(optk));
        if not Assigned(b.right) then
          begin
          B.Free;
          Exit; // error
          end;
        x:=b;
      end
       else UngetToken;
    end;
    tkAt: begin
      // P:=@function;
      NextToken;
      if (length(CurTokenText)=0) or not (CurTokenText[1] in ['A'..'_']) then begin
        UngetToken;
        ParseExc(SParserExpectedIdentifier);
      end;
      x:=TPrimitiveExpr.Create(AParent,pekString, '@'+CurTokenText);
    end;
    tkCaret: begin
      // ^A..^_ characters. See #16341
      NextToken;
      if not (length(CurTokenText)=1) or not (CurTokenText[1] in ['A'..'_']) then begin
        UngetToken;
        ParseExc(SParserExpectedIdentifier);
      end;
      x:=TPrimitiveExpr.Create(AParent,pekString, '^'+CurTokenText);
    end;
  else
    ParseExc(SParserExpectedIdentifier);
  end;

  if x.Kind<>pekSet then NextToken;

  try
    if x.Kind=pekIdent then begin
      while CurToken in [tkBraceOpen, tkSquaredBraceOpen, tkCaret] do
        case CurToken of
          tkBraceOpen: begin
            prm:=ParseParams(AParent,pekFuncParams);
            if not Assigned(prm) then Exit;
            prm.Value:=x;
            x:=prm;
          end;
          tkSquaredBraceOpen: begin
            prm:=ParseParams(AParent,pekArrayParams);
            if not Assigned(prm) then Exit;
            prm.Value:=x;
            x:=prm;
          end;
          tkCaret: begin
            u:=TUnaryExpr.Create(AParent,x, TokenToExprOp(CurToken));
            x:=u;
            NextToken;
          end;
        end;

      if CurToken in [tkDot, tkas] then begin
        optk:=CurToken;
        NextToken;
        b:=TBinaryExpr.Create(AParent,x, ParseExpIdent(AParent), TokenToExprOp(optk));
        if not Assigned(b.right) then
          begin
          b.free;
          Exit; // error
          end;
        x:=b;
      end;
    end;

    if CurToken = tkDotDot then begin
      NextToken;
      b:=TBinaryExpr.CreateRange(AParent,x, DoParseExpression(AParent));
      if not Assigned(b.right) then
        begin
        b.free;
        Exit; // error
        end;
      x:=b;
    end;

    Result:=x;
  finally
    if not Assigned(Result) then x.Free;
  end;
end;

function TPasParser.OpLevel(t: TToken): Integer;
begin
  case t of
    tknot,tkAt:
      Result:=4;
    tkMul, tkDivision, tkdiv, tkmod, tkand, tkShl,tkShr, tkas, tkPower :
      Result:=3;
    tkPlus, tkMinus, tkor, tkxor:
      Result:=2;
    tkEqual, tkNotEqual, tkLessThan, tkLessEqualThan, tkGreaterThan, tkGreaterEqualThan, tkin, tkis:
      Result:=1;
  else
    Result:=0;
  end;
end;

function TPasParser.DoParseExpression(Aparent : TPaselement;InitExpr: TPasExpr): TPasExpr;
var
  expstack  : TFPList;
  opstack   : TFPList;
  pcount    : Integer;
  x         : TPasExpr;
  i         : Integer;
  tempop    : TToken;
  NotBinary : Boolean;
  
const
  PrefixSym = [tkPlus, tkMinus, tknot, tkAt]; // + - not @
  BinaryOP  = [tkMul, tkDivision, tkdiv, tkmod, tkDotDot,
               tkand, tkShl,tkShr, tkas, tkPower,
               tkPlus, tkMinus, tkor, tkxor, tkSymmetricalDifference,
               tkEqual, tkNotEqual, tkLessThan, tkLessEqualThan,
               tkGreaterThan, tkGreaterEqualThan, tkin, tkis];

  function PopExp: TPasExpr; inline;
  begin
    if expstack.Count>0 then begin
      Result:=TPasExpr(expstack[expstack.Count-1]);
      expstack.Delete(expstack.Count-1);
    end else
      Result:=nil;
  end;

  procedure PushOper(token: TToken); inline;
  begin
    opstack.Add( Pointer(PtrInt(token)) );
  end;

  function PeekOper: TToken; inline;
  begin
    if opstack.Count>0 then Result:=TToken(PtrUInt(opstack[ opstack.Count-1]))
    else Result:=tkEOF
  end;

  function PopOper: TToken; inline;
  begin
    Result:=PeekOper;
    if Result<>tkEOF then opstack.Delete(opstack.Count-1);
  end;

  procedure PopAndPushOperator;
  var
    t       : TToken;
    xright  : TPasExpr;
    xleft   : TPasExpr;
  begin
    t:=PopOper;
    xright:=PopExp;
    xleft:=PopExp;
    expstack.Add(TBinaryExpr.Create(AParent,xleft, xright, TokenToExprOp(t)));
  end;

begin
  Result:=nil;
  expstack := TFPList.Create;
  opstack := TFPList.Create;
  try
    repeat
      NotBinary:=True;
      pcount:=0;
      if not Assigned(InitExpr) then
      begin
        // the first part of the expression has been parsed externally.
        // this is used by Constant Expresion parser (CEP) parsing only,
        // whenever it makes a false assuming on constant expression type.
        // i.e: SI_PAD_SIZE = ((128/sizeof(longint)) - 3);
        //
        // CEP assumes that it's array or record, because the expression
        // starts with "(". After the first part is parsed, the CEP meets "-"
        // that assures, it's not an array expression. The CEP should give the
        // first part back to the expression parser, to get the correct
        // token tree according to the operations priority.
        //
        // quite ugly. type information is required for CEP to work clean

        while CurToken in PrefixSym do begin
          PushOper(CurToken);
          inc(pcount);
          NextToken;
        end;

        if CurToken = tkBraceOpen then begin
          NextToken;
          x:=DoParseExpression(AParent);
          if CurToken<>tkBraceClose then
            begin
            x.free;
            Exit;
            end;
          NextToken;

          // for the expression like  (TObject(m)).Free;
          if CurToken = tkDot then begin
            NextToken;
            x:=TBinaryExpr.Create(AParent,x, ParseExpIdent(AParent), TokenToExprOp(tkDot));
          end;

        end else begin
          x:=ParseExpIdent(AParent);
        end;

        if not Assigned(x) then Exit;
        expstack.Add(x);

        for i:=1 to pcount do begin
          tempop:=PopOper;
          x:=popexp;
          if (tempop=tkMinus) and (X.Kind=pekRange) then
            begin
            TBinaryExpr(x).Left:=TUnaryExpr.Create(x, TBinaryExpr(X).left, eopSubtract);
            expstack.Add(x);
            end
           else
            expstack.Add( TUnaryExpr.Create(AParent, PopExp, TokenToExprOp(tempop) ));
        end;

      end else
      begin
        expstack.Add(InitExpr);
        InitExpr:=nil;
      end;
      if (CurToken in BinaryOP) then begin
        // Adjusting order of the operations
        NotBinary:=False;
        tempop:=PeekOper;
        while (opstack.Count>0) and (OpLevel(tempop)>=OpLevel(CurToken)) do begin
          PopAndPushOperator;
          tempop:=PeekOper;
        end;
        PushOper(CurToken);
        NextToken;
      end;

    until NotBinary or isEndOfExp;

    if not NotBinary then ParseExc(SParserExpectedIdentifier);

    while opstack.Count>0 do PopAndPushOperator;

    // only 1 expression should be on the stack, at the end of the correct expression
    if expstack.Count=1 then Result:=TPasExpr(expstack[0]);

  finally
    if not Assigned(Result) then begin
      // expression error!
      for i:=0 to expstack.Count-1 do
        TObject(expstack[i]).Free;
    end;
    opstack.Free;
    expstack.Free;
  end;
end;

function TPasParser.ParseExpression(AParent: TPaselement; Kind: TExprKind
  ): String;
var
  BracketLevel: Integer;
  LastTokenWasWord: Boolean;
  ls: String;
begin
  SetLength(Result, 0);
  BracketLevel := 0;
  LastTokenWasWord := false;
  while True do
  begin
    NextToken;
    { !!!: Does not detect when normal brackets and square brackets are mixed
      in a wrong way. }
    if CurToken in [tkBraceOpen, tkSquaredBraceOpen] then
      Inc(BracketLevel)
    else if CurToken in [tkBraceClose, tkSquaredBraceClose] then
    begin
      if BracketLevel = 0 then
        break;
      Dec(BracketLevel);
    end else if (BracketLevel = 0) then 
    begin
      if (CurToken in [tkComma, tkSemicolon,
        tkColon, tkDotDot, tkthen, tkend, tkelse, tkuntil, tkfinally, tkexcept,
        tkof, tkbegin, tkdo, tkto, tkdownto, tkinitialization, tkfinalization])
      then
        break;
        
      if (Kind=ek_PropertyIndex) and (CurToken=tkIdentifier) then begin
        ls:=LowerCase(CurTokenText);
        if (ls='read') or (ls ='write') or (ls='default') or (ls='nodefault') or (ls='implements') then
          Break;
      end;
        
    end;

    if (CurTokenString<>'') and IsIdentStart[CurTokenString[1]] then
      begin
      if LastTokenWasWord then
        Result := Result + ' ';
      LastTokenWasWord:=true;
      end
    else
      LastTokenWasWord:=false;
    if CurToken=tkString then
      begin
      If (Length(CurTokenText)>0) and (CurTokenText[1]=#0) then
        Raise Exception.Create('First char is null : "'+CurTokenText+'"');
      Result := Result + ''''+StringReplace(CurTokenText,'''','''''',[rfReplaceAll])+''''
      end
    else
      Result := Result + CurTokenText;
  end;
  if Result='' then
    ParseExc(SParserSyntaxError);
  UngetToken;
end;

function GetExprIdent(p: TPasExpr): String;
begin
  if Assigned(p) and (p is TPrimitiveExpr) and (p.Kind=pekIdent) then
    Result:=TPrimitiveExpr(p).Value
  else
    Result:='';
end;

function TPasParser.DoParseConstValueExpression(AParent: TPasElement): TPasExpr;
var
  x : TPasExpr;
  n : AnsiString;
  r : TRecordValues;
  a : TArrayValues;

function lastfield:boolean;

begin
  result:= CurToken<>tkSemicolon;
  if not result then
   begin
     nexttoken;
     if curtoken=tkbraceclose then
       result:=true
     else
       ungettoken;
   end; 
end;

begin
  if CurToken <> tkBraceOpen then
    Result:=DoParseExpression(AParent)
  else begin
    NextToken;
    x:=DoParseConstValueExpression(Aparent);
    case CurToken of
      tkComma: // array of values (a,b,c);
        begin
          a:=TArrayValues.Create(AParent);
          a.AddValues(x);
          repeat
            NextToken;
            x:=DoParseConstValueExpression(AParent);
            a.AddValues(x);
          until CurToken<>tkComma;
          Result:=a;
        end;

      tkColon: // record field (a:xxx;b:yyy;c:zzz);
        begin
          n:=GetExprIdent(x);
          x.Free;
          r:=TRecordValues.Create(AParent);
          NextToken;
          x:=DoParseConstValueExpression(AParent);
          r.AddField(n, x);
          if not lastfield then
            repeat
              n:=ExpectIdentifier;
              ExpectToken(tkColon);
              NextToken;
              x:=DoParseConstValueExpression(AParent);
              r.AddField(n, x)
            until lastfield; // CurToken<>tkSemicolon;
          Result:=r;
        end;
    else
      // Binary expression!  ((128 div sizeof(longint)) - 3);       ;
      Result:=DoParseExpression(AParent,x);
      if CurToken<>tkBraceClose then ParseExc(SParserExpectedCommaRBracket);
      NextToken;
      if CurToken <> tkSemicolon then // the continue of expresion
        Result:=DoParseExpression(AParent,Result);
      Exit;
    end;
    if CurToken<>tkBraceClose then ParseExc(SParserExpectedCommaRBracket);
    NextToken;
  end;
end;

Function TPasParser.CheckOverloadList(AList : TFPList; AName : String; Out OldMember : TPasElement) : TPasOverloadedProc;

Var
  I : Integer;

begin
  Result:=Nil;
  I:=0;
  While (Result=Nil) and (I<AList.Count) do
    begin
    OldMember:=TPasElement(AList[i]);
    if CompareText(OldMember.Name, AName) = 0 then
      begin
      if OldMember is TPasOverloadedProc then
        Result:=TPasOverloadedProc(OldMember)
      else
        begin
        Result:=TPasOverloadedProc.Create(AName, OldMember.Parent);
        Result.Overloads.Add(OldMember);
        AList[i] := Result;
        end;
      end;
    Inc(I);
    end;
  If Result=Nil then
    OldMember:=Nil;
end;

procedure TPasParser.AddProcOrFunction(Decs: TPasDeclarations;
  AProc: TPasProcedure);
var
  I : Integer;
  OldMember: TPasElement;
  OverloadedProc: TPasOverloadedProc;
begin
  With Decs do
    begin
    OverloadedProc:=CheckOverloadList(Functions,AProc.Name,OldMember);
    If (OverloadedProc<>Nil) then
      begin
      OverLoadedProc.Overloads.Add(AProc);
      if (OldMember<>OverloadedProc) then
        begin
        I:=Declarations.IndexOf(OldMember);
        If I<>-1 then
          Declarations[i]:=OverloadedProc;
        end;
      end
    else
      begin
      Declarations.Add(AProc);
      Functions.Add(AProc);
      end;
    end;
end;

// Return the parent of a function declaration. This is APArent,
// except when AParent is a class, and the function is overloaded.
// Then the parent is the overload object.
function TPasParser.CheckIfOverloaded(AParent: TPasElement; const AName: String): TPasElement;
var
  Member: TPasElement;
  OverloadedProc: TPasOverloadedProc;

begin
  Result:=AParent;
  If AParent is TPasClassType then
    begin
    OverloadedProc:=CheckOverLoadList(TPasClassType(AParent).Members,AName,Member);
    If (OverloadedProc<>Nil) then
      Result:=OverloadedProc;
    end;
end;


procedure TPasParser.ParseMain(var Module: TPasModule);
begin
  Module:=nil;
  NextToken;
  case CurToken of
    tkUnit: ParseUnit(Module);
    tkProgram: ParseProgram(Module);
    else
      ParseExc(Format(SParserExpectTokenError, ['unit']));
  end;
end;

// Starts after the "unit" token
procedure TPasParser.ParseUnit(var Module: TPasModule);
begin
  Module := nil;
  Module := TPasModule(CreateElement(TPasModule, ExpectIdentifier,
    Engine.Package));
  FCurModule:=Module;
  try
    if Assigned(Engine.Package) then
    begin
      Module.PackageName := Engine.Package.Name;
      Engine.Package.Modules.Add(Module);
    end;
    CheckHint(Module,True);
//    ExpectToken(tkSemicolon);
    ExpectToken(tkInterface);
    If LogEvent(pleInterface) then
      DoLog(SLogStartInterface );
    ParseInterface;
  finally
    FCurModule:=nil;
  end;
end;

// Starts after the "program" token
procedure TPasParser.ParseProgram(var Module: TPasModule);
begin
  Module := nil;
  Module := TPasModule(CreateElement(TPasProgram, ExpectIdentifier,
    Engine.Package));
  FCurModule:=Module;
  try
    if Assigned(Engine.Package) then
    begin
      Module.PackageName := Engine.Package.Name;
      Engine.Package.Modules.Add(Module);
    end;
    NextToken;
    ParseImplementation;
  finally
    FCurModule:=nil;
  end;
end;

// Starts after the "interface" token
procedure TPasParser.ParseInterface;
var
  Section: TInterfaceSection;
begin
  Section := TInterfaceSection(CreateElement(TInterfaceSection, '', CurModule));
  CurModule.InterfaceSection := Section;
  ParseDeclarations(Section);
end;

// Starts after the "implementation" token
procedure TPasParser.ParseImplementation;
var
  Section: TImplementationSection;
begin
  Section := TImplementationSection(CreateElement(TImplementationSection, '', CurModule));
  CurModule.ImplementationSection := Section;
  ParseDeclarations(Section);
end;

procedure TPasParser.ParseInitialization;
var
  Section: TInitializationSection;
  SubBlock: TPasImplElement;
begin
  Section := TInitializationSection(CreateElement(TInitializationSection, '', CurModule));
  CurModule.InitializationSection := Section;
  repeat
    NextToken;
    if (CurToken=tkend) then
    begin
      ExpectToken(tkDot);
      exit;
    end
    else if (CurToken=tkfinalization) then
    begin
      ParseFinalization;
      exit;
    end
    else if CurToken<>tkSemiColon then
    begin
      UngetToken;
      ParseStatement(Section,SubBlock);
      if SubBlock=nil then
        ExpectToken(tkend);
    end;
  until false;
end;

procedure TPasParser.ParseFinalization;
var
  Section: TFinalizationSection;
  SubBlock: TPasImplElement;
begin
  Section := TFinalizationSection(CreateElement(TFinalizationSection, '', CurModule));
  CurModule.FinalizationSection := Section;
  repeat
    NextToken;
    if (CurToken=tkend) then
    begin
      ExpectToken(tkDot);
      exit;
    end
    else if CurToken<>tkSemiColon then
    begin
      UngetToken;
      ParseStatement(Section,SubBlock);
      if SubBlock=nil then
        ExpectToken(tkend);
    end;
  until false;
  UngetToken;
end;

Function TPasParser.GetProcTypeFromToken(tk : TToken; IsClass : Boolean = False) : TProcType;

begin
  Case tk of
    tkProcedure :
      if IsClass then
        Result:=ptClassProcedure
      else
        Result:=ptProcedure;
    tkFunction:
      if IsClass then
        Result:=ptClassFunction
      else
        Result:=ptFunction;
    tkConstructor:
      Result:=ptConstructor;
    tkDestructor:
      Result:=ptDestructor;
    tkOperator:
      Result:=ptOperator;
  else
    ParseExc(SParserNotAProcToken);
  end;
end;

procedure TPasParser.ParseDeclarations(Declarations: TPasDeclarations);
var
  CurBlock: TDeclType;
  ConstEl: TPasConst;
  ResStrEl: TPasResString;
  TypeEl: TPasType;
  ClassEl: TPasClassType;
  List: TFPList;
  i,j: Integer;
  VarEl: TPasVariable;
  PropEl : TPasProperty;
  TypeName: String;
  PT : TProcType;

begin
  CurBlock := declNone;
  while True do
  begin
    NextToken;
    //writeln('TPasParser.ParseSection Token=',Scanner.CurTokenString,' ',CurToken);
    case CurToken of
      tkend:
        begin
        ExpectToken(tkDot);
        break;
        end;
      tkimplementation:
        if (CurToken = tkImplementation) and (Declarations is TInterfaceSection) then
          begin
          If Not Engine.InterfaceOnly then
            begin
            If LogEvent(pleImplementation) then
              DoLog(SLogStartImplementation);
            ParseImplementation;
            end;
          break;
          end;
      tkinitialization:
        if (Declarations is TInterfaceSection)
        or (Declarations is TImplementationSection) then
          begin
          ParseInitialization;
          break;
          end;
      tkfinalization:
        if (Declarations is TInterfaceSection)
        or (Declarations is TImplementationSection) then
          begin
          ParseFinalization;
          break;
          end;
      tkUses:
        if Declarations is TPasSection then
          ParseUsesList(TPasSection(Declarations))
        else
          ParseExc(SParserSyntaxError);
      tkConst:
        CurBlock := declConst;
      tkResourcestring:
        CurBlock := declResourcestring;
      tkType:
        CurBlock := declType;
      tkVar:
        CurBlock := declVar;
      tkThreadVar:
        CurBlock := declThreadVar;
      tkProperty:
        CurBlock := declProperty;
      tkProcedure, tkFunction, tkConstructor, tkDestructor,tkOperator:
        begin
        pt:=GetProcTypeFromToken(CurToken);
        AddProcOrFunction(Declarations, ParseProcedureOrFunctionDecl(Declarations, pt));
        CurBlock := declNone;
        end;
      tkClass:
        begin
          NextToken;
          If CurToken in [tkprocedure,tkFunction] then
            begin
            pt:=GetProcTypeFromToken(CurToken,True);
            AddProcOrFunction(Declarations,ParseProcedureOrFunctionDecl(Declarations, pt));
            CurBlock := declNone;
            end
          else
            ExpectToken(tkprocedure);
        end;
      tkIdentifier:
        begin
          case CurBlock of
            declConst:
              begin
                ConstEl := ParseConstDecl(Declarations);
                Declarations.Declarations.Add(ConstEl);
                Declarations.Consts.Add(ConstEl);
              end;
            declResourcestring:
              begin
                ResStrEl := ParseResourcestringDecl(Declarations);
                Declarations.Declarations.Add(ResStrEl);
                Declarations.ResStrings.Add(ResStrEl);
              end;
            declType:
              begin
                TypeEl := ParseTypeDecl(Declarations);
                if Assigned(TypeEl) then        // !!!
                begin
                  Declarations.Declarations.Add(TypeEl);
                  if TypeEl.ClassType = TPasClassType then
                  begin
                    // Remove previous forward declarations, if necessary
                    for i := 0 to Declarations.Classes.Count - 1 do
                    begin
                      ClassEl := TPasClassType(Declarations.Classes[i]);
                      if CompareText(ClassEl.Name, TypeEl.Name) = 0 then
                      begin
                        Declarations.Classes.Delete(i);
                        for j := 0 to Declarations.Declarations.Count - 1 do
                          if CompareText(TypeEl.Name,
                            TPasElement(Declarations.Declarations[j]).Name) = 0 then
                          begin
                            Declarations.Declarations.Delete(j);
                            break;
                          end;
                        ClassEl.Release;
                        break;
                      end;
                    end;
                    // Add the new class to the class list
                    Declarations.Classes.Add(TypeEl)
                  end else
                    Declarations.Types.Add(TypeEl);
                end;
              end;
            declVar, declThreadVar:
              begin
                List := TFPList.Create;
                try
                  try
                    ParseVarDecl(Declarations, List);
                  except
                    for i := 0 to List.Count - 1 do
                      TPasVariable(List[i]).Release;
                    raise;
                  end;
                  for i := 0 to List.Count - 1 do
                  begin
                    VarEl := TPasVariable(List[i]);
                    Declarations.Declarations.Add(VarEl);
                    Declarations.Variables.Add(VarEl);
                  end;
                finally
                  List.Free;
                end;
              end;
            declProperty:
              begin
              PropEl:=ParseProperty(Declarations,CurtokenString,visDefault,False);
              Declarations.Declarations.Add(PropEl);
              Declarations.properties.add(PropEl);
              end;
          else
            ParseExc(SParserSyntaxError);
          end;
        end;
      tkGeneric:
        begin
          if CurBlock <> declType then
            ParseExc(SParserSyntaxError);
          TypeName := ExpectIdentifier;
          ClassEl := TPasClassType(Engine.CreateElement(TPasClassType,TypeName,Declarations, Scanner.CurFilename, Scanner.CurRow));
          ClassEl.ObjKind:=okGeneric;
          try
            ReadGenericArguments(ClassEl.GenericTemplateTypes,ClassEl,False);
          Except
            List.Free;
            Raise;
          end;
          ExpectToken(tkEqual);
          ExpectToken(tkClass);
          NextToken;
          DoParseClassType(ClassEl, Scanner.CurFilename, Scanner.CurRow);
          Declarations.Declarations.Add(ClassEl);
          Declarations.Classes.Add(ClassEl)
        end;
      tkbegin:
        begin
        if Declarations is TProcedureBody then
          begin
          ParseProcBeginBlock(TProcedureBody(Declarations));
          break;
          end
        else if (Declarations is TInterfaceSection)
        or (Declarations is TImplementationSection) then
          begin
          ParseInitialization;
          break;
          end
        else
          ParseExc(SParserSyntaxError);
        end;
      tklabel:
        begin
          if not (Declarations is TInterfaceSection) then
            ParseLabels(Declarations);
        end;
    else
      ParseExc(SParserSyntaxError);
    end;
  end;
end;

// Starts after the "uses" token
procedure TPasParser.ParseUsesList(ASection: TPasSection);

function CheckUnit(AUnitName : string):TPasElement;
begin
    result := Engine.FindModule(AUnitName);  // should we resolve module here when "IN" filename is not known yet?
    if Assigned(result) then
      result.AddRef
    else
      Result := TPasType(CreateElement(TPasUnresolvedTypeRef, AUnitName,
        ASection));
    ASection.UsesList.Add(Result);
end;

var
  AUnitName: String;
  Element: TPasElement;
begin
  If not (Asection is TImplementationSection) Then // interface,program,library,package
    Element:=CheckUnit('System'); // system always implicitely first.    
  while True do
  begin
    AUnitName := ExpectIdentifier; 
    Element :=CheckUnit(AUnitName);

    NextToken;

    if CurToken = tkin then begin
      // todo: store unit's file name somewhere
      NextToken; // skip in
      ExpectToken(tkString); // skip unit's real file name
      if (Element is TPasModule) and (TPasmodule(Element).filename<>'')  then
        TPasModule(Element).FileName:=curtokenstring;
    end;

    if CurToken = tkSemicolon then
      break
    else if CurToken <> tkComma then
      ParseExc(SParserExpectedCommaSemicolon);
  end;
end;

// Starts after the variable name
function TPasParser.ParseConstDecl(Parent: TPasElement): TPasConst;
begin
  Result := TPasConst(CreateElement(TPasConst, CurTokenString, Parent));
  try
    NextToken;
    if CurToken = tkColon then
      Result.VarType := ParseType(nil)
    else
      UngetToken;

    ExpectToken(tkEqual);

    //skipping the expression as a value
    //Result.Value := ParseExpression;

    // using new expression parser!
    NextToken; // skip tkEqual
    Result.Expr:=DoParseConstValueExpression(Result);

    // must unget for the check to be peformed fine!
    UngetToken;

    CheckHint(Result,True);
  except
    Result.Free;
    raise;
  end;
end;

// Starts after the variable name
function TPasParser.ParseResourcestringDecl(Parent: TPasElement): TPasResString;
begin
  Result := TPasResString(CreateElement(TPasResString, CurTokenString, Parent));
  try
    ExpectToken(tkEqual);
    NextToken; // skip tkEqual
    Result.Expr:=DoParseConstValueExpression(Result);
    UngetToken;
    CheckHint(Result,True);
  except
    Result.Free;
    raise;
  end;
end;

procedure TPasParser.ReadGenericArguments(List : TFPList;Parent : TPasElement; IsSpecialize : Boolean);

Var
  N : String;

begin
  ExpectToken(tkLessThan);
  repeat
    N:=ExpectIdentifier;
    List.Add(CreateElement(TPasGenericTemplateType,N,Parent));
    NextToken;
    if not (CurToken in [tkComma, tkGreaterThan]) then
      ParseExc(Format(SParserExpectToken2Error,
        [TokenInfos[tkComma], TokenInfos[tkGreaterThan]]));
  until CurToken = tkGreaterThan;
end;

// Starts after the type name
Function TPasParser.ParseRangeType(AParent : TPasElement; Const TypeName : String; Full : Boolean = True) : TPasRangeType;

Var
  PE : TPasExpr;

begin
  Result := TPasRangeType(CreateElement(TPasRangeType, TypeName, AParent));
  try
    if Full then
      begin
      If not (CurToken=tkEqual) then
        ParseExc(Format(SParserExpectTokenError,[TokenInfos[tkEqual]]));
      end;
    NextToken;
    PE:=DoParseExpression(Result,Nil);
    if not ((PE is TBinaryExpr) and (TBinaryExpr(PE).Kind=pekRange)) then
      begin
      FreeAndNil(PE);
      ParseExc(SRangeExpressionExpected);
      end;
    Result.RangeExpr:=PE as TBinaryExpr;
    UngetToken;
  except
    FreeAndNil(Result);
    raise;
  end;
end;

Function TPasParser.ParseSpecializeType(Parent : TPasElement; Const TypeName : String) : TPasClassType;

begin
  Result := TPasClassType(Engine.CreateElement(TPasClassType, TypeName, Parent, Scanner.CurFilename, Scanner.CurRow));
  try
    Result.ObjKind := okSpecialize;
    Result.AncestorType := ParseType(nil);
    Result.IsShortDefinition:=True;
    ReadGenericArguments(TPasClassType(Result).GenericTemplateTypes,Result,True);
  except
    FreeAndNil(Result);
    Raise;
  end;
end;

Function TPasParser.ParseProcedureType(Parent : TPasElement; Const TypeName : String; Const PT : TProcType) : TPasProcedureType;

begin
  if PT in [ptFunction,ptClassFunction] then
    Result := CreateFunctionType(TypeName, 'Result', Parent, False)
  else
    Result := TPasProcedureType(CreateElement(TPasProcedureType, TypeName, Parent));
  try
    ParseProcedureOrFunctionHeader(Result, TPasProcedureType(Result), PT, True);
  except
    FreeAndNil(Result);
    raise;
  end;
end;

function TPasParser.ParseTypeDecl(Parent: TPasElement): TPasType;

var
  TypeName: String;
begin
  TypeName := CurTokenString;
  ExpectToken(tkEqual);
  Result:=ParseType(Parent,TypeName,True);
end;

Function TPasParser.GetVariableValueAndLocation(Parent : TPasElement; out Value,Location : String) : Boolean;

begin
  NextToken;
  Result:=CurToken=tkEqual;
  if Result then
    begin
    Value := ParseExpression(Parent);
    NextToken;
    end;
  if (CurToken=tkAbsolute) then
    begin
    Result:=True;
    ExpectIdentifier;
    Location:=CurTokenText;
    NextToken;
    if CurToken=tkDot then
      begin
      ExpectIdentifier;
      Location:=Location+'.'+CurTokenText;
      end
    else
      UnGetToken;
    end
  else
    UngetToken;
end;

Function TPasParser.GetVariableModifiers(Parent : TPasElement) : string;

Var
  S : String;
begin
  Result := '';
  NextToken;
  If CurTokenIsIdentifier('cvar') then
    begin
    Result:=';cvar';
    ExpectToken(tkSemicolon);
    NextToken;
    end;
  s:=LowerCase(CurTokenText);
  if Not ((s='external') or (s='public') or (s='export')) then
    UngetToken
  else
    begin
    Result:=Result+';'+CurTokenText;
    NextToken;
    if (Curtoken<>tksemicolon) then
      begin
      if (s='external') then
        begin
        if (CurToken in [tkString,tkIdentifier])
            and Not (CurTokenIsIdentifier('name')) then
          begin
          Result := Result + ' ' + CurTokenText;
          NextToken;
          end;
        end;
      if CurTokenIsIdentifier('name') then
        begin
        Result := Result + ' name ';
        NextToken;
        if (CurToken in [tkString,tkIdentifier]) then
          Result := Result + CurTokenText
        else
          ParseExc(SParserSyntaxError);
        NextToken;
        end
      else
        ParseExc(SParserSyntaxError);
      end;
    end;
end;


// Full means that a full variable declaration is being parsed.
procedure TPasParser.ParseVarList(Parent: TPasElement; VarList: TFPList; AVisibility: TPasMemberVisibility; Full : Boolean);

var
  VarNames: TStringList;
  i: Integer;
  VarType: TPasType;
  VarEl: TPasVariable;
  H : TPasMemberHints;
  Mods,Value,Loc : string;

begin
  VarNames := TStringList.Create;
  try
    Repeat
      VarNames.Add(CurTokenString);
      NextToken;
      if Not (CurToken in [tkComma,tkColon]) then
        ParseExc(SParserExpectedCommaColon);
      if CurToken=tkComma then
        ExpectIdentifier;
    Until (CurToken=tkColon);
    If Full then
      VarType := ParseComplexType(Nil)
    else
      VarType := ParseComplexType(Parent);
    If Full then
      GetVariableValueAndLocation(Parent,Value,Loc);
    H:=CheckHint(Nil,Full);
    if full then
      Mods:=GetVariableModifiers(Parent)
    else
      NextToken;
    for i := 0 to VarNames.Count - 1 do
      begin
      VarEl:=TPasVariable(CreateElement(TPasVariable,VarNames[i],Parent,AVisibility));
      VarEl.VarType := VarType;
      VarEl.Hints:=H;
      VarEl.Value:=Value;
      VarEl.AbsoluteLocation:=Loc;
      if (i>0) then
        VarType.AddRef;
      VarList.Add(VarEl);
      end;
  finally
    VarNames.Free;
  end;
end;

function TPasParser.LogEvent(E: TPParserLogEvent): Boolean;
begin
  Result:=E in FLogEvents;
end;

procedure TPasParser.DoLog(const Msg: String; SkipSourceInfo: Boolean);
begin
  If Assigned(FOnLog) then
    if SkipSourceInfo or not assigned(scanner) then
      FOnLog(Self,Msg)
    else
      FOnLog(Self,Format('%s(%d) : %s',[Scanner.CurFilename,SCanner.CurRow,Msg]));
end;

procedure TPasParser.DoLog(const Fmt: String; Args: array of const;
  SkipSourceInfo: Boolean);
begin
  DoLog(Format(Fmt,Args),SkipSourceInfo);
end;

procedure TPasParser.ParseInlineVarDecl(Parent: TPasElement; List: TFPList;
  AVisibility: TPasMemberVisibility = VisDefault; ClosingBrace: Boolean = False);

Var
  tt : TTokens;
begin
  ParseVarList(Parent,List,AVisibility,False);
  tt:=[tkEnd,tkSemicolon];
  if ClosingBrace then
   include(tt,tkBraceClose);
  if not (CurToken in tt) then
    ParseExc(SParserExpectedSemiColonEnd);
end;

// Starts after the variable name
procedure TPasParser.ParseVarDecl(Parent: TPasElement; List: TFPList);

begin
  ParseVarList(Parent,list,visDefault,True);
end;

// Starts after the opening bracket token
procedure TPasParser.ParseArgList(Parent: TPasElement; Args: TFPList; EndToken: TToken);
var
  ArgNames: TStringList;
  IsUntyped: Boolean;
  Name, Value: String;
  i: Integer;
  Arg: TPasArgument;
  Access: TArgumentAccess;
  ArgType: TPasType;
begin
  while True do
  begin
    ArgNames := TStringList.Create;
    Access := argDefault;
    IsUntyped := False;
    ArgType := nil;
    while True do
    begin
      NextToken;
      if CurToken = tkConst then
      begin
        Access := argConst;
        Name := ExpectIdentifier;
      end else if CurToken = tkVar then
      begin
        Access := ArgVar;
        Name := ExpectIdentifier;
      end else if (CurToken = tkIdentifier) and (UpperCase(CurTokenString) = 'OUT') then
      begin
        Access := ArgOut;
        Name := ExpectIdentifier;
      end else if CurToken = tkIdentifier then
        Name := CurTokenString
      else
        ParseExc(SParserExpectedConstVarID);
      ArgNames.Add(Name);
      NextToken;
      if CurToken = tkColon then
        break
      else if ((CurToken = tkSemicolon) or (CurToken = tkBraceClose)) and
        (Access <> argDefault) then
      begin
        // found an untyped const or var argument
        UngetToken;
        IsUntyped := True;
        break
      end
      else if CurToken <> tkComma then
        ParseExc(SParserExpectedCommaColon);
    end;
    SetLength(Value, 0);
    if not IsUntyped then
    begin
      ArgType := ParseType(nil);
      NextToken;
      if CurToken = tkEqual then
      begin
        Value := ParseExpression(Parent);
      end else
        UngetToken;
    end;

    for i := 0 to ArgNames.Count - 1 do
    begin
      Arg := TPasArgument(CreateElement(TPasArgument, ArgNames[i], Parent));
      Arg.Access := Access;
      Arg.ArgType := ArgType;
      if (i > 0) and Assigned(ArgType) then
        ArgType.AddRef;
      Arg.Value := Value;
      Args.Add(Arg);
    end;

    ArgNames.Free;
    NextToken;
    if CurToken = EndToken then
      break;
  end;
end;


Function TPasParser.CheckProcedureArgs(Parent  : TPasElement; Args : TFPList; Mandatory : Boolean) : boolean;

begin
  NextToken;
  Result:=(Curtoken=tkbraceOpen);
  if not Result then
    begin
    if Mandatory then
      ParseExc(SParserExpectedLBracketColon)
    else
      UngetToken;
    end
  else
    begin
    NextToken;
    if (CurToken<>tkBraceClose) then
      begin
      UngetToken;
      ParseArgList(Parent, Args, tkBraceClose);
      end;
    end;
end;

// Next token is expected to be a "(", ";" or for a function ":". The caller
// will get the token after the final ";" as next token.
procedure TPasParser.ParseProcedureOrFunctionHeader(Parent: TPasElement;
  Element: TPasProcedureType; ProcType: TProcType; OfObjectPossible: Boolean);

  procedure ConsumeSemi;
  begin
    NextToken;
    if (CurToken <> tksemicolon) and IsCurTokenHint then
      ungettoken;
  end;

Var
  Tok : String;
  i: Integer;
  Proc: TPasProcedure;
  ahint : TPasMemberHint;
  CC : TCallingConvention;
  PM : TProcedureModifier;

begin
  CheckProcedureArgs(Parent,Element.Args,ProcType=ptOperator);
  case ProcType of
    ptFunction,ptClassFunction:
      begin
      ExpectToken(tkColon);
      if Assigned(Element) then        // !!!
        TPasFunctionType(Element).ResultEl.ResultType := ParseType(Parent)
      else
        ParseType(nil);
      end;
    ptProcedure,ptConstructor,ptDestructor,ptClassProcedure:
      begin
      NextToken;
      if (CurToken = tkSemicolon) or IsCurtokenHint
        or (OfObjectPossible and (CurToken in [tkOf,tkEqual]))
      then
        UngetToken
      else
        ParseExc(SParserExpectedLBracketSemicolon);
      end;
    ptOperator:
      begin
      NextToken;
      if (CurToken=tkIdentifier) then
        begin
        TPasFunctionType(Element).ResultEl.Name := CurTokenName;
        ExpectToken(tkColon);
        end
      else
        if (CurToken=tkColon) then
          TPasFunctionType(Element).ResultEl.Name := 'Result'
        else
          ParseExc(SParserExpectedColonID);
        if Assigned(Element) then        // !!!
          TPasFunctionType(Element).ResultEl.ResultType := ParseType(Parent)
        else
          ParseType(nil);
      end;
  end;

  NextToken;
  if OfObjectPossible and (CurToken = tkOf) then
  begin
    ExpectToken(tkObject);
    Element.IsOfObject := True;
  end else
    UngetToken;

  NextToken;
  if CurToken = tkEqual then
  begin
    // for example: const p: procedure = nil;
    UngetToken;
    exit;
  end else
    UngetToken;

  ConsumeSemi; //ExpectToken(tkSemicolon);
  while True do
    begin
    NextToken;
    If TokenisCallingConvention(Element,CurTokenString,cc) then
      begin
      if Assigned(Element) then        // !!!
        Element.CallingConvention:=Cc;
      ExpectToken(tkSemicolon);
      end
    else if TokenIsProcedureModifier(Element,CurTokenString,pm) then
      begin
      if parent is TPasProcedure then
        TPasProcedure(Parent).AddModifier(pm);
      if pm=pmExternal then
        begin
        NextToken;
        if CurToken in [tkString,tkIdentifier] then
          begin
          NextToken;
          if CurToken=tkSemicolon then
            UnGetToken
          else
            begin
            Tok:=UpperCase(CurTokenString);
            if Tok='NAME' then
              begin
              NextToken;
              if not (CurToken in [tkString,tkIdentifier]) then
                ParseExc(Format(SParserExpectTokenError, [TokenInfos[tkString]]));
              end;
            end;
          end
        else
          UngetToken;
        end
      else if pm=pmForward then
        begin
        if (Parent.Parent is TInterfaceSection) then
           begin
           UngetToken;
           break;
           end;
        end
      else if (pm=pmMessage) then
        begin
        Repeat
          NextToken;
          If CurToken<>tkSemicolon then
            begin
            if parent is TPasProcedure then
              TPasProcedure(Parent).MessageName:=CurtokenString;
            If (CurToken=tkString) and (parent is TPasProcedure) then
              TPasProcedure(Parent).Messagetype:=pmtString;
            end;
        until CurToken = tkSemicolon;
        UngetToken;
        end;
      ExpectToken(tkSemicolon);
      end
    else if (CurToken = tkIdentifier) or (CurToken=tklibrary) then // library is a token and a directive.
      begin
      Tok:=UpperCase(CurTokenString);
      if IsCurTokenHint(ahint) then  // deprecated,platform,experimental,library, unimplemented etc
        begin
        element.hints:=element.hints+[ahint];
        consumesemi;
        end
      else if (tok = 'PUBLIC') then
        begin
        NextToken;
        { Should be token Name,
          if not we're in a class and the public section starts }
        If (Uppercase(CurTokenString)<>'NAME') then
          begin
          UngetToken;
          UngetToken;
          Break;
          end
        else
          begin
          NextToken;  // Should be export name string.
          ExpectToken(tkSemicolon);
          end;
        end
      else
        begin
        UnGetToken;
        Break;
        end
      end
    else if (CurToken = tkSquaredBraceOpen) then
      begin
      repeat
        NextToken
      until CurToken = tkSquaredBraceClose;
      ExpectToken(tkSemicolon);
      end
    else
      begin
      UngetToken;
      break;
      end;
    end;
  if (ProcType = ptOperator) and (Parent is TPasProcedure) then
  begin
    Proc:=TPasProcedure(Parent);
    Proc.Name := Proc.Name + '(';
    for i := 0 to Proc.ProcType.Args.Count - 1 do
    begin
      if i > 0 then
        Proc.Name := Proc.Name + ', ';
      Proc.Name := Proc.Name +
        TPasArgument(Proc.ProcType.Args[i]).ArgType.Name;
    end;
    Proc.Name := Proc.Name + '): ' +
      TPasFunctionType(Proc.ProcType).ResultEl.ResultType.Name;
  end;

  if (Parent is TPasProcedure)
  and (not TPasProcedure(Parent).IsForward)
  and (not TPasProcedure(Parent).IsExternal)
  and ((Parent.Parent is TImplementationSection)
     or (Parent.Parent is TProcedureBody))
  then
    ParseProcedureBody(Parent);
end;

// starts after the semicolon
procedure TPasParser.ParseProcedureBody(Parent: TPasElement);

var
  Body: TProcedureBody;

begin
  Body := TProcedureBody(CreateElement(TProcedureBody, '', Parent));
  TPasProcedure(Parent).Body:=Body;
  ParseDeclarations(Body);
end;


Function TPasParser.ParseProperty(Parent : TPasElement; Const AName : String; AVisibility : TPasMemberVisibility; IsClass : Boolean) : TPasProperty;

  procedure MaybeReadFullyQualifiedIdentifier(Var r : String);

  begin
    while True do
      begin
      NextToken;
      if CurToken = tkDot then
        begin
        ExpectIdentifier;
        R:=R + '.' + CurTokenString;
        end
      else
        break;
      end;
  end;

  function GetAccessorName: String;
  begin
    ExpectIdentifier;
    Result := CurTokenString;
    MaybeReadFullyQualifiedIdentifier(Result);
    if CurToken <> tkSquaredBraceOpen then
      UnGetToken
    else
      begin
      Result := Result + '[';
      NextToken;
      if CurToken in [tkIdentifier, tkNumber] then
        Result := Result + CurTokenString;
      ExpectToken(tkSquaredBraceClose);
      Result := Result + ']';
      end;
  end;

var
  isArray : Boolean;
  us  : String;
  h   : TPasMemberHint;

begin
  Result:=TPasProperty(CreateElement(TPasProperty,AName,Parent,AVisibility));
  try
    NextToken;
    isArray:=CurToken=tkSquaredBraceOpen;
    if isArray then
      begin
      ParseArgList(Result, Result.Args, tkSquaredBraceClose);
      NextToken;
      end;
    if CurToken = tkColon then
      begin
      Result.VarType := ParseType(Result);
      NextToken;
      end;
    if CurTokenIsIdentifier('INDEX') then
      begin
      Result.IndexValue := ParseExpression(Result,ek_PropertyIndex);
      NextToken;
      end;
    if CurTokenIsIdentifier('READ') then
      begin
      Result.ReadAccessorName := GetAccessorName;
      NextToken;
      end;
    if CurTokenIsIdentifier('WRITE') then
      begin
      Result.WriteAccessorName := GetAccessorName;
      NextToken;
      end;
    if CurTokenIsIdentifier('IMPLEMENTS') then
      begin
      Result.ImplementsName := GetAccessorName;
      NextToken;
      end;
    if CurTokenIsIdentifier('STORED') then
      begin
      NextToken;
      if CurToken = tkTrue then
        Result.StoredAccessorName := 'True'
      else if CurToken = tkFalse then
        Result.StoredAccessorName := 'False'
      else if CurToken = tkIdentifier then
        Result.StoredAccessorName := CurTokenString
      else
        ParseExc(SParserSyntaxError);
      NextToken;
      end;
    if CurTokenIsIdentifier('DEFAULT') then
      begin
      if isArray then
        ParseExc('Array properties cannot have default value');
      Result.DefaultValue := ParseExpression(Result);
      NextToken;
      end
    else if CurtokenIsIdentifier('NODEFAULT') then
      begin
      Result.IsNodefault:=true;
      NextToken;
      end;
    // Here the property ends. There can still be a 'default'
    if CurToken = tkSemicolon then
      NextToken;
    if CurTokenIsIdentifier('DEFAULT') then
      begin
      if not isArray then
        ParseExc('The default property must be an array property');
      NextToken;
      if CurToken = tkSemicolon then
        begin
        Result.IsDefault := True;
        NextToken;
        end
      end;
    // Handle hints
    while IsCurTokenHint(h) do
      begin
      Result.Hints:=Result.Hints+[h];
      NextToken;
      if CurToken=tkSemicolon then
        NextToken;
      end;
    UngetToken;
  except
    FreeAndNil(Result);
    Raise;
  end;
end;

// Starts after the "begin" token
procedure TPasParser.ParseProcBeginBlock(Parent: TProcedureBody);
var
  BeginBlock: TPasImplBeginBlock;
  SubBlock: TPasImplElement;
begin
  //writeln('TPasParser.ParseProcBeginBlock ');

  BeginBlock := TPasImplBeginBlock(CreateElement(TPasImplBeginBlock, '', Parent));
  Parent.Body := BeginBlock;
  repeat
    NextToken;
    if CurToken=tkend then
      break
    else if CurToken<>tkSemiColon then
    begin
      UngetToken;
      ParseStatement(BeginBlock,SubBlock);
      if SubBlock=nil then
        ExpectToken(tkend);
    end;
  until false;
  ExpectToken(tkSemicolon);
end;

// Next token is start of (compound) statement
// After parsing CurToken is on last token of statement
procedure TPasParser.ParseStatement(Parent: TPasImplBlock;
  out NewImplElement: TPasImplElement);
var
  CurBlock: TPasImplBlock;

  {$IFDEF VerbosePasParser}
  function i: string;
  var
    c: TPasElement;
  begin
    Result:='ParseImplCompoundStatement ';
    c:=CurBlock;
    while c<>nil do begin
      Result:=Result+'  ';
      c:=c.Parent;
    end;
  end;
  {$ENDIF}

  function CloseBlock: boolean; // true if parent reached
  begin
    CurBlock:=CurBlock.Parent as TPasImplBlock;
    Result:=CurBlock=Parent;
  end;

  function CloseStatement(CloseIfs: boolean): boolean; // true if parent reached
  begin
    if CurBlock=Parent then exit(true);
    while CurBlock.CloseOnSemicolon
    or (CloseIfs and (CurBlock is TPasImplIfElse)) do
      if CloseBlock then exit(true);
    Result:=false;
  end;

  procedure CreateBlock(NewBlock: TPasImplBlock);
  begin
    CurBlock:=NewBlock;
    if NewImplElement=nil then NewImplElement:=CurBlock;
  end;

var
  Condition: String;
  StartValue: String;
  VarName: String;
  EndValue: String;
  Expr: String;
  SubBlock: TPasImplElement;
  CmdElem: TPasImplElement;
  TypeName: String;
  ForDownTo: Boolean;
  left: TPasExpr;
  right: TPasExpr;
begin
  NewImplElement:=nil;
  CurBlock := Parent;
  while True do
  begin
    NextToken;
    //WriteLn(i,'Token=',CurTokenText);
    case CurToken of
    tkbegin:
      CreateBlock(CurBlock.AddBeginBlock);
    tkrepeat:
      CreateBlock(CurBlock.AddRepeatUntil);
    tkIf:
      begin
        Condition:=ParseExpression(Parent);
        //WriteLn(i,'IF Condition="',Condition,'" Token=',CurTokenText);
        CreateBlock(CurBlock.AddIfElse(Condition));
        ExpectToken(tkthen);
      end;
    tkelse:
      if (CurBlock is TPasImplIfElse) then
      begin
        if TPasImplIfElse(CurBlock).IfBranch=nil then
        begin
          // empty then => add dummy command
          CurBlock.AddCommand('');
        end;
        if TPasImplIfElse(CurBlock).ElseBranch<>nil then
        begin
          // this and the following 3 may solve TPasImplIfElse.AddElement BUG
          // ifs without begin end
          // if .. then
          //  if .. then
          //   else
          // else
          CloseBlock;
          CloseStatement(false);
        end;
      end else if (CurBlock is TPasImplWhileDo) then
      begin
        //if .. then while .. do smt else ..
        CloseBlock;
        UngetToken;
      end else if (CurBlock is TPasImplRaise) then
      begin
        //if .. then Raise Exception else ..
        CloseBlock;
        UngetToken;
      end else if (CurBlock is TPasImplTryExcept) then
      begin
        CloseBlock;
        CurBlock:=TPasImplTry(CurBlock).AddExceptElse;
      end else
        ParseExc(SParserSyntaxError);
    tkwhile:
      begin
        // while Condition do
        Condition:=ParseExpression(Parent);
        //WriteLn(i,'WHILE Condition="',Condition,'" Token=',CurTokenText);
        CreateBlock(CurBlock.AddWhileDo(Condition));
        ExpectToken(tkdo);
      end;
    tkgoto:
      begin
        nexttoken;
        curblock.AddCommand('goto '+curtokenstring);
        expecttoken(tkSemiColon);
      end;
    tkfor:
      begin
        // for VarName := StartValue to EndValue do
        ExpectIdentifier;
        VarName:=CurTokenString;
        ExpectToken(tkAssign);
        StartValue:=ParseExpression(Parent);
        //writeln(i,'FOR Start=',StartValue);
        NextToken;
        if CurToken=tkTo then
          ForDownTo:=false
        else if CurToken=tkdownto then
          ForDownTo:=true
        else
          ParseExc(Format(SParserExpectTokenError, [TokenInfos[tkTo]]));
        EndValue:=ParseExpression(Parent);
        CreateBlock(CurBlock.AddForLoop(VarName,StartValue,EndValue,ForDownTo));
        //WriteLn(i,'FOR "',VarName,'" := ',StartValue,' to ',EndValue,' Token=',CurTokenText);
        ExpectToken(tkdo);
      end;
    tkwith:
      begin
        // with Expr do
        // with Expr, Expr do
        Expr:=ParseExpression(Parent);
        //writeln(i,'WITH Expr="',Expr,'" Token=',CurTokenText);
        CreateBlock(CurBlock.AddWithDo(Expr));
        repeat
          NextToken;
          if CurToken=tkdo then break;
          if CurToken<>tkComma then
            ParseExc(Format(SParserExpectTokenError, [TokenInfos[tkdo]]));
          Expr:=ParseExpression(Parent);
          //writeln(i,'WITH ...,Expr="',Expr,'" Token=',CurTokenText);
          TPasImplWithDo(CurBlock).AddExpression(Expr);
        until false;
      end;
    tkcase:
      begin
        Expr:=ParseExpression(Parent);
        //writeln(i,'CASE OF Expr="',Expr,'" Token=',CurTokenText);
        ExpectToken(tkof);
        CreateBlock(CurBlock.AddCaseOf(Expr));
        repeat
          NextToken;
          //writeln(i,'CASE OF Token=',CurTokenText);
          case CurToken of
          tkend:
            break; // end without else
          tkelse:
            begin
              // create case-else block
              CurBlock:=TPasImplCaseOf(CurBlock).AddElse;
              break;
            end
          else
            UngetToken;
            // read case values
            repeat
              Expr:=ParseExpression(Parent);
              //writeln(i,'CASE value="',Expr,'" Token=',CurTokenText);
              NextToken;
              if CurToken=tkDotDot then
              begin
                Expr:=Expr+'..'+ParseExpression(Parent);
                NextToken;
              end;
              // do not miss '..'
              if CurBlock is TPasImplCaseStatement then
                TPasImplCaseStatement(CurBlock).Expressions.Add(Expr)
              else
                CurBlock:=TPasImplCaseOf(CurBlock).AddCase(Expr);
              //writeln(i,'CASE after value Token=',CurTokenText);
              if CurToken=tkColon then break;
              if CurToken<>tkComma then
                ParseExc(Format(SParserExpectTokenError, [TokenInfos[tkComma]]));
            until false;
            // read statement
            ParseStatement(CurBlock,SubBlock);
            CloseBlock;
            if CurToken<>tkSemicolon then
            begin
              NextToken;
              if not (CurToken in [tkSemicolon,tkelse,tkend]) then
                ParseExc(Format(SParserExpectTokenError, [TokenInfos[tkSemicolon]]));
              if CurToken<>tkSemicolon then
                UngetToken;
            end;
          end;
        until false;
        if CurToken=tkend then
        begin
          if CloseBlock then break;
          if CloseStatement(false) then break;
        end;
      end;
    tktry:
      CreateBlock(CurBlock.AddTry);
    tkfinally:
      begin
        if CloseStatement(true) then
        begin
          UngetToken;
          break;
        end;
        if CurBlock is TPasImplTry then
        begin
          CurBlock:=TPasImplTry(CurBlock).AddFinally;
        end else
          ParseExc(SParserSyntaxError);
      end;
    tkexcept:
      begin
        if CloseStatement(true) then
        begin
          UngetToken;
          break;
        end;
        if CurBlock is TPasImplTry then
        begin
          //writeln(i,'EXCEPT');
          CurBlock:=TPasImplTry(CurBlock).AddExcept;
        end else
          ParseExc(SParserSyntaxError);
      end;
    tkon:
      begin
        // in try except:
        // on E: Exception do
        // on Exception do
        if CurBlock is TPasImplTryExcept then
        begin
          VarName:='';
          TypeName:=ParseExpression(Parent);
          //writeln(i,'ON t=',TypeName,' Token=',CurTokenText);
          NextToken;
          if CurToken=tkColon then
          begin
            VarName:=TypeName;
            TypeName:=ParseExpression(Parent);
            //writeln(i,'ON v=',VarName,' t=',TypeName,' Token=',CurTokenText);
          end else
            UngetToken;
          CurBlock:=TPasImplTryExcept(CurBlock).AddExceptOn(VarName,TypeName);
          ExpectToken(tkDo);
        end else
          ParseExc(SParserSyntaxError);
      end;
    tkraise:
      CreateBlock(CurBlock.AddRaise);
    tkend:
      begin
        if CloseStatement(true) then
        begin
          UngetToken;
          break;
        end;
        if CurBlock is TPasImplBeginBlock then
        begin
          if CloseBlock then break; // close end
          if CloseStatement(false) then break;
        end else if CurBlock is TPasImplCaseElse then
        begin
          if CloseBlock then break; // close else
          if CloseBlock then break; // close caseof
          if CloseStatement(false) then break;
        end else if CurBlock is TPasImplTryHandler then
        begin
          if CloseBlock then break; // close finally/except
          if CloseBlock then break; // close try
          if CloseStatement(false) then break;
        end else
          ParseExc(SParserSyntaxError);
      end;
    tkSemiColon:
      if CloseStatement(true) then break;
    tkuntil:
      begin
        if CloseStatement(true) then
        begin
          UngetToken;
          break;
        end;
        if CurBlock is TPasImplRepeatUntil then
        begin
          Condition:=ParseExpression(Parent);
          TPasImplRepeatUntil(CurBlock).Condition:=Condition;
          //WriteLn(i,'UNTIL Condition="',Condition,'" Token=',CurTokenString);
          if CloseBlock then break;
        end else
          ParseExc(SParserSyntaxError);
      end;
    else
      left:=DoParseExpression(nil);
      case CurToken of
        tkAssign:
        begin
          // assign statement
          NextToken;
          right:=DoParseExpression(nil); // this may solve TPasImplWhileDo.AddElement BUG
          CmdElem:=CurBlock.AddAssign(left, right);
          UngetToken;
        end;
        tkColon:
        begin
          if not (left is TPrimitiveExpr) then
            ParseExc(Format(SParserExpectTokenError, [TokenInfos[tkSemicolon]]));
          // label mark. todo: check mark identifier in the list of labels
          CmdElem:=CurBlock.AddLabelMark(TPrimitiveExpr(left).Value);
          left.Free;
        end;
      else
        // simple statement (function call)
        CmdElem:=CurBlock.AddSimple(left);
        UngetToken;
      end;

      if not (CmdElem is TPasImplLabelMark) then
        if NewImplElement=nil then NewImplElement:=CmdElem;
    end;
  end;
end;

procedure TPasParser.ParseLabels(AParent: TPasElement);
var
  Labels: TPasLabels;
begin
  Labels:=TPasLabels(CreateElement(TPasLabels, '', AParent));
  repeat
    Labels.Labels.Add(ExpectIdentifier);
    NextToken;
    if not (CurToken in [tkSemicolon, tkComma]) then
      ParseExc(Format(SParserExpectTokenError, [TokenInfos[tkSemicolon]]));
  until CurToken=tkSemicolon;
end;

// Starts after the "procedure" or "function" token
Function TPasParser.GetProcedureClass(ProcType : TProcType) : TPTreeElement;

begin
  Case ProcType of
    ptFunction       : Result:=TPasFunction;
    ptClassFunction  : Result:=TPasClassFunction;
    ptClassProcedure : Result:=TPasClassProcedure;
    ptProcedure      : Result:=TPasProcedure;
    ptConstructor    : Result:=TPasConstructor;
    ptDestructor     : Result:=TPasDestructor;
    ptOperator       : Result:=TPasOperator;
  else
    ParseExc('Unknown procedure Type '+intToStr(Ord(ProcType)));
  end;
end;

function TPasParser.ParseProcedureOrFunctionDecl(Parent: TPasElement; ProcType: TProcType;AVisibility : TPasMemberVisibility = VisDefault): TPasProcedure;

  function ExpectProcName: string;
  begin
    Result:=ExpectIdentifier;
    //writeln('ExpectProcName ',Parent.Classname);
    if Parent is TImplementationSection then
    begin
      NextToken;
      if CurToken=tkDot then
      begin
        Result:=Result+'.'+ExpectIdentifier;
      end else
        UngetToken;
    end;
  end;

var
  Name: String;
  PC : TPTreeElement;

begin
  If (ProcType<>ptOperator) then
    Name:=ExpectProcName
  else
    begin
    NextToken;
    Name := 'operator ' + TokenInfos[CurToken];
    end;
  PC:=GetProcedureClass(ProcType);
  Parent:=CheckIfOverLoaded(Parent,Name);
  Result:=TPasProcedure(CreateElement(PC,Name,Parent,AVisibility));
  if ProcType in [ptFunction, ptClassFunction] then
    Result.ProcType := CreateFunctionType('', 'Result', Result, True)
  else if ProcType=ptOperator then
    Result.ProcType := CreateFunctionType('', '__INVALID__', Result,True)
  else
    Result.ProcType := TPasProcedureType(CreateElement(TPasProcedureType, '', Result));
  ParseProcedureOrFunctionHeader(Result, Result.ProcType, ProcType, False);
end;

// Current token is the first token after tkOf
Procedure TPasParser.ParseRecordVariantParts(ARec : TPasRecordType; AEndToken: TToken);

Var
  M : TPasRecordType;
  V : TPasVariant;
  Done : Boolean;

begin
  Repeat
    V:=TPasVariant(CreateElement(TPasVariant, '', ARec));
    ARec.Variants.Add(V);
    Repeat
      V.Values.Add(ParseExpression(ARec));
      NextToken;
      if Not (CurToken in [tkComma,tkColon]) then
        ParseExc(SParserExpectedCommaColon);
    Until (curToken=tkColon);
    ExpectToken(tkBraceOpen);
    NextToken;
    M:=TPasRecordType(CreateElement(TPasRecordType,'',V));
    V.Members:=M;
    ParseRecordFieldList(M,tkBraceClose);
    // Current token is closing ), so we eat that
    NextToken;
    // If there is a semicolon, we eat that too.
    if CurToken=tkSemicolon then
      NextToken;
    // ParseExpression starts with a nexttoken.
    // So we need to determine the next token, and if it is an ending token, unget.
    Done:=CurToken=AEndToken;
    If not Done then
      Ungettoken;
  Until Done;
end;

procedure TPasParser.DumpCurToken(Const Msg : String);
begin
  Writeln(Msg,' : ',TokenInfos[CurToken],' "',CurTokenString,'"');
  Flush(output)
end;

// Starts on first token after Record or (. Ends on AEndToken
Procedure TPasParser.ParseRecordFieldList(ARec : TPasRecordType; AEndToken : TToken);

Var
  V : TPasVariant;
  VN : String;

begin
  while CurToken<>AEndToken do
    begin
    Case CurToken of
      tkIdentifier :
        begin
        ParseInlineVarDecl(ARec, ARec.Members, visDefault, AEndToken=tkBraceClose);
        end;
      tkCase :
        begin
        ARec.Variants:=TFPList.Create;
        NextToken;
        VN:=CurTokenString;
        NextToken;
        If CurToken=tkColon then
          ARec.VariantName:=VN
        else
          begin
          UnGetToken;
          UnGetToken;
          end;
        ARec.VariantType:=ParseType(ARec);
        ExpectToken(tkOf);
        ParseRecordVariantParts(ARec,AEndToken);
        end;
    else
      ParseExc(SParserTypeSyntaxError);
    end;
    if CurToken<>AEndToken then
      NextToken;
    end;
end;

// Starts after the "record" token
Function TPasParser.ParseRecordDecl(Parent: TPasElement; Const TypeName : string; const Packmode : TPackMode = pmNone) : TPasRecordType;
var
  N : String;
  Variant: TPasVariant;
  M : TFPList;

begin
  Result := TPasRecordType(CreateElement(TPasRecordType, TypeName, Parent));
  try
    Result.PackMode:=PackMode;
    NextToken;
    ParseRecordFieldList(Result,tkEnd);
  except
    FreeAndNil(Result);
    Raise;
  end;
end;

Function IsVisibility(S : String;  Out AVisibility :TPasMemberVisibility) : Boolean;

Const
  VNames : array[TPasMemberVisibility] of string =
    ('', 'private', 'protected', 'public', 'published', 'automated', '', '');
Var
  V : TPasMemberVisibility;

begin
  Result:=False;
  S:=lowerCase(S);
  For V :=Low(TPasMemberVisibility) to High(TPasMemberVisibility) do
    begin
    Result:=(VNames[V]<>'') and (S=VNames[V]);
    if Result then
      begin
      AVisibility := v;
      Exit;
      end;
    end;
end;

Function TPasParser.CheckVisibility(S : String; Out AVisibility :TPasMemberVisibility) : Boolean;

Var
  B : Boolean;

begin
  s := LowerCase(CurTokenString);
  B:=(S='strict');
  if B then
    begin
    NextToken;
    s:=LowerCase(CurTokenString);
    end;
  Result:=isVisibility(S,AVisibility);
  if Result then
    begin
    if B then
      case AVisibility of
        visPrivate   : AVisibility:=visStrictPrivate;
        visProtected : AVisibility:=visStrictProtected;
      else
        ParseExc(Format(SParserStrangeVisibility,[S]));
      end
    end
  else if B then
    ParseExc(SParserExpectVisibility);
end;

procedure TPasParser.ProcessMethod(AType: TPasClassType; IsClass : Boolean; AVisibility : TPasMemberVisibility);

var
  Proc: TPasProcedure;
  ProcType: TProcType;
begin
  ProcType:=GetProcTypeFromtoken(CurToken,isClass);
  Proc:=ParseProcedureOrFunctionDecl(AType,ProcType,AVisibility);
  if Proc.Parent is TPasOverloadedProc then
    TPasOverloadedProc(Proc.Parent).Overloads.Add(Proc)
  else
    AType.Members.Add(Proc);
end;

procedure TPasParser.ParseClassFields(AType: TPasClassType; Const AVisibility : TPasMemberVisibility; IsClassMember : Boolean);

Var
  VarList: TFPList;
  Element: TPasElement;
  I : Integer;

begin
  VarList := TFPList.Create;
  try
    ParseInlineVarDecl(AType, VarList, AVisibility, False);
    for i := 0 to VarList.Count - 1 do
      begin
      Element := TPasElement(VarList[i]);
      Element.Visibility := AVisibility;
      AType.Members.Add(Element);
      end;
  finally
    VarList.Free;
  end;
end;

procedure TPasParser.ParseClassMembers(AType: TPasClassType);

Var
  CurVisibility : TPasMemberVisibility;
  Element : TPasElement;
  PT : TProcType;

begin
  CurVisibility := visDefault;
  while (CurToken<>tkEnd) do
    begin
    case CurToken of
      tkVar,
      tkIdentifier:
        begin
        if CurToken=tkVar then
          ExpectToken(tkIdentifier);
        if Not CheckVisibility(CurtokenString,CurVisibility) then
          ParseClassFields(AType,CurVisibility,False);
        end;
      tkProcedure,tkFunction,tkConstructor,tkDestructor:
        ProcessMethod(AType,False,CurVisibility);
      tkclass:
        begin
         NextToken;
         if CurToken in [tkprocedure,tkFunction] then
           ProcessMethod(AType,True,CurVisibility)
         else if CurToken = tkVar then
           begin
           ExpectToken(tkIdentifier);
           ParseClassFields(AType,CurVisibility,True);
           end
         else if CurToken=tkProperty then
           begin
           ExpectToken(tkIdentifier);
           AType.Members.Add(ParseProperty(AType,CurtokenString,CurVisibility,True));
           end
         else
           ParseExc(SParserTypeSyntaxError)
        end;
      tkProperty:
        begin
        ExpectIdentifier;
        AType.Members.Add(ParseProperty(AType,CurtokenString,CurVisibility,False));
        end;
    end;
    NextToken;
    end;
end;
procedure TPasParser.DoParseClassType(AType: TPasClassType; SourceFileName: String; SourceLineNumber: Integer);

var
  CurVisibility: TPasMemberVisibility;
  Element : TPasElement;
  s: String;
  i: Integer;

begin
  // nettism/new delphi features
  if (CurToken=tkIdentifier) and (Atype.ObjKind in [okClass,okGeneric]) then
    begin
    s := LowerCase(CurTokenString);
    if (s = 'sealed') or (s = 'abstract') then
      begin
      AType.Modifiers.Add(s);
      NextToken;
      end;
    end;
  // Parse ancestor list
  Atype.IsForward:=(CurToken=tkSemiColon);
  if (CurToken=tkBraceOpen) then
    begin
    AType.AncestorType := ParseType(nil);
    while True do
      begin
      NextToken;
      if CurToken = tkBraceClose then
        break;
      UngetToken;
      ExpectToken(tkComma);
      Element:=ParseType(Nil); // search interface.
      if assigned(element) then
        AType.Interfaces.add(element);
      end;
    NextToken;
    AType.IsShortDefinition:=(CurToken=tkSemicolon);
    end;
  if not (AType.IsShortDefinition or AType.IsForward) then
    begin
    if (AType.ObjKind=okInterface) and (CurToken = tkSquaredBraceOpen) then
      begin
      ExpectToken(tkString);
      AType.InterfaceGUID := CurTokenString;
      ExpectToken(tkSquaredBraceClose);
      end;
    ParseClassMembers(AType);
    // Eat semicolon after class...end
    CheckHint(AType,true);
    end;
end;

function TPasParser.ParseClassDecl(Parent: TPasElement; const AClassName: String; AObjKind: TPasObjKind; PackMode : TPackMode= pmNone): TPasType;

Var
  SourcefileName : string;
  SourceLineNumber : Integer;

begin
  // Save current parsing position to get it correct in all cases
  SourceFilename := Scanner.CurFilename;
  SourceLinenumber := Scanner.CurRow;

  NextToken;

  if (AObjKind = okClass) and (CurToken = tkOf) then
  begin
    Result := TPasClassOfType(Engine.CreateElement(TPasClassOfType, AClassName,
      Parent, SourceFilename, SourceLinenumber));
    ExpectIdentifier;
    UngetToken;                // Only names are allowed as following type
    TPasClassOfType(Result).DestType := ParseType(Result);
    CheckHint(Result,true);
//    ExpectToken(tkSemicolon);
    exit;
  end;

  Result := TPasClassType(Engine.CreateElement(TPasClassType, AClassName,
    Parent, SourceFilename, SourceLinenumber));

  try
    TPasClassType(Result).ObjKind := AObjKind;
    TPasClassType(Result).PackMode:=PackMode;
    DoParseClassType(TPasClassType(Result),SourceFileName,SourceLineNumber);
  except
    Result.Free;
    raise;
  end;
end;

function TPasParser.CreateElement(AClass: TPTreeElement; const AName: String;
  AParent: TPasElement): TPasElement;
begin
  Result := Engine.CreateElement(AClass, AName, AParent,
    Scanner.CurFilename, Scanner.CurRow);
end;

function TPasParser.CreateElement(AClass: TPTreeElement; const AName: String;
  AParent: TPasElement; AVisibility: TPasMemberVisibility): TPasElement;
begin
  Result := Engine.CreateElement(AClass, AName, AParent, AVisibility,
    Scanner.CurFilename, Scanner.CurRow);
end;

function TPasParser.CreateFunctionType(const AName, AResultName: String;
  AParent: TPasElement; UseParentAsResultParent: Boolean): TPasFunctionType;
begin
  Result:=Engine.CreateFunctionType(AName,AResultName,
                                    AParent,UseParentAsResultParent,
                                    Scanner.CurFilename,Scanner.CurRow);
end;



procedure DoInit;
var
  c: Char;
begin
  for c:=low(char) to high(char) do
  begin
    IsIdentStart[c]:=c in ['a'..'z','A'..'Z','_'];
  end;
end;

initialization
  DoInit;

end.
