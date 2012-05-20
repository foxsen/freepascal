unit character;

interface
{$ifndef VER2_4}
{$mode objfpc}
{$H+}
{$PACKENUM 1}
{$SCOPEDENUMS ON}

type
  // Unicode General Category
  TUnicodeCategory = (
    ucUppercaseLetter,             // Lu = Letter, uppercase
    ucLowercaseLetter,             // Ll = Letter, lowercase
    ucTitlecaseLetter,             // Lt = Letter, titlecase
    ucModifierLetter,              // Lm = Letter, modifier
    ucOtherLetter,                 // Lo = Letter, other
    
    ucNonSpacingMark,              // Mn = Mark, nonspacing
    ucCombiningMark,               // Mc = Mark, spacing combining
    ucEnclosingMark,               // Me = Mark, enclosing
    
    ucDecimalNumber,               // Nd = Number, decimal digit
    ucLetterNumber,                // Nl = Number, letter
    ucOtherNumber,                 // No = Number, other
    
    ucConnectPunctuation,          // Pc = Punctuation, connector
    ucDashPunctuation,             // Pd = Punctuation, dash
    ucOpenPunctuation,             // Ps = Punctuation, open
    ucClosePunctuation,            // Pe = Punctuation, close
    ucInitialPunctuation,          // Pi = Punctuation, initial quote (may behave like Ps or Pe depending on usage)
    ucFinalPunctuation,            // Pf = Punctuation, final quote (may behave like Ps or Pe depending on usage)
    ucOtherPunctuation,            // Po = Punctuation, other
    
    ucMathSymbol,                  // Sm = Symbol, math
    ucCurrencySymbol,              // Sc = Symbol, currency
    ucModifierSymbol,              // Sk = Symbol, modifier
    ucOtherSymbol,                 // So = Symbol, other
    
    ucSpaceSeparator,              // Zs = Separator, space
    ucLineSeparator,               // Zl = Separator, line
    ucParagraphSeparator,          // Zp = Separator, paragraph
    
    ucControl,                     // Cc = Other, control
    ucFormat,                      // Cf = Other, format
    ucSurrogate,                   // Cs = Other, surrogate
    ucPrivateUse,                  // Co = Other, private use
    ucUnassigned                   // Cn = Other, not assigned (including noncharacters)  
  );
  TUnicodeCategorySet = set of TUnicodeCategory;

  { TCharacter }

  TCharacter = class sealed
  private
    class function TestCategory(const AString : UnicodeString; AIndex : Integer; ACategory : TUnicodeCategory) : Boolean; overload; static;
    class function TestCategory(const AString : UnicodeString; AIndex : Integer; ACategory : TUnicodeCategorySet) : Boolean; overload; static;
  public
    constructor Create;

    class function ConvertFromUtf32(AChar : UCS4Char) : UnicodeString; static;
    class function ConvertToUtf32(const AString : UnicodeString; AIndex : Integer) : UCS4Char; overload; static;
    class function ConvertToUtf32(const AString : UnicodeString; AIndex : Integer; out ACharLength : Integer) : UCS4Char; overload; static;
    class function ConvertToUtf32(const AHighSurrogate, ALowSurrogate : UnicodeChar) : UCS4Char; overload; static;
    
    class function GetNumericValue(AChar : UnicodeChar) : Double; static; overload;
    class function GetNumericValue(const AString : UnicodeString; AIndex : Integer) : Double; overload; static;
    
    class function GetUnicodeCategory(AChar : UnicodeChar) : TUnicodeCategory; overload; static; inline;
    class function GetUnicodeCategory(const AString : UnicodeString; AIndex : Integer) : TUnicodeCategory; overload; static;
    
    class function IsControl(AChar : UnicodeChar) : Boolean; overload; static; inline;
    class function IsControl(const AString : UnicodeString; AIndex : Integer) : Boolean; overload; static; inline;
    
    class function IsDigit(AChar : UnicodeChar) : Boolean; overload; static; inline;
    class function IsDigit(const AString : UnicodeString; AIndex : Integer) : Boolean; overload; static; inline;
    
    class function IsSurrogate(AChar : UnicodeChar) : Boolean; overload; static; inline;
    class function IsSurrogate(const AString : UnicodeString; AIndex : Integer) : Boolean; overload; static;  
    class function IsHighSurrogate(AChar : UnicodeChar) : Boolean; overload; static; inline;
    class function IsHighSurrogate(const AString : UnicodeString; AIndex : Integer) : Boolean; overload; static;  
    class function IsLowSurrogate(AChar : UnicodeChar) : Boolean; overload; static; inline;
    class function IsLowSurrogate(const AString : UnicodeString; AIndex : Integer) : Boolean; overload; static;
    class function IsSurrogatePair(const AHighSurrogate, ALowSurrogate : UnicodeChar) : Boolean; overload; static; inline; inline;
    class function IsSurrogatePair(const AString : UnicodeString; AIndex : Integer) : Boolean; overload; static;
    
    class function IsLetter(AChar : UnicodeChar) : Boolean; overload; static; inline;
    class function IsLetter(const AString : UnicodeString; AIndex : Integer) : Boolean; overload; static; inline;
    
    class function IsLetterOrDigit(AChar : UnicodeChar) : Boolean; overload; static; inline;
    class function IsLetterOrDigit(const AString : UnicodeString; AIndex : Integer) : Boolean; overload; static; inline;
    
    class function IsLower(AChar : UnicodeChar) : Boolean; overload; static; inline; inline;
    class function IsLower(const AString : UnicodeString; AIndex : Integer) : Boolean; overload; static; inline;

    class function IsNumber(AChar : UnicodeChar) : Boolean; overload; static; inline;
    class function IsNumber(const AString : UnicodeString; AIndex : Integer) : Boolean; overload; static;

    class function IsPunctuation(AChar : UnicodeChar) : Boolean; overload; static; inline;
    class function IsPunctuation(const AString : UnicodeString; AIndex : Integer) : Boolean; overload; static; inline;

    class function IsSeparator(AChar : UnicodeChar) : Boolean; overload; static; inline;
    class function IsSeparator(const AString : UnicodeString; AIndex : Integer) : Boolean; overload; static; inline;

    class function IsSymbol(AChar : UnicodeChar) : Boolean; overload; static; inline;
    class function IsSymbol(const AString : UnicodeString; AIndex : Integer) : Boolean; overload; static; inline;

    class function IsUpper(AChar : UnicodeChar) : Boolean; overload; static; inline;
    class function IsUpper(const AString : UnicodeString; AIndex : Integer) : Boolean; overload; static; inline;

    class function IsWhiteSpace(AChar : UnicodeChar) : Boolean; overload; static; inline;
    class function IsWhiteSpace(const AString : UnicodeString; AIndex : Integer) : Boolean; overload; static;

    class function ToLower(AChar : UnicodeChar) : UnicodeChar; overload; static;
    class function ToLower(const AString : UnicodeString) : UnicodeString; overload; static;

    class function ToUpper(AChar : UnicodeChar) : UnicodeChar; overload; static;
    class function ToUpper(const AString : UnicodeString) : UnicodeString; overload; static;
  end;

  // flat functions
  function ConvertFromUtf32(AChar : UCS4Char) : UnicodeString;
  function ConvertToUtf32(const AString : UnicodeString; AIndex : Integer) : UCS4Char; overload;
  function ConvertToUtf32(const AString : UnicodeString; AIndex : Integer; out ACharLength : Integer) : UCS4Char; overload;
  function ConvertToUtf32(const AHighSurrogate, ALowSurrogate : UnicodeChar) : UCS4Char; overload;
  function GetNumericValue(AChar : UnicodeChar) : Double; overload;
  function GetNumericValue(const AString : UnicodeString; AIndex : Integer) : Double; overload;
  function GetUnicodeCategory(AChar : UnicodeChar) : TUnicodeCategory; overload;
  function GetUnicodeCategory(const AString : UnicodeString; AIndex : Integer) : TUnicodeCategory; overload;
  function IsControl(AChar : UnicodeChar) : Boolean; overload;
  function IsControl(const AString : UnicodeString; AIndex : Integer) : Boolean; overload;
  function IsDigit(AChar : UnicodeChar) : Boolean; overload;
  function IsDigit(const AString : UnicodeString; AIndex : Integer) : Boolean; overload;
  function IsSurrogate(AChar : UnicodeChar) : Boolean; overload;
  function IsSurrogate(const AString : UnicodeString; AIndex : Integer) : Boolean; overload;
  function IsHighSurrogate(AChar : UnicodeChar) : Boolean; overload;
  function IsHighSurrogate(const AString : UnicodeString; AIndex : Integer) : Boolean; overload;
  function IsLowSurrogate(AChar : UnicodeChar) : Boolean; overload;
  function IsLowSurrogate(const AString : UnicodeString; AIndex : Integer) : Boolean; overload;
  function IsSurrogatePair(const AHighSurrogate, ALowSurrogate : UnicodeChar) : Boolean; overload;
  function IsSurrogatePair(const AString : UnicodeString; AIndex : Integer) : Boolean; overload;
  function IsLetter(AChar : UnicodeChar) : Boolean; overload;
  function IsLetter(const AString : UnicodeString; AIndex : Integer) : Boolean; overload;
  function IsLetterOrDigit(AChar : UnicodeChar) : Boolean; overload;
  function IsLetterOrDigit(const AString : UnicodeString; AIndex : Integer) : Boolean; overload;
  function IsLower(AChar : UnicodeChar) : Boolean; overload;
  function IsLower(const AString : UnicodeString; AIndex : Integer) : Boolean; overload;
  function IsNumber(AChar : UnicodeChar) : Boolean; overload;
  function IsNumber(const AString : UnicodeString; AIndex : Integer) : Boolean; overload;
  function IsPunctuation(AChar : UnicodeChar) : Boolean; overload;
  function IsPunctuation(const AString : UnicodeString; AIndex : Integer) : Boolean; overload;
  function IsSeparator(AChar : UnicodeChar) : Boolean; overload;
  function IsSeparator(const AString : UnicodeString; AIndex : Integer) : Boolean; overload;
  function IsSymbol(AChar : UnicodeChar) : Boolean; overload;
  function IsSymbol(const AString : UnicodeString; AIndex : Integer) : Boolean; overload;
  function IsUpper(AChar : UnicodeChar) : Boolean; overload;
  function IsUpper(const AString : UnicodeString; AIndex : Integer) : Boolean; overload;
  function IsWhiteSpace(AChar : UnicodeChar) : Boolean; overload;
  function IsWhiteSpace(const AString : UnicodeString; AIndex : Integer) : Boolean; overload;
  function ToLower(AChar : UnicodeChar) : UnicodeChar; overload;
  function ToLower(const AString : UnicodeString) : UnicodeString; overload;
  function ToUpper(AChar : UnicodeChar) : UnicodeChar; overload;
  function ToUpper(const AString : UnicodeString) : UnicodeString; overload;
{$endif VER2_4}

implementation
{$ifndef VER2_4}
uses
  SysUtils,
  RtlConsts;

type  
  PUC_Prop = ^TUC_Prop;
  TUC_Prop = packed record
    Category        : TUnicodeCategory;
    NumericValue    : Double;
    SimpleUpperCase : DWord;
    SimpleLowerCase : DWord;
    WhiteSpace      : Boolean;
  end; 
  
  {$INCLUDE unicodedata.inc} // For BMP code points
  {$INCLUDE unicodedata2.inc} // For other planes
  
const              
  LOW_SURROGATE_BEGIN  = Word($DC00); 
  LOW_SURROGATE_END    = Word($DFFF); 
  
  HIGH_SURROGATE_BEGIN = Word($D800); 
  HIGH_SURROGATE_END   = Word($DBFF);
  HIGH_SURROGATE_COUNT = HIGH_SURROGATE_END - HIGH_SURROGATE_BEGIN + 1;
  UCS4_HALF_BASE       = LongWord($10000);
  UCS4_HALF_MASK       = Word($3FF);
  MAX_LEGAL_UTF32      = $10FFFF;
    
const
  LETTER_CATEGORIES = [
    TUnicodeCategory.ucUppercaseLetter, TUnicodeCategory.ucLowercaseLetter,
    TUnicodeCategory.ucTitlecaseLetter, TUnicodeCategory.ucModifierLetter,
    TUnicodeCategory.ucOtherLetter
  ];
  LETTER_OR_DIGIT_CATEGORIES =
    LETTER_CATEGORIES +
    [TUnicodeCategory.ucDecimalNumber,TUnicodeCategory.ucLetterNumber];
  NUMBER_CATEGORIES =
    [ TUnicodeCategory.ucDecimalNumber, TUnicodeCategory.ucLetterNumber,
      TUnicodeCategory.ucOtherNumber
    ];
  PUNCTUATION_CATEGORIES = [
    TUnicodeCategory.ucConnectPunctuation, TUnicodeCategory.ucDashPunctuation,
    TUnicodeCategory.ucOpenPunctuation, TUnicodeCategory.ucClosePunctuation,
    TUnicodeCategory.ucInitialPunctuation, TUnicodeCategory.ucFinalPunctuation,
    TUnicodeCategory.ucOtherPunctuation
  ];
  SEPARATOR_CATEGORIES =
    [ TUnicodeCategory.ucSpaceSeparator, TUnicodeCategory.ucLineSeparator,
      TUnicodeCategory.ucParagraphSeparator
    ];
  SYMBOL_CATEGORIES =
    [ TUnicodeCategory.ucMathSymbol, TUnicodeCategory.ucCurrencySymbol,
      TUnicodeCategory.ucModifierSymbol, TUnicodeCategory.ucOtherSymbol
    ];

function GetProps(const ACodePoint : Word) : PUC_Prop; inline;
begin
  Result:=
    @UC_PROP_ARRAY[
       UC_TABLE_2[
         (UC_TABLE_1[WordRec(ACodePoint).Hi] * 256) +
         WordRec(ACodePoint).Lo
       ]
     ];
end;

function GetProps(const AHighS, ALowS : UnicodeChar): PUC_Prop; inline;
begin
  Result:=
    @UC_PROP_ARRAY[
       UCO_TABLE_2[
         (UCO_TABLE_1[Word(AHighS)-HIGH_SURROGATE_BEGIN] * HIGH_SURROGATE_COUNT) +
         Word(ALowS) - LOW_SURROGATE_BEGIN
       ]
     ];
end;

procedure FromUCS4(const AValue : UCS4Char; var AHighS, ALowS : UnicodeChar);
begin
  AHighS := UnicodeChar((AValue - $10000) shr 10 + $d800);
  ALowS := UnicodeChar((AValue - $10000) and $3ff + $dc00);
end;

function ConvertFromUtf32(AChar: UCS4Char): UnicodeString;
begin
  Result := TCharacter.ConvertFromUtf32(AChar);
end;

function ConvertToUtf32(const AString: UnicodeString; AIndex: Integer): UCS4Char;
begin
  Result := TCharacter.ConvertToUtf32(AString, AIndex);
end;

function ConvertToUtf32(const AString: UnicodeString; AIndex: Integer; out ACharLength: Integer): UCS4Char;
begin
  Result := TCharacter.ConvertToUtf32(AString, AIndex, ACharLength);
end;

function ConvertToUtf32(const AHighSurrogate, ALowSurrogate: UnicodeChar): UCS4Char;
begin
  Result := TCharacter.ConvertToUtf32(AHighSurrogate, ALowSurrogate);
end;

function GetNumericValue(AChar: UnicodeChar): Double;
begin
  Result := TCharacter.GetNumericValue(AChar);
end;

function GetNumericValue(const AString: UnicodeString; AIndex: Integer): Double;
begin
  Result := TCharacter.GetNumericValue(AString, AIndex);
end;

function GetUnicodeCategory(AChar: UnicodeChar): TUnicodeCategory;
begin
  Result := TCharacter.GetUnicodeCategory(AChar);
end;

function GetUnicodeCategory(const AString: UnicodeString; AIndex: Integer): TUnicodeCategory;
begin
  Result := TCharacter.GetUnicodeCategory(AString, AIndex);
end;

function IsControl(AChar: UnicodeChar): Boolean;
begin
  Result := TCharacter.IsControl(AChar);
end;

function IsControl(const AString: UnicodeString; AIndex: Integer): Boolean;
begin
  Result := TCharacter.IsControl(AString, AIndex);
end;

function IsDigit(AChar: UnicodeChar): Boolean;
begin
  Result := TCharacter.IsDigit(AChar);
end;

function IsDigit(const AString: UnicodeString; AIndex: Integer): Boolean;
begin
  Result := TCharacter.IsDigit(AString, AIndex);
end;

function IsSurrogate(AChar: UnicodeChar): Boolean;
begin
  Result := TCharacter.IsSurrogate(AChar);
end;

function IsSurrogate(const AString: UnicodeString; AIndex: Integer): Boolean;
begin
  Result := TCharacter.IsSurrogate(AString, AIndex);
end;

function IsHighSurrogate(AChar: UnicodeChar): Boolean;
begin
  Result := TCharacter.IsHighSurrogate(AChar);
end;

function IsHighSurrogate(const AString: UnicodeString; AIndex: Integer): Boolean;
begin
  Result := TCharacter.IsHighSurrogate(AString, AIndex);
end;

function IsLowSurrogate(AChar: UnicodeChar): Boolean;
begin
  Result := TCharacter.IsLowSurrogate(AChar);
end;

function IsLowSurrogate(const AString: UnicodeString; AIndex: Integer): Boolean;
begin
  Result := TCharacter.IsLowSurrogate(AString, AIndex);
end;

function IsSurrogatePair(const AHighSurrogate, ALowSurrogate: UnicodeChar): Boolean;
begin
  Result := TCharacter.IsSurrogatePair(AHighSurrogate, ALowSurrogate);
end;

function IsSurrogatePair(const AString: UnicodeString; AIndex: Integer): Boolean;
begin
  Result := TCharacter.IsSurrogatePair(AString, AIndex);
end;

function IsLetter(AChar: UnicodeChar): Boolean;
begin
  Result := TCharacter.IsLetter(AChar);
end;

function IsLetter(const AString: UnicodeString; AIndex: Integer): Boolean;
begin
  Result := TCharacter.IsLetter(AString, AIndex);
end;

function IsLetterOrDigit(AChar: UnicodeChar): Boolean;
begin
  Result := TCharacter.IsLetterOrDigit(AChar);
end;

function IsLetterOrDigit(const AString: UnicodeString; AIndex: Integer): Boolean;
begin
  Result := TCharacter.IsLetterOrDigit(AString, AIndex);
end;

function IsLower(AChar: UnicodeChar): Boolean;
begin
  Result := TCharacter.IsLower(AChar);
end;

function IsLower(const AString: UnicodeString; AIndex: Integer): Boolean;
begin
  Result := TCharacter.IsLower(AString, AIndex);
end;

function IsNumber(AChar: UnicodeChar): Boolean;
begin
  Result := TCharacter.IsNumber(AChar);
end;

function IsNumber(const AString: UnicodeString; AIndex: Integer): Boolean;
begin
  Result := TCharacter.IsNumber(AString, AIndex);
end;

function IsPunctuation(AChar: UnicodeChar): Boolean;
begin
  Result := TCharacter.IsPunctuation(AChar);
end;

function IsPunctuation(const AString: UnicodeString; AIndex: Integer): Boolean;
begin
  Result := TCharacter.IsPunctuation(AString, AIndex);
end;

function IsSeparator(AChar: UnicodeChar): Boolean;
begin
  Result := TCharacter.IsSeparator(AChar);
end;

function IsSeparator(const AString: UnicodeString; AIndex: Integer): Boolean;
begin
  Result := TCharacter.IsSeparator(AString, AIndex);
end;

function IsSymbol(AChar: UnicodeChar): Boolean;
begin
  Result := TCharacter.IsSymbol(AChar);
end;

function IsSymbol(const AString: UnicodeString; AIndex: Integer): Boolean;
begin
  Result := TCharacter.IsSymbol(AString, AIndex);
end;

function IsUpper(AChar: UnicodeChar): Boolean;
begin
  Result := TCharacter.IsUpper(AChar);
end;

function IsUpper(const AString: UnicodeString; AIndex: Integer): Boolean;
begin
  Result := TCharacter.IsUpper(AString, AIndex);
end;

function IsWhiteSpace(AChar: UnicodeChar): Boolean;
begin
  Result := TCharacter.IsWhiteSpace(AChar);
end;

function IsWhiteSpace(const AString: UnicodeString; AIndex: Integer): Boolean;
begin
  Result := TCharacter.IsWhiteSpace(AString, AIndex);
end;

function ToLower(AChar: UnicodeChar): UnicodeChar;
begin
  Result := TCharacter.ToLower(AChar);
end;

function ToLower(const AString: UnicodeString): UnicodeString;
begin
  Result := TCharacter.ToLower(AString);
end;

function ToUpper(AChar: UnicodeChar): UnicodeChar;
begin
  Result := TCharacter.ToUpper(AChar);
end;

function ToUpper(const AString: UnicodeString): UnicodeString;
begin
  Result := TCharacter.ToUpper(AString);
end;

{ TCharacter }

class function TCharacter.TestCategory(
  const AString : UnicodeString;
        AIndex  : Integer;
        ACategory : TUnicodeCategory
) : Boolean;
var
  pu : PUC_Prop;
begin
  if (AIndex < 1) or (AIndex > Length(AString)) then
    raise EArgumentOutOfRangeException.CreateFmt(SStringIndexOutOfRange, [AIndex, Length(AString)]);
  pu := GetProps(Word(AString[AIndex]));
  if (pu^.Category = TUnicodeCategory.ucSurrogate) then begin
    if not IsSurrogatePair(AString,AIndex) then
      raise EArgumentException.Create(SInvalidUnicodeCodePointSequence);
    pu := GetProps(AString[AIndex],AString[AIndex+1]);
  end;
  Result := (pu^.Category = ACategory);
end;

class function TCharacter.TestCategory(
  const AString : UnicodeString;
        AIndex : Integer;
        ACategory : TUnicodeCategorySet
) : Boolean;
var
  pu : PUC_Prop;
begin
  if (AIndex < 1) or (AIndex > Length(AString)) then
    raise EArgumentOutOfRangeException.CreateFmt(SStringIndexOutOfRange, [AIndex, Length(AString)]);
  pu := GetProps(Word(AString[AIndex]));
  if (pu^.Category = TUnicodeCategory.ucSurrogate) then begin
    if not IsSurrogatePair(AString,AIndex) then
      raise EArgumentException.Create(SInvalidUnicodeCodePointSequence);
    pu := GetProps(AString[AIndex],AString[AIndex+1]);
  end;
  Result := (pu^.Category in ACategory);
end;

constructor TCharacter.Create;
begin
  raise ENoConstructException.CreateFmt(SClassCantBeConstructed, [ClassName]);
end;

class function TCharacter.ConvertFromUtf32(AChar : UCS4Char) : UnicodeString;
begin
  if AChar < UCS4_HALF_BASE then
  begin
    if IsSurrogate(UnicodeChar(AChar)) then
      raise EArgumentOutOfRangeException.CreateFmt(SInvalidUTF32Char, [AChar]);
    Result := UnicodeChar(AChar);
  end
  else
  begin
    if AChar > MAX_LEGAL_UTF32 then
      raise EArgumentOutOfRangeException.CreateFmt(SInvalidUTF32Char, [AChar]);
    SetLength(Result, 2);
    AChar := AChar - UCS4_HALF_BASE;
    Result[1] := UnicodeChar((AChar shr 10) + HIGH_SURROGATE_BEGIN);
    Result[2] := UnicodeChar((AChar and UCS4_HALF_MASK) + LOW_SURROGATE_BEGIN);
  end;
end;

class function TCharacter.ConvertToUtf32(const AString : UnicodeString; AIndex : Integer) : UCS4Char; overload;
begin
  if (AIndex < 1) or (AIndex > Length(AString)) then
    raise EArgumentOutOfRangeException.CreateFmt(SStringIndexOutOfRange, [AIndex, Length(AString)]);
  Result := Word(AString[AIndex]);
  if IsHighSurrogate(UnicodeChar(Result)) then
  begin
    if Length(AString) < Succ(AIndex) then
      raise EArgumentException.CreateFmt(SInvalidHighSurrogate, [AIndex]);
    Result := ConvertToUtf32(UnicodeChar(Result), AString[Succ(AIndex)]);
  end;
end;

class function TCharacter.ConvertToUtf32(const AString : UnicodeString; AIndex : Integer; out ACharLength : Integer) : UCS4Char; overload;
begin
  if (AIndex < 1) or (AIndex > Length(AString)) then
    raise EArgumentOutOfRangeException.CreateFmt(SStringIndexOutOfRange, [AIndex, Length(AString)]);
  Result := Word(AString[AIndex]);
  if IsHighSurrogate(UnicodeChar(Result)) then
  begin
    if Length(AString) < Succ(AIndex) then
      raise EArgumentException.CreateFmt(SInvalidHighSurrogate, [AIndex]);
    Result := ConvertToUtf32(UnicodeChar(Result), AString[Succ(AIndex)]);
    ACharLength := 2;
  end
  else
    ACharLength := 1;
end;

class function TCharacter.ConvertToUtf32(const AHighSurrogate, ALowSurrogate : UnicodeChar) : UCS4Char; overload;
begin
  if not IsHighSurrogate(AHighSurrogate) then
    raise EArgumentOutOfRangeException.CreateFmt(SHighSurrogateOutOfRange, [Word(AHighSurrogate)]);
  if not IsLowSurrogate(ALowSurrogate) then
    raise EArgumentOutOfRangeException.CreateFmt(SLowSurrogateOutOfRange, [Word(ALowSurrogate)]);
  Result := (UCS4Char(AHighSurrogate) - HIGH_SURROGATE_BEGIN) shl 10 + (UCS4Char(ALowSurrogate) - LOW_SURROGATE_BEGIN) + UCS4_HALF_BASE;
end;

class function TCharacter.GetNumericValue(AChar : UnicodeChar) : Double;
begin
  Result := GetProps(Word(AChar))^.NumericValue;
end;

class function TCharacter.GetNumericValue(
  const AString : UnicodeString;  
        AIndex  : Integer
) : Double;
var
  pu : PUC_Prop;
begin
  if (AIndex < 1) or (AIndex > Length(AString)) then
    raise EArgumentOutOfRangeException.CreateFmt(SStringIndexOutOfRange, [AIndex, Length(AString)]);
  pu := GetProps(Word(AString[AIndex]));
  if (pu^.Category = TUnicodeCategory.ucSurrogate) then begin
    if not IsSurrogatePair(AString,AIndex) then
      raise EArgumentException.Create(SInvalidUnicodeCodePointSequence);
    pu := GetProps(AString[AIndex],AString[AIndex+1]);
  end;
  Result := pu^.NumericValue;
end;  

class function TCharacter.GetUnicodeCategory(AChar : UnicodeChar) : TUnicodeCategory;
begin   
  Result := GetProps(Word(AChar))^.Category;  
end;

class function TCharacter.GetUnicodeCategory(
  const AString : UnicodeString;  
        AIndex  : Integer
) : TUnicodeCategory;
var
  pu : PUC_Prop;
begin   
  if (AIndex < 1) or (AIndex > Length(AString)) then
    raise EArgumentOutOfRangeException.CreateFmt(SStringIndexOutOfRange, [AIndex, Length(AString)]);
  pu := GetProps(Word(AString[AIndex]));
  if (pu^.Category = TUnicodeCategory.ucSurrogate) then begin
    if not IsSurrogatePair(AString,AIndex) then
      raise EArgumentException.Create(SInvalidUnicodeCodePointSequence);
    pu := GetProps(AString[AIndex],AString[AIndex+1]);
  end;
  Result := pu^.Category;
end;

class function TCharacter.IsControl(AChar : UnicodeChar) : Boolean;
begin  
  Result := (GetProps(Word(AChar))^.Category = TUnicodeCategory.ucControl);
end;

class function TCharacter.IsControl(
  const AString : UnicodeString;  
        AIndex  : Integer
) : Boolean;
begin
  Result := TestCategory(AString,AIndex,TUnicodeCategory.ucControl);
end;

class function TCharacter.IsDigit(AChar : UnicodeChar) : Boolean;
begin 
  Result := (GetProps(Word(AChar))^.Category = TUnicodeCategory.ucDecimalNumber);
end;

class function TCharacter.IsDigit(
  const AString : UnicodeString;  
        AIndex  : Integer
) : Boolean;
begin
  Result := TestCategory(AString,AIndex,TUnicodeCategory.ucDecimalNumber);
end;

class function TCharacter.IsSurrogate(AChar : UnicodeChar) : Boolean;
begin   
  Result := (GetProps(Word(AChar))^.Category = TUnicodeCategory.ucSurrogate);
end;

class function TCharacter.IsSurrogate(
  const AString : UnicodeString;  
        AIndex  : Integer
) : Boolean;
begin        
  if (AIndex < 1) or (AIndex > Length(AString)) then
    raise EArgumentOutOfRangeException.CreateFmt(SStringIndexOutOfRange, [AIndex, Length(AString)]);
  Result := IsSurrogate(AString[AIndex]);
end;

class function TCharacter.IsHighSurrogate(AChar : UnicodeChar) : Boolean;
begin 
  Result := (GetProps(Word(AChar))^.Category = TUnicodeCategory.ucSurrogate) and
            (Word(AChar) >= HIGH_SURROGATE_BEGIN) and 
            (Word(AChar) <= HIGH_SURROGATE_END);
end;

class function TCharacter.IsHighSurrogate(
  const AString : UnicodeString;  
        AIndex  : Integer
) : Boolean;
begin        
  if (AIndex < 1) or (AIndex > Length(AString)) then
    raise EArgumentOutOfRangeException.CreateFmt(SStringIndexOutOfRange, [AIndex, Length(AString)]);
  Result := IsHighSurrogate(AString[AIndex]);
end;

class function TCharacter.IsLowSurrogate(AChar : UnicodeChar) : Boolean;
begin   
  Result := (GetProps(Word(AChar))^.Category = TUnicodeCategory.ucSurrogate) and
            (Word(AChar) >= LOW_SURROGATE_BEGIN) and 
            (Word(AChar) <= LOW_SURROGATE_END); 
end;

class function TCharacter.IsLowSurrogate(
  const AString : UnicodeString;  
        AIndex  : Integer
) : Boolean;
begin        
  if (AIndex < 1) or (AIndex > Length(AString)) then
    raise EArgumentOutOfRangeException.CreateFmt(SStringIndexOutOfRange, [AIndex, Length(AString)]);
  Result := IsLowSurrogate(AString[AIndex]);
end;

class function TCharacter.IsSurrogatePair(
  const AHighSurrogate,
        ALowSurrogate   : UnicodeChar
) : Boolean;
begin
  Result :=
    ( (Word(AHighSurrogate) >= HIGH_SURROGATE_BEGIN) and
      (Word(AHighSurrogate) <= HIGH_SURROGATE_END)
    ) and
    ( (Word(ALowSurrogate) >= LOW_SURROGATE_BEGIN) and
      (Word(ALowSurrogate) <= LOW_SURROGATE_END)
    )
end;

class function TCharacter.IsSurrogatePair(
  const AString : UnicodeString;
        AIndex  : Integer
) : Boolean;
begin
  if (AIndex < 1) or (AIndex > Length(AString)) then
    raise EArgumentOutOfRangeException.CreateFmt(SStringIndexOutOfRange, [AIndex, Length(AString)]);
  if not IsHighSurrogate(AString[AIndex]) then begin
    Result := False;
    exit;
  end;
  if ((AIndex+1) > Length(AString)) then
    raise EArgumentOutOfRangeException.CreateFmt(SStringIndexOutOfRange, [AIndex+1, Length(AString)]);
  Result := IsSurrogatePair(AString[AIndex],AString[AIndex+1]);
end;

class function TCharacter.IsLetter(AChar : UnicodeChar) : Boolean;
begin 
  Result := (GetProps(Word(AChar))^.Category in LETTER_CATEGORIES);
end;

class function TCharacter.IsLetter(
  const AString : UnicodeString;  
        AIndex  : Integer
) : Boolean;
begin
  Result := TestCategory(AString,AIndex,LETTER_CATEGORIES);
end;

class function TCharacter.IsLetterOrDigit(AChar : UnicodeChar) : Boolean;
begin 
  Result := (GetProps(Word(AChar))^.Category in LETTER_OR_DIGIT_CATEGORIES);
end;

class function TCharacter.IsLetterOrDigit(
  const AString : UnicodeString;  
        AIndex  : Integer
) : Boolean;
begin
  Result := TestCategory(AString,AIndex,LETTER_OR_DIGIT_CATEGORIES);
end;

class function TCharacter.IsLower(AChar : UnicodeChar) : Boolean;
begin        
  Result := (GetProps(Word(AChar))^.Category = TUnicodeCategory.ucLowercaseLetter);
end;

class function TCharacter.IsLower(
  const AString : UnicodeString;  
        AIndex  : Integer
) : Boolean;
begin
  Result := TestCategory(AString,AIndex,TUnicodeCategory.ucLowercaseLetter);
end;

class function TCharacter.IsNumber(AChar : UnicodeChar) : Boolean;
begin
  Result := (GetProps(Word(AChar))^.Category in NUMBER_CATEGORIES);
end;

class function TCharacter.IsNumber(
  const AString : UnicodeString;
        AIndex  : Integer
) : Boolean;
begin
  Result := TestCategory(AString,AIndex,NUMBER_CATEGORIES);
end;

class function TCharacter.IsPunctuation(AChar : UnicodeChar) : Boolean;
begin
  Result := (GetProps(Word(AChar))^.Category in PUNCTUATION_CATEGORIES);
end;

class function TCharacter.IsPunctuation(
  const AString : UnicodeString;
        AIndex  : Integer
) : Boolean;
begin
  Result := TestCategory(AString,AIndex,PUNCTUATION_CATEGORIES);
end;

class function TCharacter.IsSeparator(AChar: UnicodeChar): Boolean;
begin
  Result := (GetProps(Word(AChar))^.Category in SEPARATOR_CATEGORIES);
end;

class function TCharacter.IsSeparator(
  const AString : UnicodeString;
        AIndex  : Integer
) : Boolean;
begin
  Result := TestCategory(AString,AIndex,SEPARATOR_CATEGORIES);
end;

class function TCharacter.IsSymbol(AChar: UnicodeChar): Boolean;
begin
  Result := (GetProps(Word(AChar))^.Category in SYMBOL_CATEGORIES);
end;

class function TCharacter.IsSymbol(
  const AString : UnicodeString;
        AIndex  : Integer
) : Boolean;
begin
  Result := TestCategory(AString,AIndex,SYMBOL_CATEGORIES);
end;

class function TCharacter.IsUpper(AChar : UnicodeChar) : Boolean;
begin
  Result := (GetProps(Word(AChar))^.Category = TUnicodeCategory.ucUppercaseLetter);
end;

class function TCharacter.IsUpper(
  const AString : UnicodeString;
        AIndex  : Integer
) : Boolean;
begin
  Result := TestCategory(AString,AIndex,TUnicodeCategory.ucUppercaseLetter);
end;

class function TCharacter.IsWhiteSpace(AChar : UnicodeChar) : Boolean;
begin
  Result := GetProps(Word(AChar))^.WhiteSpace;
end;

class function TCharacter.IsWhiteSpace(
  const AString : UnicodeString;
        AIndex  : Integer
) : Boolean;
var
  pu : PUC_Prop;
begin
  if (AIndex < 1) or (AIndex > Length(AString)) then
    raise EArgumentOutOfRangeException.CreateFmt(SStringIndexOutOfRange, [AIndex, Length(AString)]);
  pu := GetProps(Word(AString[AIndex]));
  if (pu^.Category = TUnicodeCategory.ucSurrogate) then begin
    if not IsSurrogatePair(AString,AIndex) then
      raise EArgumentException.Create(SInvalidUnicodeCodePointSequence);
    pu := GetProps(AString[AIndex],AString[AIndex+1]);
  end;
  Result := pu^.WhiteSpace;
end;

class function TCharacter.ToLower(AChar : UnicodeChar) : UnicodeChar;
begin
  Result := UnicodeChar(GetProps(Word(AChar))^.SimpleLowerCase);
  if (Result = UnicodeChar(0)) then
    Result := AChar;
end;

class function TCharacter.ToLower(const AString : UnicodeString) : UnicodeString;
var
  i, c : SizeInt;
  pp, pr : PUnicodeChar;
  pu : PUC_Prop;
  locIsSurrogate : Boolean;
begin
  c := Length(AString);
  SetLength(Result,2*c);
  if (c > 0) then begin
    pp := @AString[1];
    pr := @Result[1];
    i := 1;
    while (i <= c) do begin
      pu := GetProps(Word(pp^));
      locIsSurrogate := (pu^.Category = TUnicodeCategory.ucSurrogate);
      if locIsSurrogate then begin
        if not IsSurrogatePair(AString,i) then
          raise EArgumentException.Create(SInvalidUnicodeCodePointSequence);
        pu := GetProps(pp^,AString[i+1]);
      end;
      if (pu^.SimpleLowerCase = 0) then begin
        pr^ := pp^;
        if locIsSurrogate then begin
          Inc(pp);
          Inc(pr);
          Inc(i);
          pr^ := pp^;
        end;
      end else begin
        if (pu^.SimpleLowerCase <= $FFFF) then begin
          pr^ := UnicodeChar(Word(pu^.SimpleLowerCase));
        end else begin
          FromUCS4(UCS4Char(pu^.SimpleLowerCase),pr^,PUnicodeChar(PtrUInt(pr)+SizeOf(UnicodeChar))^);
          Inc(pr);
        end;
        if locIsSurrogate then begin
          Inc(pp);
          Inc(i);
        end;
      end;
      Inc(pp);
      Inc(pr);
      Inc(i);
    end;
    Dec(pp);
    i := ((PtrUInt(pr) - PtrUInt(@Result[1])) div SizeOf(UnicodeChar));
    SetLength(Result,i)
  end;
end;

class function TCharacter.ToUpper(AChar : UnicodeChar) : UnicodeChar;
begin
  Result := UnicodeChar(GetProps(Word(AChar))^.SimpleUpperCase);
  if (Result = UnicodeChar(0)) then
    Result := AChar;
end;

class function TCharacter.ToUpper(const AString : UnicodeString) : UnicodeString;
var
  i, c : SizeInt;
  pp, pr : PUnicodeChar;
  pu : PUC_Prop;
  locIsSurrogate : Boolean;
begin
  c := Length(AString);
  SetLength(Result,2*c);
  if (c > 0) then begin
    pp := @AString[1];
    pr := @Result[1];
    i := 1;
    while (i <= c) do begin
      pu := GetProps(Word(pp^));
      locIsSurrogate := (pu^.Category = TUnicodeCategory.ucSurrogate);
      if locIsSurrogate then begin
        if not IsSurrogatePair(AString,i) then
          raise EArgumentException.Create(SInvalidUnicodeCodePointSequence);
        pu := GetProps(pp^,AString[i+1]);
      end;
      if (pu^.SimpleUpperCase = 0) then begin
        pr^ := pp^;
        if locIsSurrogate then begin
          Inc(pp);
          Inc(pr);
          Inc(i);
          pr^ := pp^;
        end;
      end else begin
        if (pu^.SimpleUpperCase <= $FFFF) then begin
          pr^ := UnicodeChar(Word(pu^.SimpleUpperCase));
        end else begin
          FromUCS4(UCS4Char(pu^.SimpleUpperCase),pr^,PUnicodeChar(PtrUInt(pr)+SizeOf(UnicodeChar))^);
          Inc(pr);
        end;
        if locIsSurrogate then begin
          Inc(pp);
          Inc(i);
        end;
      end;
      Inc(pp);
      Inc(pr);
      Inc(i);
    end;
    Dec(pp);
    i := ((PtrUInt(pr) - PtrUInt(@Result[1])) div SizeOf(UnicodeChar));
    SetLength(Result,i)
  end;
end;
{$endif VER2_4}
end.
