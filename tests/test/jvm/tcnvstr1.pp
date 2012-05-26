program tcnvstr1;

{****************************************************************}
{  CODE GENERATOR TEST PROGRAM                                   }
{  Copyright (c) 2002, Carl Eric Codere                          }
{****************************************************************}
{ NODE TESTED : secondtypeconvert() -> second_string_string      }
{****************************************************************}
{ PRE-REQUISITES: secondload()                                   }
{                 secondassign()                                 }
{                 secondtypeconv()                               }
{****************************************************************}
{ DEFINES:                                                       }
{            FPC     = Target is FreePascal compiler             }
{****************************************************************}
{ REMARKS: Same type short conversion is not tested, except for  }
{          shortstrings , since it requires special handling.    }
{                                                                }
{                                                                }
{****************************************************************}

{$ifdef fpc}
{$mode objfpc}
  {$ifndef ver1_0}
    {$define haswidestring}
  {$endif}
{$else}
  {$ifndef ver70}
    {$define haswidestring}
  {$endif}
{$endif}

{$define hasshortstring}

uses
  {$ifdef java}jdk15{$else}androidr14{$endif};
{$H+}

{$macro on}
{$define writeln:=JLSystem.fout.println}
{$define write:=JLSystem.fout.print}

const
  { exactly 255 characters in length }
  BIG_STRING =
' This is a small text documentation to verify the validity of'+
' the string conversion routines. Of course the conversion routines'+
' should normally work like a charm, and this can only test that there'+
' aren''t any problems with maximum length strings. This fix!';
  { < 255 characters in length }
  SMALL_STRING = 'This is a small hello!';
  { > 255 characters in length }
  HUGE_STRING_END = ' the goal of this experiment';
  HUGE_STRING =
' This is a huge text documentation to verify the validity of'+
' the string conversion routines. Of course the conversion routines'+
' should normally work like a charm, and this can only test that there'+
' aren''t any problems with maximum length strings. I hope you understand'+
HUGE_STRING_END;
  EMPTY_STRING = '';

type
  shortstr = string[127];
var
{$ifdef hasshortstring}
 s2: shortstr;
{$endif}
 str_ansi: ansistring;
{$ifdef hasshortstring}
 str_short: shortstring;
{$endif}
{$ifdef haswidestring}
 str_wide : widestring;
{$endif}


procedure fail;
 begin
   Raise JLException.create('failure');
 end;

{$ifdef hasshortstring}
procedure test_ansi_to_short;
var
  p: pchar;
begin
 {************************************************************************}
 {                          ansistring -> shortstring                     }
 {************************************************************************}
 WriteLn('Test ansistring -> shortstring');
 { ansistring -> shortstring }
 str_short := '';
 str_ansi:='';
 str_ansi := SMALL_STRING;
 str_short:=str_ansi;
 Write('small ansistring -> shortstring...');
 if str_short = str_ansi then
   WriteLn('Success.')
 else
   fail;

 str_short := '';
 str_ansi:='';
 str_ansi := EMPTY_STRING;
 str_short:=str_ansi;
 Write('empty ansistring -> shortstring...');
 if str_short = str_ansi then
   WriteLn('Success.')
 else
   fail;


 str_short := '';
 str_ansi:='';
 str_ansi := BIG_STRING;
 str_short:=str_ansi;
 Write('big ansistring -> shortstring...');
 jlsystem.fout.println;
 jlsystem.fout.println('const: '+BIG_STRING);
 jlsystem.fout.println('ansi : '+unicodestring(str_ansi));
 jlsystem.fout.println('short: '+unicodestring(str_short));
 if str_short = str_ansi then
   WriteLn('Success.')
 else
   fail;


 Write('huge ansistring -> shortstring...');
 str_short := '';
 str_ansi:='';
 str_ansi := HUGE_STRING;
 str_short:=str_ansi;
 { Delphi 3/Delphi 6 does not consider these as the same string }
 if str_short <> str_ansi then
   WriteLn('Success.')
 else
   fail;
{}
 s2 := '';
 str_ansi:='';
 str_ansi := SMALL_STRING;
 s2:=str_ansi;
 Write('small ansistring -> shortstring...');
 if s2 = str_ansi then
   WriteLn('Success.')
 else
   fail;

 s2 := '';
 str_ansi:='';
 str_ansi := EMPTY_STRING;
 s2:=str_ansi;
 Write('empty ansistring -> shortstring...');
 if s2 = str_ansi then
   WriteLn('Success.')
 else
   fail;

  str_ansi:='';
  p:=pchar(str_ansi);
  Write('empty ansistring -> pchar...');
  if p^<>#0 then
    fail;
  if p[0]<>#0 then
    fail
  else
    Writeln('Success');

  p:='';
  Write('empty string const -> pchar...');
  if p^<>#0 then
    fail;
  if p[0]<>#0 then
    fail
  else
    Writeln('Success');

  p:=ansistring('');
  Write('empty ansistring const -> pchar...');
  if p^<>#0 then
    fail;
  if p[0]<>#0 then
    fail
  else
    Writeln('Success');

  p:=widestring('');
  Write('empty widestring const -> pchar...');
  if p^<>#0 then
    fail;
  if p[0]<>#0 then
    fail
  else
    Writeln('Success');

 p:=BIG_STRING;
 str_ansi:=BIG_STRING;
 Write('big ansistring -> pchar...');
 if p = str_ansi then
   WriteLn('Success.')
 else
   fail;

 s2 := '';
 str_ansi:='';
 str_ansi := BIG_STRING;
 s2:=str_ansi;
 Write('big ansistring -> shortstring...');
 { Should fail, since comparing different string lengths }
 if s2 <> str_ansi then
   WriteLn('Success.')
 else
   fail;


 str_ansi := BIG_STRING;
 Write('big ansistring -> pchar...');
 p:=pchar(str_ansi);
 if p^<>' ' then
   fail;
 if p[0]<>' ' then
   fail;
 if length(p)<>length(BIG_STRING) then
   fail
 else
   Writeln('Success');


 s2 := '';
 str_ansi:='';
 str_ansi := HUGE_STRING;
 s2:=str_ansi;
 Write('huge ansistring -> shortstring...');
 { Should fail, since comparing different string lengths }
 if s2 <> str_ansi then
   WriteLn('Success.')
 else
   fail;
end;


procedure test_short_to_short;
begin
 {************************************************************************}
 {                         shortstring -> shortstring                     }
 {************************************************************************}
 WriteLn('Test shortstring -> shortstring...');
 { shortstring -> shortstring }
 str_short := '';
 s2:='';
 s2 := SMALL_STRING;
 str_short:=s2;
 Write('small shortstring -> shortstring...');
 if str_short = s2 then
   WriteLn('Success.')
 else
   fail;

 str_short := '';
 s2:='';
 s2 := EMPTY_STRING;
 str_short:=s2;
 Write('empty shortstring -> shortstring...');
 if str_short = s2 then
   WriteLn('Success.')
 else
   fail;

{$ifdef fpc}
{ Delphi does not compile these }
 str_short := '';
 s2:='';
 s2 := BIG_STRING;
 str_short:=s2;
 Write('big shortstring -> shortstring...');
 if str_short = s2 then
   WriteLn('Success.')
 else
   fail;


 str_short := '';
 s2:='';
 s2 := HUGE_STRING;
 str_short:=s2;
 Write('huge shortstring -> shortstring...');
 { Delphi 3/Delphi 6 does not consider these as the same string }
 if str_short = s2 then
   WriteLn('Success.')
 else
   fail;
{$endif}

 s2 := '';
 str_short:='';
 str_short := SMALL_STRING;
 Write('small shortstring -> shortstring...');
 s2:=str_short;
 if s2 = str_short then
   WriteLn('Success.')
 else
   fail;

 s2 := '';
 str_short:='';
 str_short := EMPTY_STRING;
 Write('empty shortstring -> shortstring...');
 s2:=str_short;
 if s2 = str_short then
   WriteLn('Success.')
 else
   fail;

 s2 := '';
 str_short:='';
 str_short := BIG_STRING;
 Write('big shortstring -> shortstring...');
 s2:=str_short;
 { Should fail, since comparing different string lengths }
 if s2 <> str_short then
   WriteLn('Success.')
 else
   fail;

{$ifdef fpc}
 s2 := '';
 str_short:='';
 writeln(length(ShortstringClass(@str_short).fdata));
 writeln(length(str_short));
 str_short := HUGE_STRING;
 writeln(length(ShortstringClass(@str_short).fdata));
 writeln(length(str_short));
 Write('huge shortstring -> shortstring...');
 s2:=str_short;
 writeln(unicodestring(s2));
 writeln(unicodestring(str_short));
 { Should fail, since comparing different string lengths }
 if s2 <> str_short then
   WriteLn('Success.')
 else
   fail;
{$endif}
end;


procedure test_short_to_ansi;
begin
 {************************************************************************}
 {                         shortstring -> ansistring                      }
 {************************************************************************}
 WriteLn('Test shortstring -> ansistring');
 Write('small shortstring -> ansistring...');
 { shortstring -> ansistring }
 str_short := SMALL_STRING;
 str_ansi:=str_short;
 if str_short = str_ansi then
   WriteLn('Success.')
 else
   fail;

 Write('empty shortstring -> ansistring...');
 str_short := EMPTY_STRING;
 str_ansi:=str_short;
 if str_short = str_ansi then
   WriteLn('Success.')
 else
   fail;

 Write('big shortstring -> ansistring...');
 str_short := BIG_STRING;
 str_ansi:=str_short;
 if str_short = str_ansi then
   WriteLn('Success.')
 else
   fail;

 Write('small shortstring -> ansistring...');
 { shortstring -> ansistring }
 s2 := SMALL_STRING;
 str_ansi:=s2;
 if s2 = str_ansi then
   WriteLn('Success.')
 else
   fail;

 Write('empty shortstring -> ansistring...');
 s2 := EMPTY_STRING;
 str_ansi:=s2;
 if s2 = str_ansi then
   WriteLn('Success.')
 else
   fail;

end;
{$endif}

{$ifdef haswidestring}
procedure test_wide_to_ansi;
begin
 {************************************************************************}
 {                         widestring -> ansistring                      }
 {************************************************************************}
 WriteLn('Test widestring -> ansistring');
 Write('small widestring -> ansistring...');
 { widestring -> ansistring }
 str_wide := SMALL_STRING;
 str_ansi:=str_wide;
 if str_wide = str_ansi then
   WriteLn('Success.')
 else
   fail;

 Write('empty widestring -> ansistring...');
 str_wide := EMPTY_STRING;
 str_ansi:=str_wide;
 if str_wide = str_ansi then
   WriteLn('Success.')
 else
   fail;

 Write('big widestring -> ansistring...');
 str_wide := BIG_STRING;
 str_ansi:=str_wide;
 if str_wide = str_ansi then
   WriteLn('Success.')
 else
   fail;

 Write('huge widestring -> ansistring...');
 str_wide := HUGE_STRING;
 str_ansi:=str_wide;
 if str_wide = str_ansi then
   WriteLn('Success.')
 else
   fail;

end;


{$ifdef hasshortstring}
procedure test_short_to_wide;
begin
 {************************************************************************}
 {                         shortstring -> widestring                      }
 {************************************************************************}
 WriteLn('Test shortstring -> widestring');
 Write('small shortstring -> widestring...');
 { shortstring -> widestring }
 str_short := SMALL_STRING;
 str_wide:=str_short;
 if str_short = str_wide then
   WriteLn('Success.')
 else
   fail;

 Write('empty shortstring -> widestring...');
 str_short := EMPTY_STRING;
 str_wide:=str_short;
 if str_short = str_wide then
   WriteLn('Success.')
 else
   fail;

 Write('big shortstring -> widestring...');
 str_short := BIG_STRING;
 str_wide:=str_short;
 if str_short = str_wide then
   WriteLn('Success.')
 else
   fail;

{$ifdef hasshortstring}
 Write('small shortstring -> widestring...');
 { shortstring -> widestring }
 s2 := SMALL_STRING;
 str_wide:=s2;
 if s2 = str_wide then
   WriteLn('Success.')
 else
   fail;

 Write('empty shortstring -> widestring...');
 s2 := EMPTY_STRING;
 str_wide:=s2;
 if s2 = str_wide then
   WriteLn('Success.')
 else
   fail;
{$endif}
end;
{$endif}

procedure test_ansi_to_wide;
begin
 {************************************************************************}
 {                         ansistring -> widestring                      }
 {************************************************************************}
 WriteLn('Test ansistring -> widestring');
 Write('small ansistring -> widestring...');
 { ansistring -> widestring }
 str_ansi := SMALL_STRING;
 str_wide:=str_ansi;
 if str_ansi = str_wide then
   WriteLn('Success.')
 else
   fail;

 Write('empty ansistring -> widestring...');
 str_ansi := EMPTY_STRING;
 str_wide:=str_ansi;
 if str_ansi = str_wide then
   WriteLn('Success.')
 else
   fail;

 Write('big ansistring -> widestring...');
 str_ansi := BIG_STRING;
 str_wide:=str_ansi;
 if str_ansi = str_wide then
   WriteLn('Success.')
 else
   fail;

{$ifdef hasshortstring}
 Write('small ansistring -> widestring...');
 { ansistring -> widestring }
 s2 := SMALL_STRING;
 str_wide:=s2;
 if s2 = str_wide then
   WriteLn('Success.')
 else
   fail;

 Write('empty ansistring -> widestring...');
 s2 := EMPTY_STRING;
 str_wide:=s2;
 if s2 = str_wide then
   WriteLn('Success.')
 else
   fail;
{$endif hasshortstring}

end;


{$ifdef hasshortstring}
procedure test_wide_to_short;
begin
 {************************************************************************}
 {                          widestring -> shortstring                     }
 {************************************************************************}
 WriteLn('Test widestring -> shortstring');
 { widestring -> shortstring }
 str_short := '';
 str_wide:='';
 str_wide := SMALL_STRING;
 Write('small widestring -> shortstring...');
 str_short:=str_wide;
 if str_short = str_wide then
   WriteLn('Success.')
 else
   fail;

 str_short := '';
 str_wide:='';
 str_wide := EMPTY_STRING;
 Write('empty widestring -> shortstring...');
 str_short:=str_wide;
 if str_short = str_wide then
   WriteLn('Success.')
 else
   fail;


 Write('big widestring -> shortstring...');
 str_short := '';
 str_wide:='';
 str_wide := BIG_STRING;
 str_short:=str_wide;
 if str_short = str_wide then
   WriteLn('Success.')
 else
   fail;

 Write('huge widestring -> shortstring...');
 str_wide := HUGE_STRING;
 str_short:=str_wide;
 if str_short <> str_wide then
   WriteLn('Success.')
 else
   fail;

{}
 Write('small widestring -> shortstring...');
 s2 := '';
 str_wide:='';
 str_wide := SMALL_STRING;
 s2:=str_wide;
 if s2 = str_wide then
   WriteLn('Success.')
 else
   fail;

 Write('empty widestring -> shortstring...');
 s2 := '';
 str_wide:='';
 str_wide := EMPTY_STRING;
 s2:=str_wide;
 if s2 = str_wide then
   WriteLn('Success.')
 else
   fail;

 Write('big widestring -> shortstring...');
 s2 := '';
 str_wide:='';
 str_wide := BIG_STRING;
 s2:=str_wide;
 if s2 <> str_wide then
   WriteLn('Success.')
 else
   fail;

 Write('huge widestring -> shortstring...');
 s2 := '';
 str_wide:='';
 str_wide := HUGE_STRING;
 s2:=str_wide;
 if s2 <> str_wide then
   WriteLn('Success.')
 else
   fail;
end;
{$endif}
{$endif}

Begin
{$ifdef hasshortstring}
 test_ansi_to_short;
 test_short_to_short;
 test_short_to_ansi;
{$endif}
 { requires widestring support }
{$ifdef haswidestring}
{$ifdef hasshortstring}
 test_short_to_wide;
{$endif}
 test_ansi_to_wide;
{$ifdef hasshortstring}
 test_wide_to_short;
{$endif}
 test_wide_to_ansi;
{$endif}
End.
