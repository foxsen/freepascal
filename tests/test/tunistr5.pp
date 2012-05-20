﻿{$codepage utf-8}

var
  ws: unicodestring;
  us: UCS4String;
begin
// the compiler does not yet support characters which require
// a surrogate pair in utf-16
//  ws:='éłŁćçŹ你';
//  so write the last character directly using a utf-16 surrogate pair
  ws:='éłŁćçŹ'#$d87e#$dc04;

  if (length(ws)<>8) or
     (ws[1]<>'é') or
     (ws[2]<>'ł') or
     (ws[3]<>'Ł') or
     (ws[4]<>'ć') or
     (ws[5]<>'ç') or
     (ws[6]<>'Ź') or
     (ws[7]<>#$d87e) or
     (ws[8]<>#$dc04) then
    halt(1);
  us:=UnicodeStringToUCS4String(ws);
  if (length(us)<>8) or
     (us[0]<>UCS4Char(unicodechar('é'))) or
     (us[1]<>UCS4Char(unicodechar('ł'))) or
     (us[2]<>UCS4Char(unicodechar('Ł'))) or
     (us[3]<>UCS4Char(unicodechar('ć'))) or
     (us[4]<>UCS4Char(unicodechar('ç'))) or
     (us[5]<>UCS4Char(unicodechar('Ź'))) or
     (us[6]<>UCS4Char($2F804)) or
     (us[7]<>UCS4Char(0)) then
    halt(2);
  ws:=UCS4StringToUnicodeString(us);
  if (length(ws)<>8) or
     (ws[1]<>'é') or
     (ws[2]<>'ł') or
     (ws[3]<>'Ł') or
     (ws[4]<>'ć') or
     (ws[5]<>'ç') or
     (ws[6]<>'Ź') or
     (ws[7]<>#$d87e) or
     (ws[8]<>#$dc04) then
    halt(3);
end.
