{ %version=1.1}
{$codepage cp850}
begin
   if ord(widechar('�'))<>196 then
     halt(1);
   halt(0);
end.
