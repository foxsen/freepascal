{ %target=win32 }
{ %OPT=-Cr- }

uses
  windows;

var
  WindowHandle : HWND;

begin
  WindowHandle:=0;
  // the next code must compile but with a range check warning
  SetWindowLong(WindowHandle, GWL_STYLE, WS_POPUP or WS_CLIPCHILDREN);
  halt(0);
end.
