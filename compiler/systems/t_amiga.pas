{
    Copyright (c) 2004-2006 by Free Pascal Development Team

    This unit implements support import, export, link routines
    for the Amiga targets (AmigaOS/m68k, AmigaOS/PPC)

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

 ****************************************************************************
}
unit t_amiga;

{$i fpcdefs.inc}

interface

    uses
      link;


type
  PLinkerAmiga = ^TLinkerAmiga;
  TLinkerAmiga = class(texternallinker)
    private
      function WriteResponseFile(isdll: boolean): boolean;
      procedure SetAmiga68kInfo;
      procedure SetAmigaPPCInfo;
      function MakeAmiga68kExe: boolean;
      function MakeAmigaPPCExe: boolean;
    public
      constructor Create; override;
      procedure SetDefaultInfo; override;
      function  MakeExecutable: boolean; override;
  end;


implementation

    uses
       SysUtils,
       cutils,cfileutl,cclasses,
       globtype,globals,systems,verbose,script,fmodule,i_amiga;



{****************************************************************************
                               TLinkerAmiga
****************************************************************************}

constructor TLinkerAmiga.Create;
begin
  Inherited Create;
  { allow duplicated libs (PM) }
  SharedLibFiles.doubles:=true;
  StaticLibFiles.doubles:=true;
end;

procedure TLinkerAmiga.SetAmiga68kInfo;
begin
  with Info do begin
    ExeCmd[1]:='m68k-amiga-ld $OPT -d -n -o $EXE $RES';
  end;
end;

procedure TLinkerAmiga.SetAmigaPPCInfo;
begin
  with Info do begin
    ExeCmd[1]:='ld $OPT -defsym=__amigaos4__=1 -d -q -n -o $EXE $RES';
  end;
end;

procedure TLinkerAmiga.SetDefaultInfo;
begin
  case (target_info.system) of
    system_m68k_amiga:      SetAmiga68kInfo;
    system_powerpc_amiga:   SetAmigaPPCInfo;
  end;
end;


function TLinkerAmiga.WriteResponseFile(isdll: boolean): boolean;
var
  linkres  : TLinkRes;
  i        : longint;
  HPath    : TCmdStrListItem;
  s        : string;
  linklibc : boolean;
begin
  WriteResponseFile:=False;

  { Open link.res file }
  LinkRes:=TLinkRes.Create(outputexedir+Info.ResName,true);

  { Write path to search libraries }
  HPath:=TCmdStrListItem(current_module.locallibrarysearchpath.First);
  while assigned(HPath) do
   begin
    s:=HPath.Str;
    if (cs_link_on_target in current_settings.globalswitches) then
     s:=ScriptFixFileName(s);
    LinkRes.Add('-L'+s);
    HPath:=TCmdStrListItem(HPath.Next);
   end;
  HPath:=TCmdStrListItem(LibrarySearchPath.First);
  while assigned(HPath) do
   begin
    s:=HPath.Str;
    if s<>'' then
     LinkRes.Add('SEARCH_DIR("'+Unix2AmigaPath(s)+'")');
    HPath:=TCmdStrListItem(HPath.Next);
   end;

  LinkRes.Add('INPUT (');
  { add objectfiles, start with prt0 always }
  s:=FindObjectFile('prt0','',false);
  LinkRes.AddFileName(s);
  while not ObjectFiles.Empty do
   begin
    s:=ObjectFiles.GetFirst;
    if s<>'' then
     begin
      LinkRes.AddFileName(Unix2AmigaPath(maybequoted(s)));
     end;
   end;

  { Write staticlibraries }
  if not StaticLibFiles.Empty then
   begin
    LinkRes.Add(')');
    LinkRes.Add('GROUP(');
    while not StaticLibFiles.Empty do
     begin
      S:=StaticLibFiles.GetFirst;
      LinkRes.AddFileName(Unix2AmigaPath(maybequoted(s)));
     end;
   end;

  if (cs_link_on_target in current_settings.globalswitches) then
   begin
    LinkRes.Add(')');

    { Write sharedlibraries like -l<lib>, also add the needed dynamic linker
      here to be sure that it gets linked this is needed for glibc2 systems (PFV) }
    linklibc:=false;
    while not SharedLibFiles.Empty do
     begin
      S:=SharedLibFiles.GetFirst;
      if s<>'c' then
       begin
        i:=Pos(target_info.sharedlibext,S);
        if i>0 then
         Delete(S,i,255);
        LinkRes.Add('-l'+s);
       end
      else
       begin
        LinkRes.Add('-l'+s);
        linklibc:=true;
       end;
     end;
    { be sure that libc&libgcc is the last lib }
    if linklibc then
     begin
      LinkRes.Add('-lc');
      LinkRes.Add('-lgcc');
     end;
   end
  else
   begin
    while not SharedLibFiles.Empty do
     begin
      S:=SharedLibFiles.GetFirst;
      LinkRes.Add('lib'+s+target_info.staticlibext);
     end;
    LinkRes.Add(')');
   end;

{ Write and Close response }
  linkres.writetodisk;
  linkres.free;

  WriteResponseFile:=True;
end;


function TLinkerAmiga.MakeAmiga68kExe: boolean;
var
  BinStr,
  CmdStr  : TCmdStr;
  StripStr: string[40];
begin
  StripStr:='';
  if (cs_link_strip in current_settings.globalswitches) then StripStr:='-s';

  { Call linker }
  SplitBinCmd(Info.ExeCmd[1],BinStr,CmdStr);
  Replace(cmdstr,'$OPT',Info.ExtraOptions);
  Replace(cmdstr,'$EXE',Unix2AmigaPath(maybequoted(ScriptFixFileName(current_module.exefilename))));
  Replace(cmdstr,'$RES',Unix2AmigaPath(maybequoted(ScriptFixFileName(outputexedir+Info.ResName))));
  Replace(cmdstr,'$STRIP',StripStr);
  MakeAmiga68kExe:=DoExec(FindUtil(BinStr),CmdStr,true,false);
end;


function TLinkerAmiga.MakeAmigaPPCExe: boolean;
var
  BinStr,
  CmdStr  : TCmdStr;
  StripStr: string[40];
begin
  StripStr:='';
  if (cs_link_strip in current_settings.globalswitches) then StripStr:='-s';

  { Call linker }
  SplitBinCmd(Info.ExeCmd[1],BinStr,CmdStr);
  Replace(cmdstr,'$OPT',Info.ExtraOptions);
  Replace(cmdstr,'$EXE',Unix2AmigaPath(maybequoted(ScriptFixFileName(current_module.exefilename))));
  Replace(cmdstr,'$RES',Unix2AmigaPath(maybequoted(ScriptFixFileName(outputexedir+Info.ResName))));
  Replace(cmdstr,'$STRIP',StripStr);
  MakeAmigaPPCExe:=DoExec(FindUtil(BinStr),CmdStr,true,false);
end;


function TLinkerAmiga.MakeExecutable:boolean;
var
  success : boolean;
begin
  if not(cs_link_nolink in current_settings.globalswitches) then
    Message1(exec_i_linking,current_module.exefilename);

  { Write used files and libraries }
  WriteResponseFile(false);

  case (target_info.system) of
    system_m68k_amiga:      success:=MakeAmiga68kExe;
    system_powerpc_amiga:   success:=MakeAmigaPPCExe;
  end;

  { Remove ReponseFile }
  if (success) and not(cs_link_nolink in current_settings.globalswitches) then
    DeleteFile(outputexedir+Info.ResName);

  MakeExecutable:=success;   { otherwise a recursive call to link method }
end;


{*****************************************************************************
                                     Initialize
*****************************************************************************}

initialization
{$ifdef m68k}
{ TODO: No executable creation support for m68k yet!}
  RegisterExternalLinker(system_m68k_Amiga_info,TLinkerAmiga);
  RegisterTarget(system_m68k_Amiga_info);
{$endif m68k}
{$ifdef powerpc}
  RegisterExternalLinker(system_powerpc_Amiga_info,TLinkerAmiga);
  RegisterTarget(system_powerpc_Amiga_info);
{$endif powerpc}
end.
