{
    Copyright (c) 1998-2008 by Peter Vreman

    This unit implements support import,export,link routines
    for the (i386) solaris target

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
unit t_sunos;

{$i fpcdefs.inc}

interface

{ copy from t_linux
// Up to now we use gld since the solaris ld seems not support .res-files}
{-$DEFINE LinkTest} { DON't del link.res and write Info }
{$DEFINE GnuLd}{The other is not implemented }

implementation

  uses
    sysutils,
    cutils,cfileutl,cclasses,
    verbose,systems,globtype,globals,
    symconst,script,
    fmodule,aasmbase,aasmtai,aasmdata,aasmcpu,cpubase,symsym,symdef,
    cgobj,
    import,export,expunix,link,comprsrc,rescmn,i_sunos,ogbase;

  type
    timportlibsolaris=class(timportlib)
      procedure generatelib;override;
    end;

    texportlibsolaris=class(texportlibunix)
(*
      procedure setinitname(list: TAsmList; const s: string); override;
      procedure setfininame(list: TAsmList; const s: string); override;
*)
    end;

    tlinkersolaris=class(texternallinker)
    private
      Glibc2,
      Glibc21 : boolean;
      use_gnu_ld : boolean;
      linkres : TLinkRes;
      Function  WriteResponseFile(isdll:boolean) : Boolean;
    public
      constructor Create;override;
      procedure SetDefaultInfo;override;
      function  MakeExecutable:boolean;override;
      function  MakeSharedLibrary:boolean;override;
    end;


{*****************************************************************************
                               TIMPORTLIBsolaris
*****************************************************************************}

    procedure timportlibsolaris.generatelib;
      var
        i : longint;
        ImportLibrary : TImportLibrary;
      begin
        for i:=0 to current_module.ImportLibraryList.Count-1 do
          begin
            ImportLibrary:=TImportLibrary(current_module.ImportLibraryList[i]);
            current_module.linkothersharedlibs.add(ImportLibrary.Name,link_always);
          end;
      end;


{*****************************************************************************
                               TEXPORTLIBsolaris
*****************************************************************************}
(*
    procedure texportlibsolaris.setinitname(list: TAsmList; const s: string);
      begin
        inherited setinitname(list,s);
{$ifdef sparc}
        new_section(list,sec_init,'',4);
        list.concat(tai_symbol.createname_global('_init',AT_FUNCTION,0));
        list.concat(taicpu.op_reg_const_reg(A_SAVE,NR_STACK_POINTER_REG,-96,NR_STACK_POINTER_REG));
{$endif sparc}
      end;


    procedure texportlibsolaris.setfininame(list: TAsmList; const s: string);
      begin
        inherited setfininame(list,s);
{$ifdef sparc}
        new_section(list,sec_fini,'',4);
        list.concat(tai_symbol.createname_global('_fini',AT_FUNCTION,0));
        list.concat(taicpu.op_reg_const_reg(A_SAVE,NR_STACK_POINTER_REG,-96,NR_STACK_POINTER_REG));
{$endif sparc}
      end;
*)
{*****************************************************************************
                                  TLINKERsolaris
*****************************************************************************}

Constructor TLinkersolaris.Create;
begin
  Inherited Create;

  if cs_link_native in init_settings.globalswitches then
    use_gnu_ld:=false
  else
    use_gnu_ld:=true;
  if NOT Dontlinkstdlibpath Then
{$ifdef x86_64}
   LibrarySearchPath.AddPath(sysrootpath,'/lib/64;/usr/lib/64;/usr/X11R6/lib/64;/opt/sfw/lib/64',true);
{$else not x86_64}
   LibrarySearchPath.AddPath(sysrootpath,'/lib;/usr/lib;/usr/X11R6/lib;/opt/sfw/lib',true);
{$endif not x86_64}
{$ifdef  LinkTest}
     if (cs_link_staticflag in current_settings.globalswitches) then  WriteLN('ForceLinkStaticFlag');
     if (cs_link_static in current_settings.globalswitches) then  WriteLN('LinkStatic-Flag');
     if (cs_link_shared in current_settings.globalswitches) then  WriteLN('LinkSynamicFlag');
{$EndIf}
end;


procedure TLinkersolaris.SetDefaultInfo;
{
  This will also detect which libc version will be used
}
{$ifdef x86_64}
const
  gld = 'gld -m elf_x86_64 ';
  solaris_ld = '/usr/bin/ld -64 ';
{$endif}
{$ifdef i386}
const
  gld = 'gld ';
  solaris_ld = '/usr/bin/ld ';
{$endif }
{$ifdef sparc}
const
  gld = 'gld ';
  solaris_ld = 'ld ';
{$endif}
begin
  Glibc2:=false;
  Glibc21:=false;
  with Info do
   begin
{$IFDEF GnuLd}
     ExeCmd[1]:=gld + '$OPT $DYNLINK $STATIC $STRIP -L. -o $EXE $RES';
     ExeCmd[2]:=solaris_ld + '$OPT $DYNLINK $STATIC $STRIP -L . -o $EXE $RESDATA';
     DllCmd[1]:=gld + '$OPT $INITFINI -shared -L. -o $EXE $RES';
     DllCmd[2]:='gstrip --strip-unneeded $EXE';
     DllCmd[3]:=solaris_ld + '$OPT $INITFINI -M $VERSIONFILE -G -Bdynamic -L. -o $EXE $RESDATA';
     DynamicLinker:=''; { Gnu uses the default }
     Glibc21:=false;
{$ELSE}
    Not Implememted
{$ENDIF}
   end;

end;


Function TLinkersolaris.WriteResponseFile(isdll:boolean) : Boolean;
Var
  i            : longint;
{  cprtobj,
  gprtobj,
  prtobj       : string[80];}
  HPath        : TCmdStrListItem;
  s,s2         : TCmdStr;
  linkdynamic,
  linklibc     : boolean;
  LinkRes2 : TLinkRes;
begin
  WriteResponseFile:=False;
{ set special options for some targets }
  linkdynamic:=not(SharedLibFiles.empty);
{  linkdynamic:=false; // da nicht getestet }
  linklibc:=(SharedLibFiles.Find('c')<>nil);
{  prtobj:='prt0';
  cprtobj:='cprt0';
  gprtobj:='gprt0';}
  if cs_profile in current_settings.moduleswitches then
   begin
{     prtobj:=gprtobj;}
     if not glibc2 then
      AddSharedLibrary('gmon');
     AddSharedLibrary('c');
     linklibc:=true;
   end
  else
   begin
     if linklibc then
      begin
{       prtobj:=cprtobj;}
      end
      else
       AddSharedLibrary('c'); { quick hack: this solaris implementation needs alwys libc }
   end;

  if use_gnu_ld then
    begin
  { Open link.res file }
  LinkRes:=TLinkRes.Create(outputexedir+Info.ResName,true);

  { Write path to search libraries }
  HPath:=TCmdStrListItem(current_module.locallibrarysearchpath.First);
  while assigned(HPath) do
   begin
     LinkRes.Add('SEARCH_DIR("'+HPath.Str+'")');
     HPath:=TCmdStrListItem(HPath.Next);
   end;
  HPath:=TCmdStrListItem(LibrarySearchPath.First);
  while assigned(HPath) do
   begin
     LinkRes.Add('SEARCH_DIR("'+HPath.Str+'")');
     HPath:=TCmdStrListItem(HPath.Next);
   end;

  { force local symbol resolution (i.e., inside the shared }
  { library itself) for all non-exorted symbols, otherwise }
  { several RTL symbols of FPC-compiled shared libraries   }
  { will be bound to those of a single shared library or   }
  { to the main program                                    }
  if (isdll) then
    begin
      LinkRes.add('VERSION');
      LinkRes.add('{');
      LinkRes.add('  {');
      if not texportlibunix(exportlib).exportedsymnames.empty then
        begin
          LinkRes.add('    global:');
          repeat
            LinkRes.add('      '+texportlibunix(exportlib).exportedsymnames.getfirst+';');
          until texportlibunix(exportlib).exportedsymnames.empty;
        end;
      LinkRes.add('    local:');
      LinkRes.add('      *;');
      LinkRes.add('  };');
      LinkRes.add('}');
    end;

  LinkRes.Add('INPUT(');
  { add objectfiles, start with prt0 always }
  { solaris port contains _start inside the system unit, it
    needs only one entry because it is linked always against libc
  if prtobj<>'' then
   LinkRes.AddFileName(FindObjectFile(prtobj,'',false));
  }
  { try to add crti and crtbegin if linking to C }
  if linklibc then { Needed in solaris? }
   begin
{     if librarysearchpath.FindFile('crtbegin.o',s) then
      LinkRes.AddFileName(s);}
     if librarysearchpath.FindFile('crti.o',false,s) then
      LinkRes.AddFileName(s);
   end;
  { main objectfiles }
  while not ObjectFiles.Empty do
   begin
     s:=ObjectFiles.GetFirst;
     if s<>'' then
      LinkRes.AddFileName(maybequoted(s));
   end;
  LinkRes.Add(')');

  { Write staticlibraries }
  if not StaticLibFiles.Empty then
   begin
     LinkRes.Add('GROUP(');
     While not StaticLibFiles.Empty do
      begin
        S:=StaticLibFiles.GetFirst;
        LinkRes.AddFileName(maybequoted(s))
      end;
     LinkRes.Add(')');
   end;

  { Write sharedlibraries like -l<lib>, also add the needed dynamic linker
    here to be sure that it gets linked this is needed for glibc2 systems (PFV) }
  if not SharedLibFiles.Empty then
   begin
     LinkRes.Add('INPUT(');
     While not SharedLibFiles.Empty do
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
           linklibc:=true;
           linkdynamic:=false; { libc will include the ld-solaris (war ld-linux) for us }
         end;
      end;
     { be sure that libc is the last lib }
     if linklibc then
      LinkRes.Add('-lc');
     { when we have -static for the linker the we also need libgcc }
     if (cs_link_staticflag in current_settings.globalswitches) then begin
      LinkRes.Add('-lgcc');
     end;
     if linkdynamic and (Info.DynamicLinker<>'') then { gld has a default, DynamicLinker is not set in solaris }
       LinkRes.AddFileName(Info.DynamicLinker);
     LinkRes.Add(')');
   end;
  { objects which must be at the end }
  if linklibc then {needed in solaris ? }
   begin
     if {librarysearchpath.FindFile('crtend.o',s1) or}
        librarysearchpath.FindFile('crtn.o',false,s2) then
      begin
        LinkRes.Add('INPUT(');
{        LinkRes.AddFileName(s1);}
        LinkRes.AddFileName(s2);
        LinkRes.Add(')');
      end;
   end;
{ Write and Close response }
  linkres.writetodisk;
  LinkRes.Free;
    end
  else { not use_gnu_ld }
    begin
   { Open TlinkRes, will not be written to disk }
  LinkRes:=TLinkRes.Create(outputexedir+Info.ResName+'2',false);

 { Write path to search libraries }
  HPath:=TCmdStrListItem(current_module.locallibrarysearchpath.First);
  while assigned(HPath) do
   begin
     LinkRes.Add('-L '+maybequoted(HPath.Str));
     HPath:=TCmdStrListItem(HPath.Next);
   end;
  HPath:=TCmdStrListItem(LibrarySearchPath.First);
  while assigned(HPath) do
   begin
     LinkRes.Add('-L '+maybequoted(HPath.Str));
     HPath:=TCmdStrListItem(HPath.Next);
   end;
  { force local symbol resolution (i.e., inside the shared }
  { library itself) for all non-exorted symbols, otherwise }
  { several RTL symbols of FPC-compiled shared libraries   }
  { will be bound to those of a single shared library or   }
  { to the main program                                    }
  if (isdll) then
    begin
      LinkRes2:=TLinkRes.Create(outputexedir+Info.ResName,true);
      // LinkRes2.add('VERSION'); not needed for now
      LinkRes2.add('  {');
      if not texportlibunix(exportlib).exportedsymnames.empty then
        begin
          LinkRes2.add('    global:');
          repeat
            LinkRes2.add('      '+texportlibunix(exportlib).exportedsymnames.getfirst+';');
          until texportlibunix(exportlib).exportedsymnames.empty;
        end;
      LinkRes2.add('    local:');
      LinkRes2.add('      *;');
      LinkRes2.add('  };');
      LinkRes2.writetodisk;
      LinkRes2.Free;
    end;


  { add objectfiles, start with prt0 always }
  { solaris port contains _start inside the system unit, it
    needs only one entry because it is linked always against libc
  if prtobj<>'' then
   LinkRes.AddFileName(FindObjectFile(prtobj,'',false));
  }
  { try to add crti and crtbegin if linking to C }
  if linklibc then { Needed in solaris? }
   begin
{     if librarysearchpath.FindFile('crtbegin.o',s) then
      LinkRes.AddFileName(s);}
     if librarysearchpath.FindFile('crti.o',false,s) then
      LinkRes.AddFileName(s);
   end;
  { main objectfiles }
  while not ObjectFiles.Empty do
   begin
     s:=ObjectFiles.GetFirst;
     if s<>'' then
      LinkRes.AddFileName(maybequoted(s));
   end;

  { Write staticlibraries }
  if not StaticLibFiles.Empty then
   begin
     linkres.add('-('); 
     While not StaticLibFiles.Empty do
      begin
        S:=StaticLibFiles.GetFirst;
        LinkRes.AddFileName(maybequoted(s))
      end;
     linkres.add('-)'); 
   end;

  { Write sharedlibraries like -l<lib>, also add the needed dynamic linker
    here to be sure that it gets linked this is needed for glibc2 systems (PFV) }
  if not SharedLibFiles.Empty then
   begin
     While not SharedLibFiles.Empty do
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
           linklibc:=true;
           linkdynamic:=false; { libc will include the ld-solaris (war ld-linux) for us }
         end;
      end;
     { be sure that libc is the last lib }
     if linklibc then
      LinkRes.Add('-lc');
     { when we have -static for the linker the we also need libgcc }
     if (cs_link_staticflag in current_settings.globalswitches) then begin
      LinkRes.Add('-lgcc');
     end;
     if linkdynamic and (Info.DynamicLinker<>'') then { gld has a default, DynamicLinker is not set in solaris }
       LinkRes.AddFileName(Info.DynamicLinker);
   end;
  { objects which must be at the end }
  if linklibc then {needed in solaris ? }
   begin
     if {librarysearchpath.FindFile('crtend.o',s1) or}
        librarysearchpath.FindFile('crtn.o',false,s2) then
      begin
{        LinkRes.AddFileName(s1);}
        LinkRes.AddFileName(s2);
      end;
   end;
{ Write and Close response }
  //linkres.writetodisk;
  //LinkRes.Free;

    end;
  WriteResponseFile:=True;
end;


function TLinkersolaris.MakeExecutable:boolean;
var
  binstr,
  s, linkstr,
  cmdstr  : TCmdStr;
  success : boolean;
  DynLinkStr : string[60];
  StaticStr,
  StripStr   : string[40];
begin
  if not(cs_link_nolink in current_settings.globalswitches) then
   Message1(exec_i_linking,current_module.exefilename);

{ Create some replacements }
  StaticStr:='';
  StripStr:='';
  DynLinkStr:='';
  if (cs_link_staticflag in current_settings.globalswitches) then
    StaticStr:='-Bstatic';
  if (cs_link_strip in current_settings.globalswitches) then
   StripStr:='-s';
  If (cs_profile in current_settings.moduleswitches) or
     ((Info.DynamicLinker<>'') and (not SharedLibFiles.Empty)) then
   DynLinkStr:='-dynamic-linker='+Info.DynamicLinker;
  if rlinkpath<>'' then
    if use_gnu_ld then
      DynLinkStr:=DynLinkStr+' --rpath-link '+rlinkpath
    else
      DynLinkStr:=DynLinkStr+' -R '+rlinkpath;

  { solaris sets DynamicLinker, but gld will (hopefully) defaults to -Bdynamic and add the default-linker }
{ Write used files and libraries }
  WriteResponseFile(false);

{ Call linker }
  if use_gnu_ld then
    SplitBinCmd(Info.ExeCmd[1],binstr,cmdstr)
  else
    SplitBinCmd(Info.ExeCmd[2],binstr,cmdstr);
  Replace(cmdstr,'$EXE',maybequoted(current_module.exefilename));
  Replace(cmdstr,'$OPT',Info.ExtraOptions);
  if use_gnu_ld then
    Replace(cmdstr,'$RES',maybequoted(outputexedir+Info.ResName))
  else
    begin
      linkstr:='';
      while not linkres.data.Empty do
        begin
          s:=linkres.data.GetFirst;
	  if s<>'' then
            linkstr:=linkstr+' '+s;
        end;
      linkres.free;
      Replace(cmdstr,'$RESDATA',linkstr);
    end;
  Replace(cmdstr,'$STATIC',StaticStr);
  Replace(cmdstr,'$STRIP',StripStr);
  Replace(cmdstr,'$DYNLINK',DynLinkStr);
  if BinStr[1]<>'/' then
    success:=DoExec(FindUtil(utilsprefix+BinStr),CmdStr,true,false)
  else { Using utilsprefix has no sense on /usr/bin/ld }
    success:=DoExec(BinStr,Trim(CmdStr),true,false);

{ Remove ReponseFile }
{$IFNDEF LinkTest}
  if (success) and use_gnu_ld and
     not(cs_link_nolink in current_settings.globalswitches) then
   DeleteFile(outputexedir+Info.ResName);
{$ENDIF}
  MakeExecutable:=success;   { otherwise a recursive call to link method }
end;


Function TLinkersolaris.MakeSharedLibrary:boolean;
var
  InitFiniStr : string;
  binstr,
  s, linkstr,
  cmdstr  : TCmdStr;
  success : boolean;
begin
  MakeSharedLibrary:=false;
  if not(cs_link_nolink in current_settings.globalswitches) then
   Message1(exec_i_linking,current_module.sharedlibfilename);

{ Write used files and libraries }
  WriteResponseFile(true);

{ Create some replacements }
{ initname and fininame may contain $, which can be wrongly interpreted
  in a link script, thus we surround them with single quotes 
  in cs_link_nolink is in globalswitches }
  if use_gnu_ld then
    begin
      InitFiniStr:='-init ';
      if cs_link_nolink in current_settings.globalswitches then
        InitFiniStr:=InitFiniStr+''''+exportlib.initname+''''
      else
        InitFiniStr:=InitFiniStr+exportlib.initname;
      if (exportlib.fininame<>'') then
        begin
          if cs_link_nolink in current_settings.globalswitches then
            InitFiniStr:=InitFiniStr+' -fini '''+exportlib.initname+''''
          else
            InitFiniStr:=InitFiniStr+' -fini '+exportlib.fininame;
        end;
    end
  else
    begin
      InitFiniStr:='-z initarray=';
      if cs_link_nolink in current_settings.globalswitches then
        InitFiniStr:=InitFiniStr+''''+exportlib.initname+''''
      else
        InitFiniStr:=InitFiniStr+exportlib.initname;
      if (exportlib.fininame<>'') then
        begin
          if cs_link_nolink in current_settings.globalswitches then
            InitFiniStr:=InitFiniStr+' -z finiarray='''+exportlib.initname+''''
          else
            InitFiniStr:=InitFiniStr+' -z finiarray='+exportlib.fininame;
        end;
    end;

{ Call linker }
  if use_gnu_ld then
    SplitBinCmd(Info.DllCmd[1],binstr,cmdstr)
  else
    SplitBinCmd(Info.DllCmd[3],binstr,cmdstr);
  Replace(cmdstr,'$EXE',maybequoted(current_module.sharedlibfilename));
  Replace(cmdstr,'$OPT',Info.ExtraOptions);
  Replace(cmdstr,'$INITFINI',InitFiniStr);
  if use_gnu_ld then
    Replace(cmdstr,'$RES',maybequoted(outputexedir+Info.ResName))
  else
    begin
      Replace(cmdstr,'$VERSIONFILE',maybequoted(outputexedir+Info.ResName));
      linkstr:='';
      while not linkres.data.Empty do
        begin
          s:=linkres.data.GetFirst;
	  if s<>'' then
            linkstr:=linkstr+' '+s;
        end;
      linkres.free;
      Replace(cmdstr,'$RESDATA',linkstr);
    end;
  if BinStr[1]<>'/' then
    success:=DoExec(FindUtil(utilsprefix+BinStr),CmdStr,true,false)
  else { Using utilsprefix has no sense on /usr/bin/ld }
    success:=DoExec(BinStr,Trim(CmdStr),true,false);


{ Strip the library ? }
  if success and (cs_link_strip in current_settings.globalswitches) then
   begin
     SplitBinCmd(Info.DllCmd[2],binstr,cmdstr);
     Replace(cmdstr,'$EXE',maybequoted(current_module.sharedlibfilename));
     success:=DoExec(utilsprefix+FindUtil(binstr),cmdstr,true,false);
   end;

{ Remove ReponseFile }
{$IFNDEF LinkTest}
  if (success) and not(cs_link_nolink in current_settings.globalswitches) then
   DeleteFile(outputexedir+Info.ResName);
{$ENDIF}
  MakeSharedLibrary:=success;   { otherwise a recursive call to link method }
end;


{*****************************************************************************
                                     Initialize
*****************************************************************************}

initialization
{$ifdef i386}
  RegisterExternalLinker(system_i386_solaris_info,TLinkersolaris);
  RegisterImport(system_i386_solaris,TImportLibsolaris);
  RegisterExport(system_i386_solaris,TExportLibsolaris);
  RegisterTarget(system_i386_solaris_info);
{$endif i386}

{$ifdef x86_64}
  RegisterExternalLinker(system_x86_64_solaris_info,TLinkersolaris);
  RegisterImport(system_x86_64_solaris,TImportLibsolaris);
  RegisterExport(system_x86_64_solaris,TExportLibsolaris);
  RegisterTarget(system_x86_64_solaris_info);
{$endif x86_64}

{$ifdef sparc}
  RegisterExternalLinker(system_sparc_solaris_info,TLinkersolaris);
  RegisterImport(system_sparc_solaris,TImportLibsolaris);
  RegisterExport(system_sparc_solaris,TExportLibsolaris);
  RegisterTarget(system_sparc_solaris_info);
{$endif sparc}

  RegisterRes(res_elf_info,TWinLikeResourceFile);
end.
