{
    Copyright (c) 1998-2008 by Florian Klaempfl and Peter Vreman

    Reads command line options and config files

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
unit options;

{$i fpcdefs.inc}

interface

uses
  CClasses,cfileutl,
  globtype,globals,verbose,systems,cpuinfo, comprsrc;

Type
  TOption=class
    FirstPass,
    ParaLogo,
    NoPressEnter,
    FPCHelpLines,
    LogoWritten,
    FPUSetExplicitly,
    CPUSetExplicitly,
    OptCPUSetExplicitly: boolean;
    FileLevel : longint;
    QuickInfo : string;
    FPCBinaryPath: string;
    ParaIncludePath,
    ParaUnitPath,
    ParaObjectPath,
    ParaLibraryPath,
    ParaFrameworkPath : TSearchPathList;
    ParaAlignment   : TAlignmentInfo;
    Constructor Create;
    Destructor Destroy;override;
    procedure WriteLogo;
    procedure WriteInfo;
    procedure WriteHelpPages;
    procedure WriteQuickInfo;
    procedure IllegalPara(const opt:TCmdStr);
    procedure UnsupportedPara(const opt:TCmdStr);
    procedure IgnoredPara(const opt:TCmdStr);
    function  Unsetbool(var Opts:TCmdStr; Pos: Longint):boolean;
    procedure interpret_option(const opt :TCmdStr;ispara:boolean);
    procedure Interpret_envvar(const envname : TCmdStr);
    procedure Interpret_file(const filename : TPathStr);
    procedure Read_Parameters;
    procedure parsecmd(cmd:TCmdStr);
    procedure TargetOptions(def:boolean);
    procedure CheckOptionsCompatibility;
    procedure ForceStaticLinking;
   protected
    MacVersionSet: boolean;
    function ParseMacVersionMin(out minstr, emptystr: string; const compvarname, value: string; ios: boolean): boolean;
    procedure MaybeSetDefaultMacVersionMacro;
  end;

  TOptionClass=class of toption;

var
  coption : TOptionClass;

procedure read_arguments(cmd:TCmdStr);


implementation

uses
  widestr,
  {$if FPC_FULLVERSION<20700}ccharset{$else}charset{$endif},
  SysUtils,
  version,
  cutils,cmsgs,
  comphook,
  symtable,scanner,rabase,
  wpobase,
  symconst,
  i_bsd;

const
  page_size = 24;

var
  option     : toption;
  read_configfile,        { read config file, set when a cfgfile is found }
  disable_configfile : boolean;
  fpcdir,
  ppccfg,
  param_file    : string;   { file to compile specified on the commandline }


{****************************************************************************
                     Options not supported on all platforms
****************************************************************************}

const
  { pointer checking (requires special code in FPC_CHECKPOINTER,
    and can never work for libc-based targets or any other program
    linking to an external library)
  }
  supported_targets_gc = [system_i386_linux,system_powerpc_linux]
                        + [system_i386_win32]
                        + [system_i386_GO32V2]
                        + [system_i386_os2]
                        + [system_i386_beos,system_i386_haiku]
                        + [system_powerpc_morphos];

  { gprof (requires implementation of g_profilecode in the code generator) }
  supported_targets_pg = [system_i386_linux,system_x86_64_linux]
                        + [system_i386_win32]
                        + [system_powerpc_darwin,system_x86_64_darwin]
                        + [system_i386_GO32V2]
                        + [system_i386_freebsd]
                        + [system_i386_netbsd]
                        + [system_i386_wdosx];

  suppported_targets_x_smallr = systems_linux + systems_solaris
                             + [system_i386_haiku]
                             + [system_i386_beos];

{****************************************************************************
                                 Defines
****************************************************************************}

procedure set_default_link_type;
begin
  undef_system_macro('FPC_LINK_SMART');
  def_system_macro('FPC_LINK_STATIC');
  undef_system_macro('FPC_LINK_DYNAMIC');
  init_settings.globalswitches:=init_settings.globalswitches+[cs_link_static];
  init_settings.globalswitches:=init_settings.globalswitches-[cs_link_shared,cs_link_smart];
end;

{****************************************************************************
                                 Toption
****************************************************************************}

procedure StopOptions(err:longint);
begin
  if assigned(Option) then
   begin
     Option.free;
     Option:=nil;
   end;
  raise ECompilerAbortSilent.Create;
end;


procedure Toption.WriteLogo;
var
  p : pchar;
begin
  if not LogoWritten then
    begin
      p:=MessagePchar(option_logo);
      while assigned(p) do
        Comment(V_Normal,GetMsgLine(p));
      LogoWritten:= true;
    end;
end;


procedure Toption.WriteInfo;
var
  p : pchar;
  hs,hs1,s : TCmdStr;
  target : tsystem;
  cpu : tcputype;
  fpu : tfputype;
  opt : toptimizerswitch;
  wpopt: twpoptimizerswitch;
  abi : tabi;
{$if defined(arm) or defined(avr)}
  controllertype : tcontrollertype;
{$endif defined(arm) or defined(avr)}
begin
  p:=MessagePchar(option_info);
  while assigned(p) do
   begin
     s:=GetMsgLine(p);
     { list OS Targets }
     if pos('$OSTARGETS',s)>0 then
      begin
        for target:=low(tsystem) to high(tsystem) do
         if assigned(targetinfos[target]) then
          begin
            hs:=s;
            hs1:=targetinfos[target]^.name;
            if tf_under_development in targetinfos[target]^.flags then
             hs1:=hs1+' (under development)';
            Replace(hs,'$OSTARGETS',hs1);
            Comment(V_Normal,hs);
          end;
      end
     else if pos('$INSTRUCTIONSETS',s)>0 then
      begin
        for cpu:=low(tcputype) to high(tcputype) do
          begin
            hs:=s;
            hs1:=cputypestr[cpu];
            if hs1<>'' then
              begin
                Replace(hs,'$INSTRUCTIONSETS',hs1);
                Comment(V_Normal,hs);
              end;
          end;
      end
     else if pos('$FPUINSTRUCTIONSETS',s)>0 then
      begin
        for fpu:=low(tfputype) to high(tfputype) do
          begin
            hs:=s;
            hs1:=fputypestr[fpu];
            if hs1<>'' then
              begin
                Replace(hs,'$FPUINSTRUCTIONSETS',hs1);
                Comment(V_Normal,hs);
              end;
          end;
      end
     else if pos('$ABITARGETS',s)>0 then
      begin
        for abi:=low(abi) to high(abi) do
          begin
            hs:=s;
            hs1:=abi2str[abi];
            if hs1<>'' then
              begin
                Replace(hs,'$ABITARGETS',hs1);
                Comment(V_Normal,hs);
              end;
          end;
      end
     else if pos('$OPTIMIZATIONS',s)>0 then
      begin
        for opt:=low(toptimizerswitch) to high(toptimizerswitch) do
          begin
            if opt in supported_optimizerswitches then
              begin
                hs:=s;
                hs1:=OptimizerSwitchStr[opt];
                if hs1<>'' then
                  begin
                    Replace(hs,'$OPTIMIZATIONS',hs1);
                    Comment(V_Normal,hs);
                  end;
              end;
          end;
      end
     else if pos('$WPOPTIMIZATIONS',s)>0 then
      begin
        for wpopt:=low(twpoptimizerswitch) to high(twpoptimizerswitch) do
          begin
{           currently all whole program optimizations are platform-independent
            if opt in supported_wpoptimizerswitches then
}
              begin
                hs:=s;
                hs1:=WPOptimizerSwitchStr[wpopt];
                if hs1<>'' then
                  begin
                    Replace(hs,'$WPOPTIMIZATIONS',hs1);
                    Comment(V_Normal,hs);
                  end;
              end;
          end
      end
     else if pos('$CONTROLLERTYPES',s)>0 then
      begin
{$if defined(arm) or defined(avr)}
        for controllertype:=low(tcontrollertype) to high(tcontrollertype) do
          begin
{           currently all whole program optimizations are platform-independent
            if opt in supported_wpoptimizerswitches then
}
              begin
                hs:=s;
                hs1:=embedded_controllers[controllertype].ControllerTypeStr;
                if hs1<>'' then
                  begin
                    Replace(hs,'$CONTROLLERTYPES',hs1);
                    Comment(V_Normal,hs);
                  end;
              end;
          end
{$else defined(arm) or defined(avr)}
{$endif defined(arm) or defined(avr)}
      end
     else
      Comment(V_Normal,s);
   end;
  StopOptions(0);
end;


procedure Toption.WriteHelpPages;

  function PadEnd(s:string;i:longint):string;
  begin
    while (length(s)<i) do
     s:=s+' ';
    PadEnd:=s;
  end;

var
  lastident,
  j,outline,
  ident,
  lines : longint;
  show  : boolean;
  opt   : string[32];
  input,
  s     : string;
  p     : pchar;
begin
  WriteLogo;
  Lines:=4;
  if FPCHelpLines then
   Message1(option_usage,FixFileName(FPCBinaryPath))
  else
   Message1(option_usage,FixFileName(system.paramstr(0)));
  lastident:=0;
  p:=MessagePChar(option_help_pages);
  while assigned(p) do
   begin
   { get a line and reset }
     s:=GetMsgLine(p);
     ident:=0;
     show:=false;
   { parse options }
     case s[1] of
      'F': if FPCHelpLines then
            Show := true;
{$ifdef UNITALIASES}
      'a',
{$endif}
{$ifdef EXTDEBUG}
      'e',
{$endif EXTDEBUG}
{$ifdef i386}
      '3',
{$endif}
{$ifdef x86_64}
      '4',
{$endif}
{$ifdef m68k}
      '6',
{$endif}
{$ifdef arm}
      'A',
{$endif}
{$ifdef powerpc}
      'P',
{$endif}
{$ifdef powerpc64}
      'p',
{$endif}
{$ifdef sparc}
      'S',
{$endif}
{$ifdef vis}
      'I',
{$endif}
{$ifdef avr}
      'V',
{$endif}
{$ifdef jvm}
      'J',
{$endif}
      '*' : show:=true;
     end;
     if show then
      begin
        case s[2] of
         'g',
{$ifdef Unix}
         'L',
{$endif}
{$ifdef os2}
         'O',
{$endif}
         '*' : show:=true;
        else
         show:=false;
        end;
      end;
   { now we may show the message or not }
     if show then
      begin
        case s[3] of
         '0' : begin
                 ident:=0;
                 outline:=0;
               end;
         '1' : begin
                 ident:=2;
                 outline:=7;
               end;
         '2' : begin
                 ident:=6;
                 outline:=11;
               end;
         '3' : begin
                 ident:=9;
                 outline:=11;
               end;
        end;
        j:=pos('_',s);
        opt:=Copy(s,4,j-4);
        if opt='*' then
         opt:=''
        else
        if opt=' ' then
         opt:=PadEnd(opt,outline)
        else
         opt:=PadEnd('-'+opt,outline);
        if (ident=0) and (lastident<>0) then
         begin
           Comment(V_Normal,'');
           inc(Lines);
         end;
      { page full ? }
        if (lines >= page_size - 1) then
         begin
           if not NoPressEnter then
            begin
              Message(option_help_press_enter);
              readln(input);
              if upper(input)='Q' then
               StopOptions(0);
            end;
           lines:=0;
         end;
        Comment(V_Normal,PadEnd('',ident)+opt+Copy(s,j+1,255));
        LastIdent:=Ident;
        inc(Lines);
      end;
   end;
  StopOptions(0);
end;


procedure Toption.IllegalPara(const opt:TCmdStr);
begin
  Message1(option_illegal_para,opt);
  Message(option_help_pages_para);
  StopOptions(1);
end;


procedure toption.UnsupportedPara(const opt: TCmdStr);
begin
  Message1(option_unsupported_target,opt);
  StopOptions(1);
end;


procedure toption.IgnoredPara(const opt: TCmdStr);
begin
  Message1(option_ignored_target,opt);
end;


procedure toption.ForceStaticLinking;
begin
  def_system_macro('FPC_LINK_STATIC');
  undef_system_macro('FPC_LINK_SMART');
  undef_system_macro('FPC_LINK_DYNAMIC');
  include(init_settings.globalswitches,cs_link_static);
  exclude(init_settings.globalswitches,cs_link_smart);
  exclude(init_settings.globalswitches,cs_link_shared);
  LinkTypeSetExplicitly:=true;
end;


function toption.ParseMacVersionMin(out minstr, emptystr: string; const compvarname, value: string; ios: boolean): boolean;

  function subval(start,maxlen: longint; out stop: longint): string;
    var
      i: longint;
    begin
      result:='';
      i:=start;
      while (i<=length(value)) and
            (value[i] in ['0'..'9']) do
        inc(i);
      { sufficient amount of digits? }
      if (i=start) or
         (i-start>maxlen) then
        exit;
      result:=copy(value,start,i-start);
      stop:=i;
    end;

  var
    temp,
    compvarvalue: string[15];
    i: longint;
  begin
    minstr:=value;
    emptystr:='';
    MacVersionSet:=false;
    { check whether the value is a valid version number }
    if value='' then
      begin
        undef_system_macro(compvarname);
        exit(true);
      end;
    { major version number }
    compvarvalue:=subval(1,2,i);
    { not enough digits -> invalid }
    if compvarvalue='' then
      exit(false);
    { already end of string -> invalid }
    if (i>=length(value)) or
       (value[i]<>'.') then
      exit(false);
    { minor version number }
    temp:=subval(i+1,2,i);
    if temp='' then
      exit(false);
    { on Mac OS X, the minor version number is limited to 1 digit }
    if not ios then
      begin
        if length(temp)<>1 then
          exit(false);
      end
    { the minor version number always takes up two digits on iOS }
    else if length(temp)=1 then
      temp:='0'+temp;
    compvarvalue:=compvarvalue+temp;
    { optional patch level }
    if i<=length(value) then
      begin
        if value[i]<>'.' then
          exit(false);
        temp:=subval(i+1,2,i);
        if temp='' then
          exit(false);
        { there's only room for a single digit patch level in the version macro
          for Mac OS X. gcc sets it to zero if there are more digits, but that
          seems worse than clamping to 9 (don't declare as invalid like with
          minor version number, because there is a precedent like 10.4.11)
        }
        if not ios then
          begin
            if length(temp)<>1 then
              temp:='9';
          end
        else
          begin
            { on iOS, the patch level is always two digits }
            if length(temp)=1 then
              temp:='0'+temp;
          end;
        compvarvalue:=compvarvalue+temp;
        { must be the end }
        if i<=length(value) then
          exit(false);
      end
    else if not ios then
      compvarvalue:=compvarvalue+'0'
    else
      compvarvalue:=compvarvalue+'00';
    set_system_compvar(compvarname,compvarvalue);
    MacVersionSet:=true;
    result:=true;
  end;


procedure TOption.MaybeSetDefaultMacVersionMacro;
var
  envstr: ansistring;
begin
  if not(target_info.system in systems_darwin) then
    exit;
  if MacVersionSet then
    exit;
  { check for deployment target set via environment variable }
  if not(target_info.system in [system_i386_iphonesim,system_arm_darwin]) then
    begin
      envstr:=GetEnvironmentVariable('MACOSX_DEPLOYMENT_TARGET');
      if envstr<>'' then
        if not ParseMacVersionMin(MacOSXVersionMin,iPhoneOSVersionMin,'MAC_OS_X_VERSION_MIN_REQUIRED',envstr,false) then
          Message1(option_invalid_macosx_deployment_target,envstr)
        else
          exit;
    end
  else
    begin
      envstr:=GetEnvironmentVariable('IPHONEOS_DEPLOYMENT_TARGET');
      if envstr<>'' then
        if not ParseMacVersionMin(iPhoneOSVersionMin,MacOSXVersionMin,'IPHONE_OS_VERSION_MIN_REQUIRED',envstr,true) then
          Message1(option_invalid_iphoneos_deployment_target,envstr)
        else
          exit;
    end;
  { nothing specified -> defaults }
  case target_info.system of
    system_powerpc_darwin:
      begin
        set_system_compvar('MAC_OS_X_VERSION_MIN_REQUIRED','1030');
        MacOSXVersionMin:='10.3';
      end;
    system_powerpc64_darwin,
    system_i386_darwin:
      begin
        set_system_compvar('MAC_OS_X_VERSION_MIN_REQUIRED','1040');
        MacOSXVersionMin:='10.4';
      end;
    system_x86_64_darwin:
      begin
        { actually already works on 10.4, but it's unlikely any 10.4 system
          with an x86-64 is still in use, so don't default to it }
        set_system_compvar('MAC_OS_X_VERSION_MIN_REQUIRED','1050');
        MacOSXVersionMin:='10.5';
      end;
    system_arm_darwin,
    system_i386_iphonesim:
      begin
        set_system_compvar('IPHONE_OS_VERSION_MIN_REQUIRED','30000');
        iPhoneOSVersionMin:='3.0';
      end;
    else
      internalerror(2012031001);
  end;
end;


function Toption.Unsetbool(var Opts:TCmdStr; Pos: Longint):boolean;
{ checks if the character after pos in Opts is a + or a - and returns resp.
  false or true. If it is another character (or none), it also returns false }
begin
  UnsetBool := false;
  if Length(Opts)>Pos then
   begin
    inc(Pos);
    UnsetBool := Opts[Pos] = '-';
    if Opts[Pos] in ['-','+']then
     delete(Opts,Pos,1);
   end;
end;


procedure TOption.interpret_option(const opt:TCmdStr;ispara:boolean);
var
  code : integer;
  c    : char;
  more : TCmdStr;
  major,minor : longint;
  error : integer;
  j,l   : longint;
  d,s   : TCmdStr;
  unicodemapping : punicodemap;
begin
  if opt='' then
   exit;

  { only parse define,undef,target,verbosity,link etc options the firsttime }
  if firstpass and
     not(
         (opt[1]='-') and
         (
          ((length(opt)>1) and (opt[2] in ['i','d','v','T','u','n','X','l'])) or
          ((length(opt)>3) and (opt[2]='F') and (opt[3]='e'))
         )
        ) then
    exit;

  Message1(option_handling_option,opt);
  case opt[1] of
    '-' :
      begin
         more:=Copy(opt,3,2147483647);
         if firstpass then
           Message1(option_interpreting_firstpass_option,opt)
         else
           Message1(option_interpreting_option,opt);
         case opt[2] of
           '?' :
             begin
               if (More <> '') and (More [1] = 'F') then
                 begin
                   FPCHelpLines := true;
                   Delete (More, 1, 1);
                   FPCBinaryPath := More;
                 end;
               WriteHelpPages;
             end;

           'a' :
             begin
               include(init_settings.globalswitches,cs_asm_leave);
               j:=1;
               while j<=length(more) do
                begin
                  case more[j] of
                    'l' :
                      include(init_settings.globalswitches,cs_asm_source);
                    'r' :
                      include(init_settings.globalswitches,cs_asm_regalloc);
                    't' :
                      include(init_settings.globalswitches,cs_asm_tempalloc);
                    'n' :
                      include(init_settings.globalswitches,cs_asm_nodes);
                    'p' :
                      begin
                        exclude(init_settings.globalswitches,cs_asm_leave);
                        if UnsetBool(More, 0) then
                          exclude(init_settings.globalswitches,cs_asm_pipe)
                        else
                          include(init_settings.globalswitches,cs_asm_pipe);
                      end;
                    '-' :
                      init_settings.globalswitches:=init_settings.globalswitches -
                          [cs_asm_leave, cs_asm_source,cs_asm_regalloc, cs_asm_tempalloc,
                           cs_asm_nodes, cs_asm_pipe];
                    else
                      IllegalPara(opt);
                  end;
                  inc(j);
                end;
             end;

           'A' :
             begin
               paratargetasm:=find_asm_by_string(More);
               if paratargetasm=as_none then
                 IllegalPara(opt);
             end;

           'b' :
             begin
               // Message1(option_obsolete_switch,'-b');
               if UnsetBool(More,0) then
                 begin
                   init_settings.moduleswitches:=init_settings.moduleswitches-[cs_browser];
                   init_settings.moduleswitches:=init_settings.moduleswitches-[cs_local_browser];
                 end
               else
                 begin
                   init_settings.moduleswitches:=init_settings.moduleswitches+[cs_browser];
                 end;
               if More<>'' then
                 if (More='l') or (More='l+') then
                   init_settings.moduleswitches:=init_settings.moduleswitches+[cs_local_browser]
                 else if More='l-' then
                   init_settings.moduleswitches:=init_settings.moduleswitches-[cs_local_browser]
                 else
                   IllegalPara(opt);
             end;

           'B' :
             do_build:=not UnSetBool(more,0);

           'C' :
             begin
               j:=1;
               while j<=length(more) do
                begin
                  case more[j] of
                    '3' :
                      If UnsetBool(More, j) then
                        exclude(init_settings.localswitches,cs_ieee_errors)
                      Else
                        include(init_settings.localswitches,cs_ieee_errors);
                    'a' :
                      begin
                        s:=upper(copy(more,j+1,length(more)-j));
                        if not(SetAbiType(s,target_info.abi)) then
                          IllegalPara(opt);
                        break;
                      end;

                    'b' :
                       begin
                         if UnsetBool(More, j) then
                           target_info.endian:=endian_little
                         else
                           target_info.endian:=endian_big;
                       end;

                    'c' :
                       begin
                         if not SetAktProcCall(upper(copy(more,j+1,length(more)-j)),init_settings.defproccall) then
                          IllegalPara(opt);
                         break;
                       end;
{$ifdef cpufpemu}
                    'e' :
                       begin
                         If UnsetBool(More, j) then
                           exclude(init_settings.moduleswitches,cs_fp_emulation)
                         Else
                           include(init_settings.moduleswitches,cs_fp_emulation);
                       end;
{$endif cpufpemu}
                    'f' :
                      begin
                        s:=upper(copy(more,j+1,length(more)-j));
                        if not(SetFpuType(s,init_settings.fputype)) then
                          IllegalPara(opt);
                        FPUSetExplicitly:=True;
                        break;
                      end;
                    'F' :
                       begin
                         if not SetMinFPConstPrec(copy(more,j+1,length(more)-j),init_settings.minfpconstprec) then
                           IllegalPara(opt);
                         break;
                       end;
                    'g' :
                       begin
                         if tf_no_pic_supported in target_info.flags then
                           begin
                             { consume a possible '-' coming after it }
                             UnsetBool(More, j);
                             message(scan_w_pic_ignored);
                           end
                         else if UnsetBool(More, j) then
                           exclude(init_settings.moduleswitches,cs_create_pic)
                         else
                           include(init_settings.moduleswitches,cs_create_pic);
                      end;
                    'h' :
                      begin
                         val(copy(more,j+1,length(more)-j),heapsize,code);
                         if (code<>0) or (heapsize<1024) then
                           IllegalPara(opt);
                         break;
                      end;
                    'i' :
                      If UnsetBool(More, j) then
                        exclude(init_settings.localswitches,cs_check_io)
                      else
                        include(init_settings.localswitches,cs_check_io);
                    'n' :
                      If UnsetBool(More, j) then
                        exclude(init_settings.globalswitches,cs_link_nolink)
                      Else
                        include(init_settings.globalswitches,cs_link_nolink);
                    'N' :
                      If UnsetBool(More, j) then
                        exclude(init_settings.localswitches,cs_check_low_addr_load)
                      Else
                        include(init_settings.localswitches,cs_check_low_addr_load);
                    'o' :
                      If UnsetBool(More, j) then
                        exclude(init_settings.localswitches,cs_check_overflow)
                      Else
                        include(init_settings.localswitches,cs_check_overflow);
                    'O' :
                      If UnsetBool(More, j) then
                        exclude(init_settings.localswitches,cs_check_ordinal_size)
                      Else
                        include(init_settings.localswitches,cs_check_ordinal_size);
                    'p' :
                      begin
                        s:=upper(copy(more,j+1,length(more)-j));
                        if not(Setcputype(s,init_settings.cputype)) then
                          IllegalPara(opt);
                        CPUSetExplicitly:=true;
                        break;
                      end;
                    'P':
                      begin
                        delete(more,1,1);
                        if upper(copy(more,1,pos('=',more)-1))='PACKSET' then
                          begin
                            delete(more,1,pos('=',more));
                            if more='0' then
                              init_settings.setalloc:=0
                            else if (more='1') or (more='DEFAULT') or (more='NORMAL') then
                              init_settings.setalloc:=1
                            else if more='2' then
                              init_settings.setalloc:=2
                            else if more='4' then
                              init_settings.setalloc:=4
                            else if more='8' then
                              init_settings.setalloc:=8
                            else
                              IllegalPara(opt);
                          end
                        else
                          IllegalPara(opt);
                      end;
                    'r' :
                      If UnsetBool(More, j) then
                        exclude(init_settings.localswitches,cs_check_range)
                      Else
                        include(init_settings.localswitches,cs_check_range);
                    'R' :
                      If UnsetBool(More, j) then
                        begin
                          exclude(init_settings.localswitches,cs_check_range);
                          exclude(init_settings.localswitches,cs_check_object);
                        end
                      Else
                        begin
                          include(init_settings.localswitches,cs_check_range);
                          include(init_settings.localswitches,cs_check_object);
                        end;
                    's' :
                      begin
                         val(copy(more,j+1,length(more)-j),stacksize,code);
                         if (code<>0) or (stacksize>=67107840) or (stacksize<1024) then
                          IllegalPara(opt);
                         break;
                      end;
                    't' :
                       If UnsetBool(More, j) then
                         exclude(init_settings.localswitches,cs_check_stack)
                       Else
                         include(init_settings.localswitches,cs_check_stack);
                    'D' :
                       If UnsetBool(More, j) then
                         exclude(init_settings.moduleswitches,cs_create_dynamic)
                       Else
                         include(init_settings.moduleswitches,cs_create_dynamic);
                    'X' :
                       If UnsetBool(More, j) then
                         exclude(init_settings.moduleswitches,cs_create_smart)
                       Else
                         include(init_settings.moduleswitches,cs_create_smart);
                    'T' :
                      begin
                        if not UpdateTargetSwitchStr(copy(more,j+1,length(more)),init_settings.targetswitches) then
                          IllegalPara(opt);
                        break;
                      end;
                    'v' :
                       If target_info.system in systems_jvm then
                         If UnsetBool(More, j) then
                           exclude(init_settings.localswitches,cs_check_var_copyout)
                         Else
                           include(init_settings.localswitches,cs_check_var_copyout)
                       else
                         IllegalPara(opt)
                    else
                       IllegalPara(opt);
                  end;
                  inc(j);
                end;
             end;

           'd' :
             if more <> '' then
               begin
                 l:=Pos(':=',more);
                 if l>0 then
                   set_system_compvar(Copy(more,1,l-1),Copy(more,l+2,255))
                 else
                   def_system_macro(more);
               end;
           'D' :
             begin
               include(init_settings.globalswitches,cs_link_deffile);
               j:=1;
               while j<=length(more) do
                begin
                  case more[j] of
                    'd' :
                      begin
                        description:=Copy(more,j+1,255);
                        break;
                      end;
                    'v' :
                      begin
                        dllversion:=Copy(more,j+1,255);
                        l:=pos('.',dllversion);
                        dllminor:=0;
                        error:=0;
                        if l>0 then
                         begin
                           val(copy(dllversion,l+1,255),minor,error);
                           if (error=0) and
                              (minor>=0) and (minor<=$ffff) then
                             dllminor:=minor
                           else
                             if error=0 then
                               error:=1;
                         end;
                        if l=0 then
                          l:=256;
                        dllmajor:=1;
                        if error=0 then
                          val(copy(dllversion,1,l-1),major,error);
                        if (error=0) and (major>=0) and (major<=$ffff) then
                          dllmajor:=major
                        else
                          if error=0 then
                            error:=1;
                        if error<>0 then
                          Message1(scan_w_wrong_version_ignored,dllversion);
                        break;
                      end;
                    'w' :
                      usewindowapi:=true;
                    '-' :
                      begin
                        exclude(init_settings.globalswitches,cs_link_deffile);
                        usewindowapi:=false;
                      end;
                    else
                      IllegalPara(opt);
                  end;
                  inc(j);
                end;
             end;

           'e' :
             exepath:=FixPath(More,true);

           'E' :
             begin
               if UnsetBool(More, 0) then
                 exclude(init_settings.globalswitches,cs_link_nolink)
               else
                 include(init_settings.globalswitches,cs_link_nolink);
             end;

           'f' :
             begin
               if more='PIC' then
                 begin
                   if tf_no_pic_supported in target_info.flags then
                     message(scan_w_pic_ignored)
                   else
                     include(init_settings.moduleswitches,cs_create_pic)
                 end
               else
                 IllegalPara(opt);
             end;

           'F' :
             begin
               if more='' then
                 IllegalPara(opt);
               c:=more[1];
               Delete(more,1,1);
               DefaultReplacements(More);
               case c of
                 'a' :
                   autoloadunits:=more;
                 'c' :
                   begin
                     if (upper(more)='UTF8') or (upper(more)='UTF-8') then
                       init_settings.sourcecodepage:=CP_UTF8
                     else if not(cpavailable(more)) then
                       Message1(option_code_page_not_available,more)
                     else
                       init_settings.sourcecodepage:=codepagebyname(more);
                     include(init_settings.moduleswitches,cs_explicit_codepage);
                   end;
                 'C' :
                   RCCompiler := More;
                 'd' :
                   if UnsetBool(more, 0) then
                     init_settings.disabledircache:=false
                   else
                     init_settings.disabledircache:=true;
                 'D' :
                   utilsdirectory:=FixPath(More,true);
                 'e' :
                   SetRedirectFile(More);
                 'E' :
                   OutputExeDir:=FixPath(More,true);
                 'f' :
                     if (target_info.system in systems_darwin) then
                       if ispara then
                         ParaFrameworkPath.AddPath(More,false)
                       else
                         frameworksearchpath.AddPath(More,true)
                     else
                       IllegalPara(opt);
                 'i' :
                   begin
                     if ispara then
                       ParaIncludePath.AddPath(More,false)
                     else
                       includesearchpath.AddPath(More,true);
                   end;
                 'm' :
                   begin
                     s:=ExtractFileDir(more);
                     if TryStrToInt(ExtractFileName(more),j) then
                       begin
                         unicodemapping:=loadunicodemapping(More,More+'.txt',j);
                         if assigned(unicodemapping) then
                           registermapping(unicodemapping)
                         else
                           IllegalPara(opt);
                       end
                     else
                       IllegalPara(opt);
                   end;
                 'g' :
                   Message2(option_obsolete_switch_use_new,'-Fg','-Fl');
                 'l' :
                   begin
                     if ispara then
                       ParaLibraryPath.AddPath(sysrootpath,More,false)
                     else
                       LibrarySearchPath.AddPath(sysrootpath,More,true);
                   end;
                 'L' :
                   begin
                     if More<>'' then
                       ParaDynamicLinker:=More
                     else
                       IllegalPara(opt);
                   end;
                 'o' :
                   begin
                     if ispara then
                       ParaObjectPath.AddPath(More,false)
                     else
                       ObjectSearchPath.AddPath(More,true);
                   end;
                 'r' :
                   Msgfilename:=More;
                 'R' :
                   ResCompiler := More;
                 'u' :
                   begin
                     if ispara then
                       ParaUnitPath.AddPath(More,false)
                     else
                       unitsearchpath.AddPath(More,true);
                   end;
                 'U' :
                   OutputUnitDir:=FixPath(More,true);
                 'W',
                 'w':
                   begin
                     if More<>'' then
                       begin
                         DefaultReplacements(More);
                         D:=ExtractFilePath(More);
                         if (D<>'') then
                           D:=FixPath(D,True);
                         D:=D+ExtractFileName(More);
                         if (c='W') then
                           WpoFeedbackOutput:=D
                         else
                           WpoFeedbackInput:=D;
                       end
                     else
                       IllegalPara(opt);
                   end;
                 else
                   IllegalPara(opt);
               end;
             end;

           'g' :
             begin
               if UnsetBool(More, 0) then
                begin
                  exclude(init_settings.moduleswitches,cs_debuginfo);
                  exclude(init_settings.globalswitches,cs_use_heaptrc);
                  exclude(init_settings.globalswitches,cs_use_lineinfo);
                  exclude(init_settings.localswitches,cs_checkpointer);
                  localvartrashing := -1;
                end
               else
                begin
                  include(init_settings.moduleswitches,cs_debuginfo);
                  if paratargetdbg=dbg_none then
                    paratargetdbg:=target_info.dbg;
                end;
               if not RelocSectionSetExplicitly then
                 RelocSection:=false;
               j:=1;
               while j<=length(more) do
                 begin
                   case more[j] of
                     'c' :
                       begin
                         if UnsetBool(More, j) then
                           exclude(init_settings.localswitches,cs_checkpointer)
                         else if (target_info.system in supported_targets_gc) then
                           include(init_settings.localswitches,cs_checkpointer)
                         else
                           UnsupportedPara('-gc');
                       end;
                     'h' :
                       begin
                         if UnsetBool(More, j) then
                           exclude(init_settings.globalswitches,cs_use_heaptrc)
                         else
                           include(init_settings.globalswitches,cs_use_heaptrc);
                       end;
                     'l' :
                       begin
                         if UnsetBool(More, j) then
                           exclude(init_settings.globalswitches,cs_use_lineinfo)
                         else
                           include(init_settings.globalswitches,cs_use_lineinfo);
                       end;
                     'o' :
                       begin
                         if not UpdateDebugStr(copy(more,j+1,length(more)),init_settings.debugswitches) then
                           IllegalPara(opt);
                         break;
                       end;
                     'p' :
                       begin
                         if UnsetBool(More, j) then
                           exclude(init_settings.globalswitches,cs_stabs_preservecase)
                         else
                           include(init_settings.globalswitches,cs_stabs_preservecase);
                       end;
                     's' :
                       begin
                         paratargetdbg:=dbg_stabs;
                       end;
                     't' :
                       begin
                         if UnsetBool(More, j) then
                            localvartrashing := -1
                         else
                           localvartrashing := (localvartrashing + 1) mod nroftrashvalues;
                       end;
                     'v' :
                       begin
                         if UnsetBool(More, j) then
                           exclude(init_settings.globalswitches,cs_gdb_valgrind)
                         else
                           include(init_settings.globalswitches,cs_gdb_valgrind);
                       end;
                     'w' :
                       begin
                         if (j<length(more)) and (more[j+1] in ['2','3','4']) then
                           begin
                             case more[j+1] of
                               '2': paratargetdbg:=dbg_dwarf2;
                               '3': paratargetdbg:=dbg_dwarf3;
                               '4': paratargetdbg:=dbg_dwarf4;
                             end;
                             inc(j);
                           end
                         else
                           paratargetdbg:=dbg_dwarf2;
                       end;
                     else
                       IllegalPara(opt);
                   end;
                   inc(j);
                 end;
             end;

           'h' :
             begin
               NoPressEnter:=true;
               if (More <> '') and (More [1] = 'F') then
                 begin
                   FPCHelpLines := true;
                   Delete (More, 1, 1);
                   FPCBinaryPath := More;
                 end;
               WriteHelpPages;
             end;

           'i' :
             begin
               if More='' then
                 WriteInfo
               else
                 QuickInfo:=QuickInfo+More;
             end;

           'I' :
             begin
               if ispara then
                 ParaIncludePath.AddPath(More,false)
               else
                includesearchpath.AddPath(More,false);
             end;

           'k' :
             begin
               if more<>'' then
                 ParaLinkOptions:=ParaLinkOptions+' '+More
               else
                 IllegalPara(opt);
             end;

           'l' :
             ParaLogo:=not UnSetBool(more,0);

           'm' :
             parapreprocess:=not UnSetBool(more,0);

           'M' :
             begin
               more:=Upper(more);
               if not SetCompileMode(more, true) then
                 if not SetCompileModeSwitch(more, true) then
                   IllegalPara(opt);
             end;

           'n' :
             begin
               if More='' then
                 disable_configfile:=true
               else
                 IllegalPara(opt);
             end;

           'o' :
             begin
               if More<>'' then
                 begin
                   DefaultReplacements(More);
                   D:=ExtractFilePath(More);
                   if (D<>'') then
                     OutputExeDir:=FixPath(D,True);
                   OutputFileName:=ExtractFileName(More);
                 end
               else
                 IllegalPara(opt);
             end;

           'O' :
             begin
               j:=1;
               while j<=length(more) do
                begin
                  case more[j] of
                    '1' :
                      init_settings.optimizerswitches:=init_settings.optimizerswitches+level1optimizerswitches;
                    '2' :
                      init_settings.optimizerswitches:=init_settings.optimizerswitches+level2optimizerswitches;
                    '3' :
                      init_settings.optimizerswitches:=init_settings.optimizerswitches+level3optimizerswitches;
                    'a' :
                      begin
                        if not(UpdateAlignmentStr(Copy(Opt,j+3,255),ParaAlignment)) then
                          IllegalPara(opt);
                        break;
                      end;
                    's' :
                      include(init_settings.optimizerswitches,cs_opt_size);
                    'p' :
                      begin
                        if not Setcputype(copy(more,j+1,length(more)),init_settings.optimizecputype) then
                          begin
                            OptCPUSetExplicitly:=true;
                            { Give warning for old i386 switches }
                            if (Length(More)-j=1) and
                               (More[j+1]>='1') and (More[j+1]<='5')then
                              Message2(option_obsolete_switch_use_new,'-Op<nr>','-Op<name>')
                            else
                              IllegalPara(opt);
                          end;
                        break;
                      end;
                    'o' :
                      begin
                        if not UpdateOptimizerStr(copy(more,j+1,length(more)),init_settings.optimizerswitches) then
                         IllegalPara(opt);
                        break;
                      end;
                    '-' :
                      begin
                        init_settings.optimizerswitches:=[];
                        FillChar(ParaAlignment,sizeof(ParaAlignment),0);
                      end;
                    { Obsolete switches }
                    'g' :
                      Message2(option_obsolete_switch_use_new,'-Og','-Os');
                    'G' :
                      Message1(option_obsolete_switch,'-OG');
                    'r' :
                      Message2(option_obsolete_switch_use_new,'-Or','-O2 or -Ooregvar');
                    'u' :
                      Message2(option_obsolete_switch_use_new,'-Ou','-Oouncertain');
                    'w' :
                      begin
                        if not UpdateWpoStr(copy(more,j+1,length(more)),init_settings.dowpoptimizerswitches) then
                          IllegalPara(opt);
                        break;
                      end;
                    'W' :
                      begin
                        if not UpdateWpoStr(copy(more,j+1,length(more)),init_settings.genwpoptimizerswitches) then
                          IllegalPara(opt);
                        break;
                      end;
                    else
                      IllegalPara(opt);
                  end;
                  inc(j);
                end;
             end;

           'p' :
             begin
               if UnsetBool(More, 0) then
                 begin
                   init_settings.moduleswitches:=init_settings.moduleswitches-[cs_profile];
                   undef_system_macro('FPC_PROFILE');
                 end
               else
                 if Length(More)=0 then
                   IllegalPara(opt)
                 else
                 case more[1] of
                  'g' : if UnsetBool(more, 1) then
                         begin
                           exclude(init_settings.moduleswitches,cs_profile);
                           undef_system_macro('FPC_PROFILE');
                         end
                        else if (target_info.system in supported_targets_pg) then
                         begin
                           include(init_settings.moduleswitches,cs_profile);
                           def_system_macro('FPC_PROFILE');
                         end
                        else
                          UnsupportedPara('-pg');
                 else
                   IllegalPara(opt);
                 end;
             end;

           'P' : ; { Ignore used by fpc.pp }

           'R' :
             begin
               if not SetAsmReadMode(More,init_settings.asmmode) then
                 IllegalPara(opt);
             end;

           's' :
             begin
               if UnsetBool(More, 0) then
                 begin
                   init_settings.globalswitches:=init_settings.globalswitches-[cs_asm_extern,cs_link_extern,cs_link_nolink];
                   if more<>'' then
                     IllegalPara(opt);
                 end
               else
                 begin
                   init_settings.globalswitches:=init_settings.globalswitches+[cs_asm_extern,cs_link_extern,cs_link_nolink];
                   if more='h' then
                     init_settings.globalswitches:=init_settings.globalswitches-[cs_link_on_target]
                   else if more='t' then
                     init_settings.globalswitches:=init_settings.globalswitches+[cs_link_on_target]
                   else if more='r' then
                     init_settings.globalswitches:=init_settings.globalswitches+[cs_asm_leave,cs_no_regalloc]
                   else if more<>'' then
                     IllegalPara(opt);
                 end;
             end;

           'S' :
             begin
               if more='' then
                 IllegalPara(opt);
               if more[1]='I' then
                 begin
{$ifdef jvm}
                   UnsupportedPara('-SI');
{$endif}
                   if upper(more)='ICOM' then
                     init_settings.interfacetype:=it_interfacecom
                   else if upper(more)='ICORBA' then
                     init_settings.interfacetype:=it_interfacecorba
                   else
                     IllegalPara(opt);
                 end
               else
                begin
                  j:=1;
                  while j<=length(more) do
                   begin
                     case more[j] of
                       '2' : //an alternative to -Mobjfpc
                         SetCompileMode('OBJFPC',true);
                       'a' :
                         If UnsetBool(More, j) then
                           exclude(init_settings.localswitches,cs_do_assertion)
                         else
                           include(init_settings.localswitches,cs_do_assertion);
                       'c' :
                         If UnsetBool(More, j) then
                           exclude(init_settings.moduleswitches,cs_support_c_operators)
                         else
                           include(init_settings.moduleswitches,cs_support_c_operators);
                       'd' : //an alternative to -Mdelphi
                         SetCompileMode('DELPHI',true);
                       'e' :
                         begin
                           SetErrorFlags(copy(more,j+1,length(more)));
                           break;
                         end;
                       'f' :
                         begin
                           inc(j);
                           if more[j]='-' then
                             begin
                               features:=[];
                               if length(more)>j then
                                 IllegalPara(opt);
                             end
                           else
                             begin
                               if (IncludeFeature(upper(copy(more,j,length(more)-j+1)))) then
                                 j:=length(more)
                               else
                                 IllegalPara(opt);
                             end;
                         end;
                       'g' :
                         If UnsetBool(More, j) then
                           exclude(init_settings.moduleswitches,cs_support_goto)
                         else
                           include(init_settings.moduleswitches,cs_support_goto);
                       'h' :
                         If UnsetBool(More, j) then
                           exclude(init_settings.localswitches,cs_refcountedstrings)
                         else
                           include(init_settings.localswitches,cs_refcountedstrings);
                       'i' :
                         If UnsetBool(More, j) then
                           exclude(init_settings.localswitches,cs_do_inline)
                         else
                           include(init_settings.localswitches,cs_do_inline);
                       'k' :
                         If UnsetBool(More, j) then
                           exclude(init_settings.globalswitches,cs_load_fpcylix_unit)
                         else
                           include(init_settings.globalswitches,cs_load_fpcylix_unit);
                       'm' :
                         If UnsetBool(More, j) then
                           exclude(init_settings.moduleswitches,cs_support_macro)
                         else
                           include(init_settings.moduleswitches,cs_support_macro);
                       'o' : //an alternative to -Mtp
                         SetCompileMode('TP',true);
{$ifdef gpc_mode}
                       'p' : //an alternative to -Mgpc
                         SetCompileMode('GPC',true);
{$endif}
                       's' :
                         If UnsetBool(More, j) then
                           exclude(init_settings.globalswitches,cs_constructor_name)
                         else
                           include(init_settings.globalswitches,cs_constructor_name);
                       't' :
                         Message1(option_obsolete_switch,'-St');
                       'v' :
                         If UnsetBool(More, j) then
                           exclude(init_settings.globalswitches,cs_support_vectors)
                         else
                           include(init_settings.globalswitches,cs_support_vectors);
                       'x' :
                         If UnsetBool(More, j) then
                           exclude(init_settings.globalswitches,cs_support_exceptions)
                         else
                           include(init_settings.globalswitches,cs_support_exceptions);
                       'y' :
                         If UnsetBool(More, j) then
                           exclude(init_settings.localswitches,cs_typed_addresses)
                         else
                           include(init_settings.localswitches,cs_typed_addresses);
                       '-' :
                         begin
                           init_settings.globalswitches:=init_settings.globalswitches - [cs_constructor_name,cs_support_exceptions,
                                                                                         cs_support_vectors,cs_load_fpcylix_unit];

                           init_settings.localswitches:=init_settings.localswitches - [cs_do_assertion,cs_do_inline, cs_refcountedstrings,
                                                                                       cs_typed_addresses];

                           init_settings.moduleswitches:=init_settings.moduleswitches - [cs_support_c_operators, cs_support_goto,
                                                                                         cs_support_macro];
                         end;
                       else
                         IllegalPara(opt);
                     end;
                     inc(j);
                   end;
                end;
             end;

           'T' :
             begin
               more:=Upper(More);
               if paratarget=system_none then
                begin
                  { remove old target define }
                  TargetOptions(false);
                  { load new target }
                  paratarget:=find_system_by_string(More);
                  if paratarget<>system_none then
                    set_target(paratarget)
                  else
                    IllegalPara(opt);
                  { set new define }
                  TargetOptions(true);
                end
               else
                if More<>upper(target_info.shortname) then
                 Message1(option_target_is_already_set,target_info.shortname);
             end;

           'u' :
             if more <> '' then
               undef_system_macro(more);
           'U' :
             begin
               j:=1;
               while j<=length(more) do
                begin
                  case more[j] of
{$ifdef UNITALIASES}
                    'a' :
                       begin
                         AddUnitAlias(Copy(More,j+1,255));
                         break;
                       end;
{$endif UNITALIASES}
                    'n' :
                      exclude(init_settings.globalswitches,cs_check_unit_name);
                    'p' :
                       begin
                         Message2(option_obsolete_switch_use_new,'-Up','-Fu');
                         break;
                       end;
                    'r' :
                      do_release:=true;
                    's' :
                      include(init_settings.moduleswitches,cs_compilesystem);
                    '-' :
                      begin
                        exclude(init_settings.moduleswitches,cs_compilesystem);
                        exclude(init_settings.globalswitches,cs_check_unit_name);
                      end;
                    else
                      IllegalPara(opt);
                  end;
                  inc(j);
                end;
             end;

           'v' :
             begin
               if not setverbosity(More) then
                 IllegalPara(opt);
             end;

           'V' : ; { Ignore used by fpc }

           'W' :
             begin
               j:=1;
               while j<=length(More) do
                begin
                  case More[j] of
                    'A':
                      begin
                        if target_info.system in systems_all_windows then
                          begin
                            if UnsetBool(More, j) then
                              apptype:=app_cui
                            else
                              apptype:=app_native;
                          end
                        else
                          IllegalPara(opt);
                      end;
                    'b':
                      begin
                        if target_info.system in systems_darwin then
                          begin
                            if UnsetBool(More, j) then
                              apptype:=app_cui
                            else
                              apptype:=app_bundle
                          end
                        else
                          IllegalPara(opt);
                      end;
                    'B':
                      begin
                        if target_info.system in systems_all_windows+systems_symbian then
                          begin
                            {  -WB200000 means set trefered base address
                              to $200000, but does not change relocsection boolean
                              this way we can create both relocatble and
                              non relocatable DLL at a specific base address PM }
                            if (length(More)>j) then
                              begin
                                val('$'+Copy(More,j+1,255),imagebase,code);
                                if code<>0 then
                                  IllegalPara(opt);
                                ImageBaseSetExplicity:=true;
                              end
                            else
                              begin
                                RelocSection:=true;
                                RelocSectionSetExplicitly:=true;
                              end;
                            break;
                          end
                        else
                          IllegalPara(opt);
                      end;
                    'C':
                      begin
                        if target_info.system in systems_all_windows+systems_os2+systems_macos then
                          begin
                            if UnsetBool(More, j) then
                              apptype:=app_gui
                            else
                              apptype:=app_cui;
                          end
                        else
                          IllegalPara(opt);
                      end;
                    'D':
                      begin
                        if target_info.system in systems_all_windows then
                          begin
                            UseDeffileForExports:=not UnsetBool(More, j);
                            UseDeffileForExportsSetExplicitly:=true;
                          end
                        else
                          IllegalPara(opt);
                      end;
                    'e':
                      begin
                        if (target_info.system in systems_darwin) then
                          begin
                            RegisterRes(res_macosx_ext_info,TWinLikeResourceFile);
                            set_target_res(res_ext);
                            target_info.resobjext:='.fpcres';
                          end
                        else
                          IllegalPara(opt);
                      end;
                    'F':
                      begin
                        if target_info.system in systems_os2 then
                          begin
                            if UnsetBool(More, j) then
                              apptype:=app_cui
                            else
                              apptype:=app_fs;
                          end
                        else
                          IllegalPara(opt);
                      end;
                    'G':
                      begin
                        if target_info.system in systems_all_windows+systems_os2+systems_macos then
                          begin
                            if UnsetBool(More, j) then
                              apptype:=app_cui
                            else
                              apptype:=app_gui;
                          end
                        else
                          IllegalPara(opt);
                      end;
                    'I':
                      begin
                        if target_info.system in systems_all_windows then
                          begin
                            GenerateImportSection:=not UnsetBool(More,j);
                            GenerateImportSectionSetExplicitly:=true;
                          end
                        else
                          IllegalPara(opt);
                      end;
                    'i':
                      begin
                        if (target_info.system in systems_darwin) then
                          begin
                            set_target_res(res_macho);
                            target_info.resobjext:=
                              targetinfos[target_info.system]^.resobjext;
                          end
                        else
                          IllegalPara(opt);
                      end;
                    'M':
                      begin
                        if (target_info.system in (systems_darwin-[system_i386_iphonesim])) and
                           ParseMacVersionMin(MacOSXVersionMin,iPhoneOSVersionMin,'MAC_OS_X_VERSION_MIN_REQUIRED',copy(More,2,255),false) then
                          begin
                            break;
                          end
                        else
                          IllegalPara(opt);
                      end;
                    'N':
                      begin
                        if target_info.system in systems_all_windows then
                          begin
                            RelocSection:=UnsetBool(More,j);
                            RelocSectionSetExplicitly:=true;
                          end
                        else
                          IllegalPara(opt);
                      end;
                    'p':
                      begin
{$if defined(arm) or defined(avr)}
                        if (target_info.system in systems_embedded) then
                          begin
                            s:=upper(copy(more,j+1,length(more)-j));
                            if not(SetControllerType(s,init_settings.controllertype)) then
                              IllegalPara(opt);
                            break;
                          end
                        else
{$endif defined(arm) or defined(avr)}
                          IllegalPara(opt);
                      end;
                    'P':
                      begin
                        if (target_info.system in [system_i386_iphonesim,system_arm_darwin]) and
                           ParseMacVersionMin(iPhoneOSVersionMin,MacOSXVersionMin,'IPHONE_OS_VERSION_MIN_REQUIRED',copy(More,2,255),true) then
                          begin
                            break;
                          end
                        else
                          IllegalPara(opt);
                      end;
                    'R':
                      begin
                        if target_info.system in systems_all_windows then
                          begin
                            { support -WR+ / -WR- as synonyms to -WR / -WN }
                            RelocSection:=not UnsetBool(More,j);
                            RelocSectionSetExplicitly:=true;
                          end
                        else
                          IllegalPara(opt);
                      end;
                    'T':
                      begin
                        if target_info.system in systems_macos then
                          begin
                            if UnsetBool(More, j) then
                              apptype:=app_cui
                            else
                              apptype:=app_tool;
                          end
                        else
                          IllegalPara(opt);
                      end;
                    'X':
                      begin
                        if (target_info.system in systems_linux) then
                          begin
                            if UnsetBool(More, j) then
                              exclude(init_settings.moduleswitches,cs_executable_stack)
                            else
                              include(init_settings.moduleswitches,cs_executable_stack)
                          end
                        else
                          IllegalPara(opt);
                      end
                    else
                      IllegalPara(opt);
                  end;
                  inc(j);
                end;
             end;

           'X' :
             begin
               j:=1;
               while j<=length(more) do
                begin
                  case More[j] of
                    'c' : Cshared:=TRUE;
                    'd' : Dontlinkstdlibpath:=TRUE;
                    'e' :
                      begin
                        If UnsetBool(More, j) then
                          exclude(init_settings.globalswitches,cs_link_extern)
                        else
                          include(init_settings.globalswitches,cs_link_extern);
                      end;
                    'f' :
                      include(init_settings.globalswitches,cs_link_pthread);
                    'g' :
                      begin
                        If UnsetBool(More, j) then
                          exclude(init_settings.globalswitches,cs_link_separate_dbg_file)
                        else
                          include(init_settings.globalswitches,cs_link_separate_dbg_file);
                      end;
                    'i' :
                      begin
                        If UnsetBool(More, j) then
                          include(init_settings.globalswitches,cs_link_extern)
                        else
                          exclude(init_settings.globalswitches,cs_link_extern);
                      end;
                    'n' :
                      begin
                        If UnsetBool(More, j) then
                          exclude(init_settings.globalswitches,cs_link_native)
                        else
                          include(init_settings.globalswitches,cs_link_native);
                      end;

                    'm' :
                      begin
                        If UnsetBool(More, j) then
                          exclude(init_settings.globalswitches,cs_link_map)
                        else
                          include(init_settings.globalswitches,cs_link_map);
                      end;
                    'p' : ; { Ignore used by fpc.pp }
                    'r' :
                      begin
                        if (target_info.system in suppported_targets_x_smallr) then
                          begin
                            rlinkpath:=Copy(more,2,length(More)-1);
                            DefaultReplacements(rlinkpath);
                          end
                        else
                          IgnoredPara('-Xr');
                        more:='';
                      end;
                    'R' :
                      begin
                        sysrootpath:=copy(more,2,length(more)-1);
                        defaultreplacements(sysrootpath);
                        more:='';
                      end;
                    's' :
                      begin
                        If UnsetBool(More, j) then
                          exclude(init_settings.globalswitches,cs_link_strip)
                        else
                          include(init_settings.globalswitches,cs_link_strip);
                      end;
                    't' :
                      include(init_settings.globalswitches,cs_link_staticflag);
                    'v' :
                      begin
                        If UnsetBool(More, j) then
                          exclude(init_settings.globalswitches,cs_link_opt_vtable)
                        else
                          include(init_settings.globalswitches,cs_link_opt_vtable);
                      end;
                    'D' :
                      begin
                        def_system_macro('FPC_LINK_DYNAMIC');
                        undef_system_macro('FPC_LINK_SMART');
                        undef_system_macro('FPC_LINK_STATIC');
                        exclude(init_settings.globalswitches,cs_link_static);
                        exclude(init_settings.globalswitches,cs_link_smart);
                        include(init_settings.globalswitches,cs_link_shared);
                        LinkTypeSetExplicitly:=true;
                      end;
                    'M' :
                      begin
                        mainaliasname:=Copy(more,2,length(More)-1);
                        More:='';
                      end;
                    'P' :
                      begin
                        utilsprefix:=Copy(more,2,length(More)-1);
                        DefaultReplacements(utilsprefix);
                        More:='';
                      end;
                    'L' : begin  // -XLO is link order -XLA is link alias. -XLD avoids load defaults.
                                 // these are not aggregable.
                            if (j=length(more)) or not (more[j+1] in ['O','A','D']) then
                              IllegalPara(opt)
                            else
                              begin
                                case more[j+1] of
                                 'A' : begin
                                        s:=Copy(more,3,length(More)-2);
                                        if not LinkLibraryAliases.AddDep(s) Then
                                           IllegalPara(opt);
                                       end;
                                 'O' : begin
                                        s:=Copy(more,3,length(More)-2);
                                        if not LinkLibraryOrder.AddWeight(s) Then
                                           IllegalPara(opt);
                                       end;
                                 'D' : include(init_settings.globalswitches,cs_link_no_default_lib_order)
                                else
                                  IllegalPara(opt);
                                 end; {case}
                                j:=length(more);
                              end; {else begin}
                          end;
                    'S' :
                      begin
                        ForceStaticLinking;
                      end;
                    'X' :
                      begin
                        def_system_macro('FPC_LINK_SMART');
                        undef_system_macro('FPC_LINK_STATIC');
                        undef_system_macro('FPC_LINK_DYNAMIC');
                        exclude(init_settings.globalswitches,cs_link_static);
                        include(init_settings.globalswitches,cs_link_smart);
                        exclude(init_settings.globalswitches,cs_link_shared);
                        LinkTypeSetExplicitly:=true;
                      end;
                    '-' :
                      begin
                        exclude(init_settings.globalswitches,cs_link_staticflag);
                        exclude(init_settings.globalswitches,cs_link_strip);
                        exclude(init_settings.globalswitches,cs_link_map);
                        set_default_link_type;
                      end;
                    else
                      IllegalPara(opt);
                  end;
                  inc(j);
                end;
             end;
           else
             IllegalPara(opt);
         end;
       end;

    '@' :
      begin
        Message(option_no_nested_response_file);
        StopOptions(1);
      end;

    else
      begin
        if (length(param_file)<>0) then
          Message2(option_only_one_source_support,param_file,opt);
        param_file:=opt;
        Message1(option_found_file,opt);
      end;
  end;
end;


procedure Toption.Interpret_file(const filename : TPathStr);

  procedure RemoveSep(var fn:TPathStr);
  var
    i : longint;
  begin
    i:=0;
    while (i<length(fn)) and (fn[i+1] in [',',' ',#9]) do
      inc(i);
    Delete(fn,1,i);
    i:=length(fn);
    while (i>0) and (fn[i] in [',',' ',#9]) do
      dec(i);
    fn:=copy(fn,1,i);
  end;

  function GetName(var fn:TPathStr):TPathStr;
  var
    i : longint;
  begin
    i:=0;
    while (i<length(fn)) and (fn[i+1] in ['a'..'z','A'..'Z','0'..'9','_','-']) do
     inc(i);
    GetName:=Copy(fn,1,i);
    Delete(fn,1,i);
  end;

const
  maxlevel = 15;
var
  f     : text;
  s, tmp,
  opts  : TCmdStr;
  skip  : array[0..maxlevel] of boolean;
  line,
  level : longint;
  option_read : boolean;
begin
{ avoid infinite loop }
  Inc(FileLevel);
  Option_read:=false;
  If FileLevel>MaxLevel then
   Message(option_too_many_cfg_files);
{ Maybe It's Directory ?}   //Jaro Change:
  if PathExists(filename,false) then
    begin
       Message1(option_config_is_dir,filename);
       exit;
    end;
{ open file }
  Message1(option_using_file,filename);
  assign(f,ExpandFileName(filename));
  {$push}{$I-}
   reset(f);
  {$pop}
  if ioresult<>0 then
   begin
     Message1(option_unable_open_file,filename);
     exit;
   end;
  Message1(option_start_reading_configfile,filename);
  fillchar(skip,sizeof(skip),0);
  level:=0;
  line:=0;
  while not eof(f) do
   begin
     readln(f,opts);
     inc(line);
     RemoveSep(opts);
     if (opts<>'') and (opts[1]<>';') then
      begin
        if opts[1]='#' then
         begin
           Message1(option_interpreting_file_option,opts);
           Delete(opts,1,1);
           s:=upper(GetName(opts));
           if (s='SECTION') then
            begin
              RemoveSep(opts);
              s:=upper(GetName(opts));
              if level=0 then
               skip[level]:=not defined_macro(s) or (s='COMMON');
            end
           else
            if (s='IFDEF') then
             begin
               RemoveSep(opts);
               if Level>=maxlevel then
                begin
                  Message2(option_too_many_ifdef,filename,tostr(line));
                  stopOptions(1);
                end;
               inc(Level);
               skip[level]:=(skip[level-1] or not defined_macro(upper(GetName(opts))));
             end
           else
            if (s='IFNDEF') then
             begin
               RemoveSep(opts);
               if Level>=maxlevel then
                begin
                  Message2(option_too_many_ifdef,filename,tostr(line));
                  stopOptions(1);
                end;
               inc(Level);
               skip[level]:=(skip[level-1] or defined_macro(upper(GetName(opts))));
             end
           else
            if (s='ELSE') then
              begin
                if Level=0 then
                  begin
                    Message2(option_else_without_if,filename,tostr(line));
                    stopOptions(1);
                  end
                else
                  skip[level]:=skip[level-1] or (not skip[level])
              end
           else
            if (s='ENDIF') then
             begin
               skip[level]:=false;
               if Level=0 then
                begin
                  Message2(option_too_many_endif,filename,tostr(line));
                  stopOptions(1);
                end;
               dec(level);
             end
           else
            if (not skip[level]) then
             begin
               if (s='DEFINE') then
                begin
                  RemoveSep(opts);
                  tmp:= GetName(opts);
                  if tmp <> '' then
                    def_system_macro(tmp);
                  Option_read:=true;
                end
              else
               if (s='UNDEF') then
                begin
                  RemoveSep(opts);
                  tmp:= GetName(opts);
                  if tmp <> '' then
                    undef_system_macro(tmp);
                  Option_read:=true;
                end
              else
               if (s='WRITE') then
                begin
                  Delete(opts,1,1);
                  WriteLn(opts);
                  Option_read:=true;
                end
              else
               if (s='INCLUDE') then
                begin
                  Delete(opts,1,1);
                  Interpret_file(opts);
                  Option_read:=true;
                end;
            end;
         end
        else
         begin
           if (opts[1]='-') or (opts[1]='@') then
            begin
              if (not skip[level]) then
                interpret_option(opts,false);
              Option_read:=true;
            end
           else
             Message1(option_illegal_para,opts);
         end;
      end;
   end;
  if Level>0 then
   Message(option_too_less_endif);
  if Not Option_read then
    Message1(option_no_option_found,filename)
  else
    Message1(option_end_reading_configfile,filename);
  Close(f);
  Dec(FileLevel);
end;


procedure Toption.Interpret_envvar(const envname : TCmdStr);
var
  argstart,
  env,
  pc     : pchar;
  arglen : longint;
  quote  : set of char;
  hs     : TCmdStr;
begin
  Message1(option_using_env,envname);
  env:=GetEnvPChar(envname);
  pc:=env;
  if assigned(pc) then
   begin
     repeat
       { skip leading spaces }
       while pc^ in [' ',#9,#13] do
        inc(pc);
       case pc^ of
         #0 :
           break;
         '"' :
           begin
             quote:=['"'];
             inc(pc);
           end;
         '''' :
           begin
              quote:=[''''];
              inc(pc);
           end;
         else
           quote:=[' ',#9,#13];
       end;
     { scan until the end of the argument }
       argstart:=pc;
       while (pc^<>#0) and not(pc^ in quote) do
        inc(pc);
     { create argument }
       arglen:=pc-argstart;
{ TODO: FIXME: silent truncation of environment parameters }
       if (arglen > 255) then
         arglen := 255;
       setlength(hs,arglen);
       move(argstart^,hs[1],arglen);
       interpret_option(hs,true);
     { skip quote }
       if pc^ in quote then
        inc(pc);
     until false;
   end
  else
   Message1(option_no_option_found,'(env) '+envname);
  FreeEnvPChar(env);
end;


procedure toption.read_parameters;
var
  opts       : TCmdStr;
  paramindex : longint;
begin
  paramindex:=0;
  while paramindex<paramcount do
   begin
     inc(paramindex);
     opts:=objpas.paramstr(paramindex);
     if length(opts)>0 then
       case opts[1] of
         '@' :
           if not firstpass then
           begin
             Delete(opts,1,1);
             Message1(option_reading_further_from,opts);
             interpret_file(opts);
           end;
         '!' :
           if not firstpass then
           begin
             Delete(opts,1,1);
             Message1(option_reading_further_from,'(env) '+opts);
             interpret_envvar(opts);
           end;
         else
           interpret_option(opts,true);
       end;
   end;
end;


procedure toption.parsecmd(cmd:TCmdStr);
var
  i,ps  : longint;
  opts  : TCmdStr;
begin
  while (cmd<>'') do
   begin
     while cmd[1]=' ' do
      delete(cmd,1,1);
     i:=pos(' ',cmd);
     if i=0 then
       i:=2147483647;
     opts:=Copy(cmd,1,i-1);
     Delete(cmd,1,i);
     case opts[1] of
       '@' :
         if not firstpass then
         begin
           Delete(opts,1,1);
           Message1(option_reading_further_from,opts);
           interpret_file(opts);
         end;
       '!' :
         if not firstpass then
         begin
           Delete(opts,1,1);
           Message1(option_reading_further_from,'(env) '+opts);
           interpret_envvar(opts);
         end;
       '"' :
         begin
           Delete(opts,1,1);
           ps:=pos('"',cmd);
           if (i<>256) and (ps>0) then
             begin
               opts:=opts + ' '+ copy(cmd,1,ps-1);
               cmd:=copy(cmd,ps+1,255);
             end;
           interpret_option(opts,true);
         end;
       else
         interpret_option(opts,true);
     end;
   end;
end;


procedure toption.writequickinfo;
var
  s : string;
  i : longint;

  procedure addinfo(const hs:string);
  begin
    if s<>'' then
     s:=s+' '+hs
    else
     s:=hs;
  end;

begin
  s:='';
  i:=0;
  while (i<length(quickinfo)) do
   begin
     inc(i);
     case quickinfo[i] of
      'S' :
        begin
          inc(i);
          case quickinfo[i] of
           'O' :
             addinfo(lower(source_info.shortname));
           'P' :
             addinfo(source_cpu_string);
           else
             IllegalPara('-i'+QuickInfo);
          end;
        end;
      'T' :
        begin
          inc(i);
          case quickinfo[i] of
           'O' :
             addinfo(lower(target_info.shortname));
           'P' :
             AddInfo(target_cpu_string);
           else
             IllegalPara('-i'+QuickInfo);
          end;
        end;
      'V' :
        AddInfo(version_string);
      'W' :
        AddInfo(full_version_string);
      'D' :
        AddInfo(date_string);
      '_' :
        ;
      else
        IllegalPara('-i'+QuickInfo);
    end;
  end;
  if s<>'' then
   begin
     writeln(s);
     stopoptions(0);
   end;
end;


procedure TOption.TargetOptions(def:boolean);
var
  s : string;
  i : integer;
  target_unsup_features : tfeatures;
begin
  if def then
   def_system_macro(target_info.shortname)
  else
   undef_system_macro(target_info.shortname);

  s:=target_info.extradefines;
  while (s<>'') do
   begin
     i:=pos(';',s);
     if i=0 then
      i:=length(s)+1;
     if def then
      def_system_macro(Copy(s,1,i-1))
     else
      undef_system_macro(Copy(s,1,i-1));
     delete(s,1,i);
   end;

  if (tf_winlikewidestring in target_info.flags) then
    if def then
      def_system_macro('FPC_WINLIKEWIDESTRING')
    else
      undef_system_macro('FPC_WINLIKEWIDESTRING');

  if (tf_requires_proper_alignment in target_info.flags) then
    if def then
      def_system_macro('FPC_REQUIRES_PROPER_ALIGNMENT')
    else
      undef_system_macro('FPC_REQUIRES_PROPER_ALIGNMENT');

  if source_info.system<>target_info.system then
    if def then
      def_system_macro('FPC_CROSSCOMPILING')
    else
      undef_system_macro('FPC_CROSSCOMPILING');

  if source_info.cpu<>target_info.cpu then
    if def then
      def_system_macro('FPC_CPUCROSSCOMPILING')
    else
      def_system_macro('FPC_CPUCROSSCOMPILING');

  if (tf_no_generic_stackcheck in target_info.flags) then
    if def then
      def_system_macro('FPC_NO_GENERIC_STACK_CHECK')
    else
      undef_system_macro('FPC_NO_GENERIC_STACK_CHECK');

  if (tf_section_threadvars in target_info.flags) then
    if def then
      def_system_macro('FPC_SECTION_THREADVARS')
    else
      undef_system_macro('FPC_SECTION_THREADVARS');

  { Code generation flags }
  if def and
     (tf_pic_default in target_info.flags) then
    include(init_settings.moduleswitches,cs_create_pic)
  else
    exclude(init_settings.moduleswitches,cs_create_pic);

  { Resources support }
  if (tf_has_winlike_resources in target_info.flags) then
    if def then
      def_system_macro('FPC_HAS_WINLIKERESOURCES')
    else
      undef_system_macro('FPC_HAS_WINLIKERESOURCES');

  { Features }
  case target_info.system of
    system_arm_gba:
      target_unsup_features:=[f_dynlibs];
    system_arm_nds:
      target_unsup_features:=[f_threading,f_commandargs,f_fileio,f_textio,f_consoleio,f_dynlibs];
    system_i386_nativent:
      // until these features are implemented, they are disabled in the compiler
      target_unsup_features:=[f_stackcheck];
    system_jvm_java32,
    system_jvm_android32:
      target_unsup_features:=[f_heap,f_textio,f_consoleio,f_fileio,
         f_variants,f_objects,f_threading,f_commandargs,
         f_processes,f_stackcheck,f_dynlibs,f_softfpu,f_objectivec1,f_resources];
    else
      target_unsup_features:=[];
  end;
  if def then
    features:=features-target_unsup_features
  else
    features:=features+target_unsup_features;
end;

procedure TOption.checkoptionscompatibility;
begin
  if (paratargetdbg in [dbg_dwarf2,dbg_dwarf3]) and
     not(target_info.system in systems_darwin) then
    begin
      { smartlink creation does not yet work with DWARF
        debug info on most targets, but it works in internal assembler }
      if (cs_create_smart in init_settings.moduleswitches) and
         not (af_outputbinary in target_asm.flags) then
        begin
          Message(option_dwarf_smartlink_creation);
          exclude(init_settings.moduleswitches,cs_create_smart);
        end;

      { smart linking does not yet work with DWARF debug info on most targets }
      if (cs_link_smart in init_settings.globalswitches) then
        begin
          Message(option_dwarf_smart_linking);
          ForceStaticLinking;
        end;
    end;

  { external debug info is only supported for DWARF on darwin }
  if (target_info.system in systems_darwin) and
     (cs_link_separate_dbg_file in init_settings.globalswitches) and
     not(paratargetdbg in [dbg_dwarf2,dbg_dwarf3]) then
    begin
      Message(option_debug_external_unsupported);
      exclude(init_settings.globalswitches,cs_link_separate_dbg_file);
    end;
end;


constructor TOption.create;
begin
  LogoWritten:=false;
  NoPressEnter:=false;
  FirstPass:=false;
  FPUSetExplicitly:=false;
  CPUSetExplicitly:=false;
  OptCPUSetExplicitly:=false;
  FileLevel:=0;
  Quickinfo:='';
  ParaIncludePath:=TSearchPathList.Create;
  ParaObjectPath:=TSearchPathList.Create;
  ParaUnitPath:=TSearchPathList.Create;
  ParaLibraryPath:=TSearchPathList.Create;
  ParaFrameworkPath:=TSearchPathList.Create;
  FillChar(ParaAlignment,sizeof(ParaAlignment),0);
  MacVersionSet:=false;
end;


destructor TOption.destroy;
begin
  ParaIncludePath.Free;
  ParaObjectPath.Free;
  ParaUnitPath.Free;
  ParaLibraryPath.Free;
  ParaFrameworkPath.Free;
end;


{****************************************************************************
                              Callable Routines
****************************************************************************}

function check_configfile(const fn:string;var foundfn:string):boolean;

  function CfgFileExists(const fn:string):boolean;
  begin
    Comment(V_Tried,'Configfile search: '+fn);
    CfgFileExists:=FileExists(fn);
  end;

var
{$ifdef Unix}
  hs,
{$endif Unix}
  configpath : string;
begin
  foundfn:=fn;
  check_configfile:=true;
  { retrieve configpath }
  configpath:=FixPath(GetEnvironmentVariable('PPC_CONFIG_PATH'),false);
{$ifdef Unix}
  if configpath='' then
   configpath:=ExpandFileName(FixPath(exepath+'../etc/',false));
{$endif}
  {
    Order to read configuration file :
    try reading fpc.cfg in :
     1 - current dir
     2 - configpath
     3 - compiler path
  }
  if not FileExists(fn) then
   begin
{$ifdef Unix}
     hs:=GetEnvironmentVariable('HOME');
     if (hs<>'') and CfgFileExists(FixPath(hs,false)+'.'+fn) then
      foundfn:=FixPath(hs,false)+'.'+fn
     else
{$endif}
      if CfgFileExists(configpath+fn) then
       foundfn:=configpath+fn
     else
{$ifdef WINDOWS}
       if (GetEnvironmentVariable('USERPROFILE')<>'') and CfgFileExists(FixPath(GetEnvironmentVariable('USERPROFILE'),false)+fn) then
         foundfn:=FixPath(GetEnvironmentVariable('USERPROFILE'),false)+fn
     else
       if (GetEnvironmentVariable('ALLUSERSPROFILE')<>'') and CfgFileExists(FixPath(GetEnvironmentVariable('ALLUSERSPROFILE'),false)+fn) then
         foundfn:=FixPath(GetEnvironmentVariable('ALLUSERSPROFILE'),false)+fn
     else
{$endif WINDOWS}
{$ifndef Unix}
      if CfgFileExists(exepath+fn) then
       foundfn:=exepath+fn
     else
{$else}
      if CfgFileExists('/etc/'+fn) then
       foundfn:='/etc/'+fn
     else
{$endif}
      check_configfile:=false;
   end;
end;


procedure read_arguments(cmd:TCmdStr);
var
  env: ansistring;
  i : tfeature;
  abi : tabi;
begin
  option:=coption.create;
  disable_configfile:=false;

  { Non-core target defines }
  Option.TargetOptions(true);

{ get default messagefile }
  msgfilename:=GetEnvironmentVariable('PPC_ERROR_FILE');

{ default configfile can be specified on the commandline,
   remove it first }
  if (cmd<>'') and (cmd[1]='[') then
    begin
      ppccfg:=Copy(cmd,2,pos(']',cmd)-2);
      Delete(cmd,1,pos(']',cmd));
    end
  else
    ppccfg:='fpc.cfg';

{ first pass reading of parameters, only -i -v -T etc.}
  option.firstpass:=true;
  if cmd<>'' then
    option.parsecmd(cmd)
  else
    begin
      option.read_parameters;
      { Write only quickinfo }
      if option.quickinfo<>'' then
        option.writequickinfo;
    end;
  option.firstpass:=false;

  { redefine target options so all defines are written even if no -Txxx is passed on the command line }
  Option.TargetOptions(true);

{ target is set here, for wince the default app type is gui }
  if target_info.system in systems_wince then
    apptype:=app_gui;

{ default defines }
  def_system_macro(target_info.shortname);
  def_system_macro('FPC');
  def_system_macro('VER'+version_nr);
  def_system_macro('VER'+version_nr+'_'+release_nr);
  def_system_macro('VER'+version_nr+'_'+release_nr+'_'+patch_nr);

{ Temporary defines, until things settle down }
  def_system_macro('RESSTRSECTIONS');
  def_system_macro('FPC_HASFIXED64BITVARIANT');
  def_system_macro('FPC_HASINTERNALOLEVARIANT2VARIANTCAST');
  def_system_macro('FPC_HAS_VARSETS');
  def_system_macro('FPC_HAS_VALGRINDBOOL');
  def_system_macro('FPC_HAS_STR_CURRENCY');
  def_system_macro('FPC_REAL2REAL_FIXED');
  def_system_macro('FPC_STRTOCHARARRAYPROC');
  def_system_macro('FPC_STRTOSHORTSTRINGPROC');
  def_system_macro('FPC_OBJFPC_EXTENDED_IF');
  def_system_macro('FPC_HAS_OPERATOR_ENUMERATOR');
  def_system_macro('FPC_HAS_CONSTREF');
  def_system_macro('FPC_STATICRIPFIXED');
  def_system_macro('FPC_VARIANTCOPY_FIXED');
  def_system_macro('FPC_DYNARRAYCOPY_FIXED');
{$if defined(x86) or defined(powerpc) or defined(powerpc64)}
  def_system_macro('FPC_HAS_INTERNAL_ABS_LONG');
{$endif}
  def_system_macro('FPC_HAS_UNICODESTRING');
  def_system_macro('FPC_RTTI_PACKSET1');
  def_system_macro('FPC_HAS_CPSTRING');
{$ifdef x86_64}
  def_system_macro('FPC_HAS_RIP_RELATIVE');
{$endif x86_64}
  def_system_macro('FPC_HAS_CEXTENDED');
  def_system_macro('FPC_HAS_RESSTRINITS');

{ these cpus have an inline rol/ror implementaion }
{$ifdef cpurox}
  def_system_macro('FPC_HAS_INTERNAL_ROX');
{$endif}

{ these cpus have an inline sar implementaion }
{ currently, all supported CPUs have an internal sar implementation }
{ $if defined(x86) or defined(arm) or defined(powerpc) or defined(powerpc64) or defined(sparc) or defined(mips) or defined(mipsel)}
  def_system_macro('FPC_HAS_INTERNAL_SAR');
{ $endif}

{ inline bsf/bsr implementation }
{$if defined(x86) or defined(x86_64)}
  def_system_macro('FPC_HAS_INTERNAL_BSX');
{$endif}

{$ifdef powerpc64}
  def_system_macro('FPC_HAS_LWSYNC');
{$endif}
  def_system_macro('FPC_HAS_MEMBAR');
  def_system_macro('FPC_SETBASE_USED');

{$if defined(x86) or defined(arm) or defined(jvm)}
  def_system_macro('INTERNAL_BACKTRACE');
{$endif}
  def_system_macro('STR_CONCAT_PROCS');
{$warnings off}
  if pocall_default = pocall_register then
    def_system_macro('REGCALL');
{$warnings on}
  { don't remove this, it's also for fpdoc necessary (FK) }
  def_system_macro('FPC_HAS_FEATURE_SUPPORT');
{ using a case is pretty useless here (FK) }
{ some stuff for TP compatibility }
{$ifdef i386}
  def_system_macro('CPU86');
  def_system_macro('CPU87');
  def_system_macro('CPU386');
{$endif}

{ new processor stuff }
{$ifdef i386}
  def_system_macro('CPUI386');
  def_system_macro('CPU32');
  def_system_macro('CPUX86');
  def_system_macro('FPC_HAS_TYPE_EXTENDED');
  def_system_macro('FPC_HAS_TYPE_DOUBLE');
  def_system_macro('FPC_HAS_TYPE_SINGLE');
{$endif}
{$ifdef m68k}
  def_system_macro('CPU68');
  def_system_macro('CPU68K');
  def_system_macro('CPUM68K');
  def_system_macro('CPU32');
  def_system_macro('FPC_CURRENCY_IS_INT64');
  def_system_macro('FPC_COMP_IS_INT64');
{$endif}
{$ifdef ALPHA}
  def_system_macro('CPUALPHA');
  def_system_macro('CPU64');
{$endif}
{$ifdef powerpc}
  def_system_macro('CPUPOWERPC');
  def_system_macro('CPUPOWERPC32');
  def_system_macro('CPU32');
  def_system_macro('FPC_CURRENCY_IS_INT64');
  def_system_macro('FPC_COMP_IS_INT64');
{$endif}
{$ifdef POWERPC64}
  def_system_macro('CPUPOWERPC');
  def_system_macro('CPUPOWERPC64');
  def_system_macro('CPU64');
  def_system_macro('FPC_CURRENCY_IS_INT64');
  def_system_macro('FPC_COMP_IS_INT64');
{$endif}
{$ifdef iA64}
  def_system_macro('CPUIA64');
  def_system_macro('CPU64');
{$endif}
{$ifdef x86_64}
  def_system_macro('CPUX86_64');
  def_system_macro('CPUAMD64');
  def_system_macro('CPU64');
  def_system_macro('CPUX64');
  { not supported for now, afaik (FK)
   def_system_macro('FPC_HAS_TYPE_FLOAT128'); }
  { win64 doesn't support the legacy fpu }
  if target_info.system=system_x86_64_win64 then
    begin
      def_system_macro('FPC_CURRENCY_IS_INT64');
      def_system_macro('FPC_COMP_IS_INT64');
    end;
{$endif}
{$ifdef sparc}
  def_system_macro('CPUSPARC');
  def_system_macro('CPUSPARC32');
  def_system_macro('CPU32');
  def_system_macro('FPC_CURRENCY_IS_INT64');
  def_system_macro('FPC_COMP_IS_INT64');
{$endif}
{$ifdef vis}
  def_system_macro('CPUVIS');
  def_system_macro('CPU32');
{$endif}
{$ifdef arm}
  def_system_macro('CPUARM');
  def_system_macro('CPU32');
  def_system_macro('FPC_CURRENCY_IS_INT64');
  def_system_macro('FPC_COMP_IS_INT64');
{$endif arm}
{$ifdef avr}
  def_system_macro('CPUAVR');
  def_system_macro('CPU16');
  def_system_macro('FPC_CURRENCY_IS_INT64');
  def_system_macro('FPC_COMP_IS_INT64');
{$endif avr}
{$ifdef jvm}
  def_system_macro('CPUJVM');
  def_system_macro('CPU32');
  def_system_macro('FPC_CURRENCY_IS_INT64');
  def_system_macro('FPC_COMP_IS_INT64');
{$endif jvm}

{$ifdef mips}

// HIGHLY TENTATIVE, from David Zhang's options.pas. MarkMLl.

  def_system_macro('CPUMIPS');
  def_system_macro('CPUMIPS32');
  def_system_macro('CPU32');
//  def_system_macro('FPC_HAS_TYPE_DOUBLE');
//  def_system_macro('FPC_HAS_TYPE_SINGLE');
//  def_system_macro('FPC_INCLUDE_SOFTWARE_INT64_TO_DOUBLE');
  def_system_macro('FPC_CURRENCY_IS_INT64');
  def_system_macro('FPC_COMP_IS_INT64');
//  def_system_macro('FPC_REQUIRES_PROPER_ALIGNMENT');
{$endif}

  { read configuration file }
  if (not disable_configfile) and
     (ppccfg<>'') then
    read_configfile:=check_configfile(ppccfg,ppccfg)
  else
    read_configfile := false;

{ Read commandline and configfile }
  param_file:='';

  { read configfile }
  if read_configfile then
    option.interpret_file(ppccfg);

  { read parameters again to override config file }
  if cmd<>'' then
    option.parsecmd(cmd)
  else
    begin
      { Write help pages if no parameters are passed }
      if (paramcount=0) then
        Option.WriteHelpPages;
      option.read_parameters;
      { Write only quickinfo }
      if option.quickinfo<>'' then
        option.writequickinfo;
    end;

  { check the compatibility of different options and adjust them if necessary
    (and print possible errors)
  }
  option.checkoptionscompatibility;

  { Stop if errors in options }
  if ErrorCount>0 then
   StopOptions(1);

  { endian define }
  case target_info.endian of
    endian_little :
      begin
        def_system_macro('ENDIAN_LITTLE');
        def_system_macro('FPC_LITTLE_ENDIAN');
      end;
    endian_big :
      begin
        def_system_macro('ENDIAN_BIG');
        def_system_macro('FPC_BIG_ENDIAN');
      end;
  end;

  { define abi }
  for abi:=low(tabi) to high(tabi) do
    undef_system_macro('FPC_ABI_'+abi2str[abi]);
  def_system_macro('FPC_ABI_'+abi2str[target_info.abi]);

  { Define FPC_ABI_EABI in addition to FPC_ABI_EABIHF on EABI VFP hardfloat
    systems since most code needs to behave the same on both}
  if target_info.abi = abi_eabihf then
    def_system_macro('FPC_ABI_EABI');

  { Write logo }
  if option.ParaLogo then
    option.writelogo;

{ Check file to compile }
  if param_file='' then
   begin
     Message(option_no_source_found);
     StopOptions(1);
   end;
{$ifndef Unix}
  param_file:=FixFileName(param_file);
{$endif not unix}
  inputfilepath:=ExtractFilePath(param_file);
  inputfilename:=ExtractFileName(param_file);
  if ExtractFileExt(inputfilename)='' then
    begin
      if FileExists(inputfilepath+ChangeFileExt(inputfilename,sourceext)) then
        inputfilename:=ChangeFileExt(inputfilename,sourceext)
      else if FileExists(inputfilepath+ChangeFileExt(inputfilename,pasext)) then
        inputfilename:=ChangeFileExt(inputfilename,pasext)
      else if ((m_mac in current_settings.modeswitches) or
              (tf_p_ext_support in target_info.flags))
             and FileExists(inputfilepath+ChangeFileExt(inputfilename,pext)) then
        inputfilename:=ChangeFileExt(inputfilename,pext);
    end;

  { Check output dir }
  if (OutputExeDir<>'') and
     not PathExists(OutputExeDir,false) then
    begin
      Message1(general_e_path_does_not_exist,OutputExeDir);
      StopOptions(1);
    end;

  { Add paths specified with parameters to the searchpaths }
  UnitSearchPath.AddList(option.ParaUnitPath,true);
  ObjectSearchPath.AddList(option.ParaObjectPath,true);
  IncludeSearchPath.AddList(option.ParaIncludePath,true);
  LibrarySearchPath.AddList(option.ParaLibraryPath,true);
  FrameworkSearchPath.AddList(option.ParaFrameworkPath,true);

  { add unit environment and exepath to the unit search path }
  if inputfilepath<>'' then
   Unitsearchpath.AddPath(inputfilepath,true);
  if not disable_configfile then
    begin
      env:=GetEnvironmentVariable(target_info.unit_env);
      if env<>'' then
        UnitSearchPath.AddPath(GetEnvironmentVariable(target_info.unit_env),false);
    end;

{$ifdef Unix}
  fpcdir:=FixPath(GetEnvironmentVariable('FPCDIR'),false);
  if fpcdir='' then
    begin
      if PathExists('/usr/local/lib/fpc/'+version_string,true) then
        fpcdir:='/usr/local/lib/fpc/'+version_string+'/'
      else
        fpcdir:='/usr/lib/fpc/'+version_string+'/';
    end;
{$else unix}
  fpcdir:=FixPath(GetEnvironmentVariable('FPCDIR'),false);
  if fpcdir='' then
    begin
      fpcdir:=ExePath+'../';
      if not(PathExists(fpcdir+'units',true)) and
         not(PathExists(fpcdir+'rtl',true)) then
        fpcdir:=fpcdir+'../';
    end;
{$endif unix}
  { first try development RTL, else use the default installation path }
  if not disable_configfile then
    begin
      if PathExists(FpcDir+'rtl',true) then
        if tf_use_8_3 in Source_Info.Flags then
          UnitSearchPath.AddPath(FpcDir+'rtl/'+target_os_string,false)
        else
          UnitSearchPath.AddPath(FpcDir+'rtl/'+target_full_string,false)
      else
        if tf_use_8_3 in Source_Info.Flags then
          UnitSearchPath.AddPath(FpcDir+'units/'+target_os_string+'/rtl',false)
        else
          UnitSearchPath.AddPath(FpcDir+'units/'+target_full_string+'/rtl',false);
    end;
  { Add exepath if the exe is not in the current dir, because that is always searched already.
    Do not add it when linking on the target because then we can maybe already find
    .o files that are not for the target }
  if (ExePath<>GetCurrentDir) and
     not(cs_link_on_target in init_settings.globalswitches) then
   UnitSearchPath.AddPath(ExePath,false);
  { Add unit dir to the object and library path }
  objectsearchpath.AddList(unitsearchpath,false);
  librarysearchpath.AddList(unitsearchpath,false);

  { maybe override assembler }
  if (paratargetasm<>as_none) then
    begin
      if not set_target_asm(paratargetasm) then
        begin
          Message2(option_incompatible_asm,asminfos[paratargetasm]^.idtxt,target_info.name);
          set_target_asm(target_info.assemextern);
          Message1(option_asm_forced,target_asm.idtxt);
        end;
      if (af_no_debug in asminfos[paratargetasm]^.flags) and
         (paratargetdbg<>dbg_none) then
        begin
          Message1(option_confict_asm_debug,
            asminfos[paratargetasm]^.idtxt);
          paratargetdbg:=dbg_none;
          exclude(init_settings.moduleswitches,cs_debuginfo);
        end;
    end;
  {TOptionheck a second time as we might have changed assembler just above }
  option.checkoptionscompatibility;

  { maybe override debug info format }
  if (paratargetdbg<>dbg_none) then
    set_target_dbg(paratargetdbg);

  { switch assembler if it's binary and we got -a on the cmdline }
  if (cs_asm_leave in init_settings.globalswitches) and
     (af_outputbinary in target_asm.flags) then
   begin
     Message(option_switch_bin_to_src_assembler);
     set_target_asm(target_info.assemextern);
   end;

  { Force use of external linker if there is no
    internal linker or the linking is skipped }
  if not(cs_link_extern in init_settings.globalswitches) and
     (not assigned(target_info.link) or
      (cs_link_nolink in init_settings.globalswitches)) then
    include(init_settings.globalswitches,cs_link_extern);

  { turn off stripping if compiling with debuginfo or profile }
  if (
      (cs_debuginfo in init_settings.moduleswitches) or
      (cs_profile in init_settings.moduleswitches)
     ) and
     not(cs_link_separate_dbg_file in init_settings.globalswitches) then
    exclude(init_settings.globalswitches,cs_link_strip);

  { set Mac OS X version default macros if not specified explicitly }
  option.MaybeSetDefaultMacVersionMacro;

  { force fpu emulation on arm/wince, arm/gba, arm/embedded, arm/nds and
    arm/darwin if fpu type not explicitly set }
  if not(option.FPUSetExplicitly) and
     ((target_info.system in [system_arm_wince,system_arm_gba,system_m68k_amiga,
         system_m68k_linux,system_arm_nds,system_arm_embedded,system_arm_darwin])
{$ifdef arm}
      or (target_info.abi=abi_eabi)
{$endif arm}
     )
{$ifdef arm}
     or (init_settings.fputype=fpu_soft)
{$endif arm}
  then
    begin
{$ifdef cpufpemu}
      include(init_settings.moduleswitches,cs_fp_emulation);
      { cs_fp_emulation and fpu_soft are equal on arm }
      init_settings.fputype:=fpu_soft;
{$endif cpufpemu}
    end;

{$ifdef arm}
  if target_info.abi = abi_eabihf then
    begin
      if not(option.FPUSetExplicitly) then
        begin
          init_settings.fputype:=fpu_vfpv3_d16
        end
      else
        begin
          if not (init_settings.fputype in [fpu_vfpv2,fpu_vfpv3,fpu_vfpv3_d16]) then
            begin
              Message(option_illegal_fpu_eabihf);
              StopOptions(1);
            end;
        end;
    end;
{$endif arm}

{$ifdef arm}
{ set default cpu type to ARMv6 for Darwin unless specified otherwise }
if (target_info.system=system_arm_darwin) then
  begin
    if not option.CPUSetExplicitly then
      init_settings.cputype:=cpu_armv6;
    if not option.OptCPUSetExplicitly then
      init_settings.optimizecputype:=cpu_armv6;
  end;

{ set default cpu type to ARMv7 for ARMHF unless specified otherwise }
if (target_info.abi = abi_eabihf) then
  begin
    if not option.CPUSetExplicitly then
      init_settings.cputype:=cpu_armv7;
    if not option.OptCPUSetExplicitly then
      init_settings.optimizecputype:=cpu_armv7;
  end;
{$endif arm}

{$ifdef jvm}
  { set default CPU type to Dalvik when targeting Android }
  if target_info.system=system_jvm_android32 then
    begin
      if not option.CPUSetExplicitly then
        init_settings.cputype:=cpu_dalvik;
    end;
{$endif jvm}

  { now we can define cpu and fpu type }
  def_system_macro('CPU'+Cputypestr[init_settings.cputype]);

  def_system_macro('FPU'+fputypestr[init_settings.fputype]);

  if init_settings.fputype<>fpu_none then
    begin
{$if defined(i386)}
      def_system_macro('FPC_HAS_TYPE_EXTENDED');
{$endif}
      def_system_macro('FPC_HAS_TYPE_SINGLE');
      def_system_macro('FPC_HAS_TYPE_DOUBLE');
{$if not defined(i386) and not defined(x86_64)}
      def_system_macro('FPC_INCLUDE_SOFTWARE_INT64_TO_DOUBLE');
{$endif}
{$ifdef x86_64}
      { win64 doesn't support the legacy fpu }
      if target_info.system=system_x86_64_win64 then
        undef_system_macro('FPC_HAS_TYPE_EXTENDED')
      else
        def_system_macro('FPC_HAS_TYPE_EXTENDED');
{$endif}
    end;
    { Enable now for testing }
{$ifndef DISABLE_TLS_DIRECTORY}
    if target_info.system in systems_windows then
      def_system_macro('FPC_USE_TLS_DIRECTORY');
{$endif not DISABLE_TLS_DIRECTORY}

{$ifdef TEST_WIN64_SEH}
    if target_info.system=system_x86_64_win64 then
      def_system_macro('FPC_USE_WIN64_SEH');
{$endif TEST_WIN64_SEH}

{$ifdef ARM}
  { define FPC_DOUBLE_HILO_SWAPPED if needed to properly handle doubles in RTL }
  if (init_settings.fputype in [fpu_fpa,fpu_fpa10,fpu_fpa11]) and
    not(cs_fp_emulation in init_settings.moduleswitches) then
    def_system_macro('FPC_DOUBLE_HILO_SWAPPED');
{$endif ARM}

  { Section smartlinking conflicts with import sections on Windows }
  if GenerateImportSection and
     (target_info.system in [system_i386_win32,system_x86_64_win64]) then
    exclude(target_info.flags,tf_smartlink_sections);

  if not LinkTypeSetExplicitly then
    set_default_link_type;

  { Default alignment settings,
    1. load the defaults for the target
    2. override with generic optimizer setting (little size)
    3. override with the user specified -Oa }
  UpdateAlignment(init_settings.alignment,target_info.alignment);
  if (cs_opt_size in current_settings.optimizerswitches) then
   begin
     init_settings.alignment.procalign:=1;
     init_settings.alignment.jumpalign:=1;
     init_settings.alignment.loopalign:=1;
   end;

  UpdateAlignment(init_settings.alignment,option.paraalignment);

  set_system_macro('FPC_VERSION',version_nr);
  set_system_macro('FPC_RELEASE',release_nr);
  set_system_macro('FPC_PATCH',patch_nr);
  set_system_macro('FPC_FULLVERSION',Format('%d%.02d%.02d',[StrToInt(version_nr),StrToInt(release_nr),StrToInt(patch_nr)]));

  if not(target_info.system in systems_windows) then
    def_system_macro('FPC_WIDESTRING_EQUAL_UNICODESTRING');

  for i:=low(tfeature) to high(tfeature) do
    if i in features then
      def_system_macro('FPC_HAS_FEATURE_'+featurestr[i]);
  option.free;
  Option:=nil;

  clearstack_pocalls := [pocall_cdecl,pocall_cppdecl,pocall_syscall,pocall_mwpascal];
  cdecl_pocalls := [pocall_cdecl, pocall_cppdecl];
  if (tf_safecall_clearstack in target_info.flags) then
    begin
      include (cdecl_pocalls, pocall_safecall);
      include (clearstack_pocalls, pocall_safecall)
    end;
end;


initialization
  coption:=toption;
finalization
  if assigned(option) then
   option.free;
end.
