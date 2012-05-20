{
    Copyright (c) 1998-2002 by Florian Klaempfl

    This unit implements the scanner part and handling of the switches

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
unit scanner;

{$i fpcdefs.inc}

interface

    uses
       cclasses,
       globtype,globals,constexp,version,tokens,
       verbose,comphook,
       finput,
       widestr;

    const
       max_include_nesting=32;
       max_macro_nesting=16;
       preprocbufsize=32*1024;


    type
       tcommentstyle = (comment_none,comment_tp,comment_oldtp,comment_delphi,comment_c);

       tscannerfile = class;

       preproctyp = (pp_ifdef,pp_ifndef,pp_if,pp_ifopt,pp_else,pp_elseif);

       tpreprocstack = class
          typ     : preproctyp;
          accept  : boolean;
          next    : tpreprocstack;
          name    : TIDString;
          line_nb : longint;
          owner   : tscannerfile;
          constructor Create(atyp:preproctyp;a:boolean;n:tpreprocstack);
       end;

       tdirectiveproc=procedure;

       tdirectiveitem = class(TFPHashObject)
       public
          is_conditional : boolean;
          proc : tdirectiveproc;
          constructor Create(AList:TFPHashObjectList;const n:string;p:tdirectiveproc);
          constructor CreateCond(AList:TFPHashObjectList;const n:string;p:tdirectiveproc);
       end;

       // stack for replay buffers
       treplaystack = class
         token    : ttoken;
         settings : tsettings;
         tokenbuf : tdynamicarray;
         next     : treplaystack;
         change_endian : boolean;
         constructor Create(atoken: ttoken;asettings:tsettings;
           atokenbuf:tdynamicarray;anext:treplaystack; achange_endian : boolean);
       end;

       tcompile_time_predicate = function(var valuedescr: String) : Boolean;

       tspecialgenerictoken =
         (ST_LOADSETTINGS,
          ST_LINE,
          ST_COLUMN,
          ST_FILEINDEX,
          ST_LOADMESSAGES);

       { tscannerfile }
       tscannerfile = class
       private
         procedure do_gettokenpos(out tokenpos: longint; out filepos: tfileposinfo);
         procedure cachenexttokenpos;
         procedure setnexttoken;
         procedure savetokenpos;
         procedure restoretokenpos;
         procedure writetoken(t: ttoken);
         function readtoken : ttoken;
       public
          inputfile    : tinputfile;  { current inputfile list }
          inputfilecount : longint;

          inputbuffer,                { input buffer }
          inputpointer : pchar;
          inputstart   : longint;

          line_no,                    { line }
          lastlinepos  : longint;

          lasttokenpos,
          nexttokenpos : longint;     { token }
          lasttoken,
          nexttoken    : ttoken;

          oldlasttokenpos     : longint; { temporary saving/restoring tokenpos }
          oldcurrent_filepos,
          oldcurrent_tokenpos : tfileposinfo;


          replaytokenbuf,
          recordtokenbuf : tdynamicarray;
          tokenbuf_change_endian : boolean;

          { last settings we stored }
          last_settings : tsettings;
          last_message : pmessagestaterecord;
          { last filepos we stored }
          last_filepos,
          { if nexttoken<>NOTOKEN, then nexttokenpos holds its filepos }
          next_filepos   : tfileposinfo;

          comment_level,
          yylexcount     : longint;
          lastasmgetchar : char;
          ignoredirectives : TFPHashList; { ignore directives, used to give warnings only once }
          preprocstack   : tpreprocstack;
          replaystack    : treplaystack;
          in_asm_string  : boolean;

          preproc_pattern : string;
          preproc_token   : ttoken;

          constructor Create(const fn:string; is_macro: boolean = false);
          destructor Destroy;override;
        { File buffer things }
          function  openinputfile:boolean;
          procedure closeinputfile;
          function  tempopeninputfile:boolean;
          procedure tempcloseinputfile;
          procedure saveinputfile;
          procedure restoreinputfile;
          procedure firstfile;
          procedure nextfile;
          procedure addfile(hp:tinputfile);
          procedure reload;
          { replaces current token with the text in p }
          procedure substitutemacro(const macname:string;p:pchar;len,line,fileindex:longint);
        { Scanner things }
          procedure gettokenpos;
          procedure inc_comment_level;
          procedure dec_comment_level;
          procedure illegal_char(c:char);
          procedure end_of_file;
          procedure checkpreprocstack;
          procedure poppreprocstack;
          procedure ifpreprocstack(atyp : preproctyp;compile_time_predicate:tcompile_time_predicate;messid:longint);
          procedure elseifpreprocstack(compile_time_predicate:tcompile_time_predicate);
          procedure elsepreprocstack;
          procedure popreplaystack;
          procedure handleconditional(p:tdirectiveitem);
          procedure handledirectives;
          procedure linebreak;
          procedure recordtoken;
          procedure startrecordtokens(buf:tdynamicarray);
          procedure stoprecordtokens;
          procedure replaytoken;
          procedure startreplaytokens(buf:tdynamicarray; achange_endian : boolean);
          { bit length sizeint is target depend }
          procedure tokenwritesizeint(val : sizeint);
          function  tokenreadsizeint : sizeint;
          { longword/longint are 32 bits on all targets }
          { word/smallint are 16-bits on all targest }
          function  tokenreadlongword : longword;
          function  tokenreadword : word;
          function  tokenreadlongint : longint;
          function  tokenreadsmallint : smallint;
          { short int is one a signed byte }
          function  tokenreadshortint : shortint;
          function  tokenreadbyte : byte;
          { This one takes the set size as an parameter }
          procedure tokenreadset(var b;size : longint);
          function  tokenreadenum(size : longint) : longword;

          procedure tokenreadsettings(var asettings : tsettings; expected_size : longint);
          procedure readchar;
          procedure readstring;
          procedure readnumber;
          function  readid:string;
          function  readval:longint;
          function  readval_asstring:string;
          function  readcomment:string;
          function  readquotedstring:string;
          function  readstate:char;
          function  readstatedefault:char;
          procedure skipspace;
          procedure skipuntildirective;
          procedure skipcomment;
          procedure skipdelphicomment;
          procedure skipoldtpcomment;
          procedure readtoken(allowrecordtoken:boolean);
          function  readpreproc:ttoken;
          function  asmgetcharstart : char;
          function  asmgetchar:char;
       end;

{$ifdef PREPROCWRITE}
       tpreprocfile=class
         f   : text;
         buf : pointer;
         spacefound,
         eolfound : boolean;
         constructor create(const fn:string);
         destructor  destroy;
         procedure Add(const s:string);
         procedure AddSpace;
       end;
{$endif PREPROCWRITE}

    var
        { read strings }
        c              : char;
        orgpattern,
        pattern        : string;
        cstringpattern : ansistring;
        patternw       : pcompilerwidestring;

        { token }
        token,                        { current token being parsed }
        idtoken    : ttoken;          { holds the token if the pattern is a known word }

        current_scanner : tscannerfile;  { current scanner in use }

        aktcommentstyle : tcommentstyle; { needed to use read_comment from directives }
{$ifdef PREPROCWRITE}
        preprocfile     : tpreprocfile;  { used with only preprocessing }
{$endif PREPROCWRITE}

    type
        tdirectivemode = (directive_all, directive_turbo, directive_mac);

    procedure AddDirective(const s:string; dm: tdirectivemode; p:tdirectiveproc);
    procedure AddConditional(const s:string; dm: tdirectivemode; p:tdirectiveproc);

    procedure InitScanner;
    procedure DoneScanner;

    { To be called when the language mode is finally determined }
    Function SetCompileMode(const s:string; changeInit: boolean):boolean;
    Function SetCompileModeSwitch(s:string; changeInit: boolean):boolean;


implementation

    uses
      SysUtils,
      cutils,cfileutl,
      systems,
      switches,
      symbase,symtable,symtype,symsym,symconst,symdef,defutil,
      { This is needed for tcputype }
      cpuinfo,
      fmodule
{$if FPC_FULLVERSION<20700}
      ,ccharset
{$endif}
      ;

    var
      { dictionaries with the supported directives }
      turbo_scannerdirectives : TFPHashObjectList;     { for other modes }
      mac_scannerdirectives   : TFPHashObjectList;     { for mode mac }


{*****************************************************************************
                              Helper routines
*****************************************************************************}

    const
      { use any special name that is an invalid file name to avoid problems }
      preprocstring : array [preproctyp] of string[7]
        = ('$IFDEF','$IFNDEF','$IF','$IFOPT','$ELSE','$ELSEIF');

    function is_keyword(const s:string):boolean;
      var
        low,high,mid : longint;
      begin
        if not (length(s) in [tokenlenmin..tokenlenmax]) or
           not (s[1] in ['a'..'z','A'..'Z']) then
         begin
           is_keyword:=false;
           exit;
         end;
        low:=ord(tokenidx^[length(s),s[1]].first);
        high:=ord(tokenidx^[length(s),s[1]].last);
        while low<high do
         begin
           mid:=(high+low+1) shr 1;
           if pattern<tokeninfo^[ttoken(mid)].str then
            high:=mid-1
           else
            low:=mid;
         end;
        is_keyword:=(pattern=tokeninfo^[ttoken(high)].str) and
                    (tokeninfo^[ttoken(high)].keyword in current_settings.modeswitches);
      end;


    Procedure HandleModeSwitches(switch: tmodeswitch; changeInit: boolean);
      begin
        { turn ansi/unicodestrings on by default ? (only change when this
          particular setting is changed, so that a random modeswitch won't
          change the state of $h+/$h-) }
        if switch in [m_all,m_default_ansistring,m_default_unicodestring] then
          begin
            if ([m_default_ansistring,m_default_unicodestring]*current_settings.modeswitches)<>[] then
              begin
                { can't have both ansistring and unicodestring as default }
                if switch=m_default_ansistring then
                  begin
                    exclude(current_settings.modeswitches,m_default_unicodestring);
                    if changeinit then
                      exclude(init_settings.modeswitches,m_default_unicodestring);
                  end
                else if switch=m_default_unicodestring then
                  begin
                    exclude(current_settings.modeswitches,m_default_ansistring);
                    if changeinit then
                      exclude(init_settings.modeswitches,m_default_ansistring);
                  end;
                { enable $h+ }
                include(current_settings.localswitches,cs_refcountedstrings);
                if changeinit then
                  include(init_settings.localswitches,cs_refcountedstrings);
              end
            else
              begin
                exclude(current_settings.localswitches,cs_refcountedstrings);
                if changeinit then
                  exclude(init_settings.localswitches,cs_refcountedstrings);
              end;
          end;

        { turn inline on by default ? }
        if switch in [m_all,m_default_inline] then
          begin
            if (m_default_inline in current_settings.modeswitches) then
             begin
               include(current_settings.localswitches,cs_do_inline);
               if changeinit then
                 include(init_settings.localswitches,cs_do_inline);
             end
            else
             begin
               exclude(current_settings.localswitches,cs_do_inline);
               if changeinit then
                 exclude(init_settings.localswitches,cs_do_inline);
             end;
          end;

        { turn on system codepage by default }
        if switch in [m_all,m_systemcodepage] then
          begin
            if m_systemcodepage in current_settings.modeswitches then
              begin
                current_settings.sourcecodepage:=DefaultSystemCodePage;
                if not cpavailable(current_settings.sourcecodepage) then
                  begin
                    Message2(scan_w_unavailable_system_codepage,IntToStr(current_settings.sourcecodepage),IntToStr(default_settings.sourcecodepage));
                    current_settings.sourcecodepage:=default_settings.sourcecodepage;
                  end;
                include(current_settings.moduleswitches,cs_explicit_codepage);
                if changeinit then
                begin
                  init_settings.sourcecodepage:=current_settings.sourcecodepage;
                  include(init_settings.moduleswitches,cs_explicit_codepage);
                end;
              end
            else
              begin
                exclude(current_settings.moduleswitches,cs_explicit_codepage);
                if changeinit then
                  exclude(init_settings.moduleswitches,cs_explicit_codepage);
              end;
          end;
      end;


    Function SetCompileMode(const s:string; changeInit: boolean):boolean;
      var
        b : boolean;
        oldmodeswitches : tmodeswitches;
      begin
        oldmodeswitches:=current_settings.modeswitches;

        b:=true;
        if s='DEFAULT' then
          current_settings.modeswitches:=fpcmodeswitches
        else
         if s='DELPHI' then
          current_settings.modeswitches:=delphimodeswitches
        else
         if s='DELPHIUNICODE' then
          current_settings.modeswitches:=delphiunicodemodeswitches
        else
         if s='TP' then
          current_settings.modeswitches:=tpmodeswitches
        else
         if s='FPC' then begin
          current_settings.modeswitches:=fpcmodeswitches;
          { TODO: enable this for 2.3/2.9 }
          //  include(current_settings.localswitches, cs_typed_addresses);
        end else
         if s='OBJFPC' then begin
          current_settings.modeswitches:=objfpcmodeswitches;
          { TODO: enable this for 2.3/2.9 }
          //  include(current_settings.localswitches, cs_typed_addresses);
        end
{$ifdef gpc_mode}
        else if s='GPC' then
          current_settings.modeswitches:=gpcmodeswitches
{$endif}
        else
         if s='MACPAS' then
          current_settings.modeswitches:=macmodeswitches
        else
         if s='ISO' then
          current_settings.modeswitches:=isomodeswitches
        else
         b:=false;

{$ifdef jvm}
          { enable final fields by default for the JVM targets }
          include(current_settings.modeswitches,m_final_fields);
{$endif jvm}

        if b and changeInit then
          init_settings.modeswitches := current_settings.modeswitches;

        if b then
         begin
           { resolve all postponed switch changes }
           flushpendingswitchesstate;

           HandleModeSwitches(m_all,changeinit);

           { turn on bitpacking for mode macpas and iso pascal }
           if ([m_mac,m_iso] * current_settings.modeswitches <> []) then
             begin
               include(current_settings.localswitches,cs_bitpacking);
               if changeinit then
                 include(init_settings.localswitches,cs_bitpacking);
             end;

           { support goto/label by default in delphi/tp7/mac modes }
           if ([m_delphi,m_tp7,m_mac,m_iso] * current_settings.modeswitches <> []) then
             begin
               include(current_settings.moduleswitches,cs_support_goto);
               if changeinit then
                 include(init_settings.moduleswitches,cs_support_goto);
             end;

           { support pointer math by default in fpc/objfpc modes }
           if ([m_fpc,m_objfpc] * current_settings.modeswitches <> []) then
             begin
               include(current_settings.localswitches,cs_pointermath);
               if changeinit then
                 include(init_settings.localswitches,cs_pointermath);
             end
           else
             begin
               exclude(current_settings.localswitches,cs_pointermath);
               if changeinit then
                 exclude(init_settings.localswitches,cs_pointermath);
             end;

           { Default enum and set packing for delphi/tp7 }
           if (m_tp7 in current_settings.modeswitches) or
              (m_delphi in current_settings.modeswitches) then
             begin
               current_settings.packenum:=1;
               current_settings.setalloc:=1;
             end
           else if (m_mac in current_settings.modeswitches) then
             { compatible with Metrowerks Pascal }
             current_settings.packenum:=2
           else
             current_settings.packenum:=4;
           if changeinit then
             init_settings.packenum:=current_settings.packenum;
{$ifdef i386}
           { Default to intel assembler for delphi/tp7 on i386 }
           if (m_delphi in current_settings.modeswitches) or
              (m_tp7 in current_settings.modeswitches) then
             current_settings.asmmode:=asmmode_i386_intel;
           if changeinit then
             init_settings.asmmode:=current_settings.asmmode;
{$endif i386}

           { Exception support explicitly turned on (mainly for macpas, to }
           { compensate for lack of interprocedural goto support)          }
           if (cs_support_exceptions in current_settings.globalswitches) then
             include(current_settings.modeswitches,m_except);

           { Default strict string var checking in TP/Delphi modes }
           if ([m_delphi,m_tp7] * current_settings.modeswitches <> []) then
             begin
               include(current_settings.localswitches,cs_strict_var_strings);
               if changeinit then
                 include(init_settings.localswitches,cs_strict_var_strings);
             end;

            { Undefine old symbol }
            if (m_delphi in oldmodeswitches) then
              undef_system_macro('FPC_DELPHI')
            else if (m_tp7 in oldmodeswitches) then
              undef_system_macro('FPC_TP')
            else if (m_objfpc in oldmodeswitches) then
              undef_system_macro('FPC_OBJFPC')
{$ifdef gpc_mode}
            else if (m_gpc in oldmodeswitches) then
              undef_system_macro('FPC_GPC')
{$endif}
            else if (m_mac in oldmodeswitches) then
              undef_system_macro('FPC_MACPAS');

            { define new symbol in delphi,objfpc,tp,gpc,macpas mode }
            if (m_delphi in current_settings.modeswitches) then
              def_system_macro('FPC_DELPHI')
            else if (m_tp7 in current_settings.modeswitches) then
              def_system_macro('FPC_TP')
            else if (m_objfpc in current_settings.modeswitches) then
              def_system_macro('FPC_OBJFPC')
{$ifdef gpc_mode}
            else if (m_gpc in current_settings.modeswitches) then
              def_system_macro('FPC_GPC')
{$endif}
            else if (m_mac in current_settings.modeswitches) then
              def_system_macro('FPC_MACPAS');
         end;

        SetCompileMode:=b;
      end;


    Function SetCompileModeSwitch(s:string; changeInit: boolean):boolean;
      var
        i : tmodeswitch;
        doinclude : boolean;
      begin
        s:=upper(s);

        { on/off? }
        doinclude:=true;
        case s[length(s)] of
          '+':
            s:=copy(s,1,length(s)-1);
          '-':
            begin
              s:=copy(s,1,length(s)-1);
              doinclude:=false;
            end;
        end;

        Result:=false;
        for i:=m_class to high(tmodeswitch) do
          if s=modeswitchstr[i] then
            begin
              { Objective-C is currently only supported for Darwin targets }
              if doinclude and
                 (i in [m_objectivec1,m_objectivec2]) and
                 not(target_info.system in systems_objc_supported) then
                begin
                  Message1(option_unsupported_target_for_feature,'Objective-C');
                  break;
                end;

              if changeInit then
                current_settings.modeswitches:=init_settings.modeswitches;
              Result:=true;
              if doinclude then
                begin
                  include(current_settings.modeswitches,i);
                  { Objective-C 2.0 support implies 1.0 support }
                  if (i=m_objectivec2) then
                    include(current_settings.modeswitches,m_objectivec1);
                  if (i in [m_objectivec1,m_objectivec2]) then
                    include(current_settings.modeswitches,m_class);
                end
              else
                begin
                  exclude(current_settings.modeswitches,i);
                  { Objective-C 2.0 support implies 1.0 support }
                  if (i=m_objectivec2) then
                    exclude(current_settings.modeswitches,m_objectivec1);
                  if (i in [m_objectivec1,m_objectivec2]) and
                     ([m_delphi,m_objfpc]*current_settings.modeswitches=[]) then
                    exclude(current_settings.modeswitches,m_class);
                end;

              { set other switches depending on changed mode switch }
              HandleModeSwitches(i,changeinit);

              if changeInit then
                init_settings.modeswitches:=current_settings.modeswitches;

              break;
            end;
      end;

{*****************************************************************************
                           Conditional Directives
*****************************************************************************}

    procedure dir_else;
      begin
        current_scanner.elsepreprocstack;
      end;


    procedure dir_endif;
      begin
        current_scanner.poppreprocstack;
      end;

    function isdef(var valuedescr: String): Boolean;
      var
        hs    : string;
      begin
        current_scanner.skipspace;
        hs:=current_scanner.readid;
        valuedescr:= hs;
        if hs='' then
          Message(scan_e_error_in_preproc_expr);
        isdef:=defined_macro(hs);
      end;

    procedure dir_ifdef;
      begin
        current_scanner.ifpreprocstack(pp_ifdef,@isdef,scan_c_ifdef_found);
      end;

    function isnotdef(var valuedescr: String): Boolean;
      var
        hs    : string;
      begin
        current_scanner.skipspace;
        hs:=current_scanner.readid;
        valuedescr:= hs;
        if hs='' then
          Message(scan_e_error_in_preproc_expr);
        isnotdef:=not defined_macro(hs);
      end;

    procedure dir_ifndef;
      begin
        current_scanner.ifpreprocstack(pp_ifndef,@isnotdef,scan_c_ifndef_found);
      end;

    function opt_check(var valuedescr: String): Boolean;
      var
        hs    : string;
        state : char;
      begin
        opt_check:= false;
        current_scanner.skipspace;
        hs:=current_scanner.readid;
        valuedescr:= hs;
        if (length(hs)>1) then
          Message1(scan_w_illegal_switch,hs)
        else
          begin
            state:=current_scanner.ReadState;
            if state in ['-','+'] then
              opt_check:=CheckSwitch(hs[1],state)
            else
              Message(scan_e_error_in_preproc_expr);
          end;
      end;

    procedure dir_ifopt;
      begin
        flushpendingswitchesstate;
        current_scanner.ifpreprocstack(pp_ifopt,@opt_check,scan_c_ifopt_found);
      end;

    procedure dir_libprefix;
      var
        s : string;
      begin
        current_scanner.skipspace;
        if c <> '''' then
          Message2(scan_f_syn_expected, '''', c);
        s := current_scanner.readquotedstring;
        stringdispose(outputprefix);
        outputprefix := stringdup(s);
        with current_module do
         setfilename(paramfn, paramallowoutput);
      end;

    procedure dir_libsuffix;
      var
        s : string;
      begin
        current_scanner.skipspace;
        if c <> '''' then
          Message2(scan_f_syn_expected, '''', c);
        s := current_scanner.readquotedstring;
        stringdispose(outputsuffix);
        outputsuffix := stringdup(s);
        with current_module do
          setfilename(paramfn, paramallowoutput);
      end;

    procedure dir_extension;
      var
        s : string;
      begin
        current_scanner.skipspace;
        if c <> '''' then
          Message2(scan_f_syn_expected, '''', c);
        s := current_scanner.readquotedstring;
        if OutputFileName='' then
          OutputFileName:=InputFileName;
        OutputFileName:=ChangeFileExt(OutputFileName,'.'+s);
        with current_module do
          setfilename(paramfn, paramallowoutput);
      end;

{
Compile time expression type check
----------------------------------
Each subexpression returns its type to the caller, which then can
do type check.  Since data types of compile time expressions is
not well defined, the type system does a best effort. The drawback is
that some errors might not be detected.

Instead of returning a particular data type, a set of possible data types
are returned. This way ambigouos types can be handled.  For instance a
value of 1 can be both a boolean and and integer.

Booleans
--------

The following forms of boolean values are supported:
* C coded, that is 0 is false, non-zero is true.
* TRUE/FALSE for mac style compile time variables

Thus boolean mac compile time variables are always stored as TRUE/FALSE.
When a compile time expression is evaluated, they are then translated
to C coded booleans (0/1), to simplify for the expression evaluator.

Note that this scheme then also of support mac compile time variables which
are 0/1 but with a boolean meaning.

The TRUE/FALSE format is new from 22 august 2005, but the above scheme
means that units which is not recompiled, and thus stores
compile time variables as the old format (0/1), continue to work.

Short circuit evaluation
------------------------
For this to work, the part of a compile time expression which is short
circuited, should not be evaluated, while it still should be parsed.
Therefor there is a parameter eval, telling whether evaluation is needed.
In case not, the value returned can be arbitrary.
}

    type
      {Compile time expression types}
      TCTEType = (ctetBoolean, ctetInteger, ctetString, ctetSet);
      TCTETypeSet = set of TCTEType;

    const
      cteTypeNames : array[TCTEType] of string[10] = (
        'BOOLEAN','INTEGER','STRING','SET');

      {Subset of types which can be elements in sets.}
      setelementdefs = [ctetBoolean, ctetInteger, ctetString];


    function GetCTETypeName(t: TCTETypeSet): String;
      var
        i: TCTEType;
      begin
        result:= '';
        for i:= Low(TCTEType) to High(TCTEType) do
          if i in t then
            if result = '' then
              result:= cteTypeNames[i]
            else
              result:= result + ' or ' + cteTypeNames[i];
      end;

    procedure CTEError(actType, desiredExprType: TCTETypeSet; place: String);

    begin
      Message3(scan_e_compile_time_typeerror,
               GetCTETypeName(desiredExprType),
               GetCTETypeName(actType),
               place
              );
    end;

    function parse_compiler_expr(var compileExprType: TCTETypeSet):string;

        function read_expr(var exprType: TCTETypeSet; eval : Boolean) : string; forward;

        procedure preproc_consume(t : ttoken);
        begin
          if t<>current_scanner.preproc_token then
            Message(scan_e_preproc_syntax_error);
          current_scanner.preproc_token:=current_scanner.readpreproc;
        end;

        function preproc_substitutedtoken(var macroType: TCTETypeSet; eval : Boolean): string;
                                { Currently this parses identifiers as well as numbers.
          The result from this procedure can either be that the token
          itself is a value, or that it is a compile time variable/macro,
          which then is substituted for another value (for macros
          recursivelly substituted).}

        var
          hs: string;
          mac : tmacro;
          macrocount,
          len : integer;
          numres : longint;
          w: word;
        begin
          result := current_scanner.preproc_pattern;
          if not eval then
            exit;

          mac:= nil;
          { Substitue macros and compiler variables with their content/value.
            For real macros also do recursive substitution. }
          macrocount:=0;
          repeat
            mac:=tmacro(search_macro(result));

            inc(macrocount);
            if macrocount>max_macro_nesting then
              begin
                Message(scan_w_macro_too_deep);
                break;
              end;

            if assigned(mac) and mac.defined then
              if assigned(mac.buftext) then
                begin
                  if mac.buflen>255 then
                    begin
                      len:=255;
                      Message(scan_w_macro_cut_after_255_chars);
                    end
                  else
                    len:=mac.buflen;
                  hs[0]:=char(len);
                  move(mac.buftext^,hs[1],len);
                  result:=upcase(hs);
                  mac.is_used:=true;
                end
              else
                begin
                  Message1(scan_e_error_macro_lacks_value, result);
                  break;
                end
            else
              begin
                  break;
              end;

            if mac.is_compiler_var then
              break;
          until false;

          { At this point, result do contain the value. Do some decoding and
            determine the type.}
          val(result,numres,w);
          if (w=0) then {It is an integer}
            begin
              if (numres = 0) or (numres = 1) then
                macroType := [ctetInteger, ctetBoolean]
              else
                macroType := [ctetInteger];
            end
          else if assigned(mac) and (m_mac in current_settings.modeswitches) and (result='FALSE') then
            begin
              result:= '0';
              macroType:= [ctetBoolean];
            end
          else if assigned(mac) and (m_mac in current_settings.modeswitches) and (result='TRUE') then
            begin
              result:= '1';
              macroType:= [ctetBoolean];
            end
          else if (m_mac in current_settings.modeswitches) and
                  (not assigned(mac) or not mac.defined) and
                  (macrocount = 1) then
            begin
              {Errors in mode mac is issued here. For non macpas modes there is
               more liberty, but the error will eventually be caught at a later stage.}
              Message1(scan_e_error_macro_undefined, result);
              macroType:= [ctetString]; {Just to have something}
            end
          else
            macroType:= [ctetString];
        end;

        function read_factor(var factorType: TCTETypeSet; eval : Boolean) : string;
        var
           hs : string;
           mac: tmacro;
           srsym : tsym;
           srsymtable : TSymtable;
           hdef : TDef;
           l : longint;
           w : integer;
           hasKlammer: Boolean;
           setElemType : TCTETypeSet;

        begin
           if current_scanner.preproc_token=_ID then
             begin
                if current_scanner.preproc_pattern='DEFINED' then
                  begin
                    factorType:= [ctetBoolean];
                    preproc_consume(_ID);
                    current_scanner.skipspace;
                    if current_scanner.preproc_token =_LKLAMMER then
                      begin
                        preproc_consume(_LKLAMMER);
                        current_scanner.skipspace;
                        hasKlammer:= true;
                      end
                    else if (m_mac in current_settings.modeswitches) then
                      hasKlammer:= false
                    else
                      Message(scan_e_error_in_preproc_expr);

                    if current_scanner.preproc_token =_ID then
                      begin
                        hs := current_scanner.preproc_pattern;
                        mac := tmacro(search_macro(hs));
                        if assigned(mac) and mac.defined then
                          begin
                            hs := '1';
                            mac.is_used:=true;
                          end
                        else
                          hs := '0';
                        read_factor := hs;
                        preproc_consume(_ID);
                        current_scanner.skipspace;
                      end
                    else
                      Message(scan_e_error_in_preproc_expr);

                    if hasKlammer then
                      if current_scanner.preproc_token =_RKLAMMER then
                        preproc_consume(_RKLAMMER)
                      else
                        Message(scan_e_error_in_preproc_expr);
                  end
                else
                if (m_mac in current_settings.modeswitches) and (current_scanner.preproc_pattern='UNDEFINED') then
                  begin
                    factorType:= [ctetBoolean];
                    preproc_consume(_ID);
                    current_scanner.skipspace;
                    if current_scanner.preproc_token =_ID then
                      begin
                        hs := current_scanner.preproc_pattern;
                        mac := tmacro(search_macro(hs));
                        if assigned(mac) then
                          begin
                            hs := '0';
                            mac.is_used:=true;
                          end
                        else
                          hs := '1';
                        read_factor := hs;
                        preproc_consume(_ID);
                        current_scanner.skipspace;
                      end
                    else
                      Message(scan_e_error_in_preproc_expr);
                  end
                else
                if (m_mac in current_settings.modeswitches) and (current_scanner.preproc_pattern='OPTION') then
                  begin
                    factorType:= [ctetBoolean];
                    preproc_consume(_ID);
                    current_scanner.skipspace;
                    if current_scanner.preproc_token =_LKLAMMER then
                      begin
                        preproc_consume(_LKLAMMER);
                        current_scanner.skipspace;
                      end
                    else
                      Message(scan_e_error_in_preproc_expr);

                    if not (current_scanner.preproc_token = _ID) then
                      Message(scan_e_error_in_preproc_expr);

                    hs:=current_scanner.preproc_pattern;
                    if (length(hs) > 1) then
                      {This is allowed in Metrowerks Pascal}
                      Message(scan_e_error_in_preproc_expr)
                    else
                      begin
                        if CheckSwitch(hs[1],'+') then
                          read_factor := '1'
                        else
                          read_factor := '0';
                      end;

                    preproc_consume(_ID);
                    current_scanner.skipspace;
                    if current_scanner.preproc_token =_RKLAMMER then
                      preproc_consume(_RKLAMMER)
                    else
                      Message(scan_e_error_in_preproc_expr);
                  end
                else
                if current_scanner.preproc_pattern='SIZEOF' then
                  begin
                    factorType:= [ctetInteger];
                    preproc_consume(_ID);
                    current_scanner.skipspace;
                    if current_scanner.preproc_token =_LKLAMMER then
                      begin
                        preproc_consume(_LKLAMMER);
                        current_scanner.skipspace;
                      end
                    else
                      Message(scan_e_preproc_syntax_error);

                    if eval then
                      if searchsym(current_scanner.preproc_pattern,srsym,srsymtable) then
                        begin
                          l:=0;
                          case srsym.typ of
                            staticvarsym,
                            localvarsym,
                            paravarsym :
                              l:=tabstractvarsym(srsym).getsize;
                            typesym:
                              l:=ttypesym(srsym).typedef.size;
                            else
                              Message(scan_e_error_in_preproc_expr);
                          end;
                          str(l,read_factor);
                        end
                      else
                        Message1(sym_e_id_not_found,current_scanner.preproc_pattern);

                    preproc_consume(_ID);
                    current_scanner.skipspace;

                    if current_scanner.preproc_token =_RKLAMMER then
                      preproc_consume(_RKLAMMER)
                    else
                      Message(scan_e_preproc_syntax_error);
                  end
                else
                if current_scanner.preproc_pattern='HIGH' then
                  begin
                    factorType:= [ctetInteger];
                    preproc_consume(_ID);
                    current_scanner.skipspace;
                    if current_scanner.preproc_token =_LKLAMMER then
                      begin
                        preproc_consume(_LKLAMMER);
                        current_scanner.skipspace;
                      end
                    else
                      Message(scan_e_preproc_syntax_error);

                    if eval then
                      if searchsym(current_scanner.preproc_pattern,srsym,srsymtable) then
                        begin
                          hdef:=nil;
                          hs:='';
                          l:=0;
                          case srsym.typ of
                            staticvarsym,
                            localvarsym,
                            paravarsym :
                              hdef:=tabstractvarsym(srsym).vardef;
                            typesym:
                              hdef:=ttypesym(srsym).typedef;
                            else
                              Message(scan_e_error_in_preproc_expr);
                          end;
                          if hdef<>nil then
                            begin
                              if hdef.typ=setdef then
                                hdef:=tsetdef(hdef).elementdef;
                              case hdef.typ of
                                orddef:
                                  with torddef(hdef).high do
                                    if signed then
                                      str(svalue,hs)
                                    else
                                      str(uvalue,hs);
                                enumdef:
                                  l:=tenumdef(hdef).maxval;
                                arraydef:
                                  if is_open_array(hdef) or is_array_of_const(hdef) or is_dynamic_array(hdef) then
                                    Message(type_e_mismatch)
                                  else
                                    l:=tarraydef(hdef).highrange;
                                stringdef:
                                  if is_open_string(hdef) or is_ansistring(hdef) or is_wide_or_unicode_string(hdef) then
                                    Message(type_e_mismatch)
                                  else
                                    l:=tstringdef(hdef).len;
                                else
                                  Message(type_e_mismatch);
                              end;
                            end;
                          if hs='' then
                            str(l,read_factor)
                          else
                            read_factor:=hs;
                        end
                      else
                        Message1(sym_e_id_not_found,current_scanner.preproc_pattern);

                    preproc_consume(_ID);
                    current_scanner.skipspace;

                    if current_scanner.preproc_token =_RKLAMMER then
                      preproc_consume(_RKLAMMER)
                    else
                      Message(scan_e_preproc_syntax_error);
                  end
                else
                if current_scanner.preproc_pattern='DECLARED' then
                  begin
                    factorType:= [ctetBoolean];
                    preproc_consume(_ID);
                    current_scanner.skipspace;
                    if current_scanner.preproc_token =_LKLAMMER then
                      begin
                        preproc_consume(_LKLAMMER);
                        current_scanner.skipspace;
                      end
                    else
                      Message(scan_e_error_in_preproc_expr);
                    if current_scanner.preproc_token =_ID then
                      begin
                        hs := upper(current_scanner.preproc_pattern);
                        if searchsym(hs,srsym,srsymtable) then
                          hs := '1'
                        else
                          hs := '0';
                        read_factor := hs;
                        preproc_consume(_ID);
                        current_scanner.skipspace;
                      end
                    else
                      Message(scan_e_error_in_preproc_expr);
                    if current_scanner.preproc_token =_RKLAMMER then
                      preproc_consume(_RKLAMMER)
                    else
                      Message(scan_e_error_in_preproc_expr);
                  end
                else
                if current_scanner.preproc_pattern='NOT' then
                  begin
                    factorType:= [ctetBoolean];
                    preproc_consume(_ID);
                    hs:=read_factor(factorType, eval);
                    if eval then
                      begin
                        if not (ctetBoolean in factorType) then
                          CTEError(factorType, [ctetBoolean], 'NOT');
                        val(hs,l,w);
                        if l<>0 then
                          read_factor:='0'
                        else
                          read_factor:='1';
                      end
                    else
                      read_factor:='0'; {Just to have something}
                  end
                else
                if (m_mac in current_settings.modeswitches) and (current_scanner.preproc_pattern='TRUE') then
                  begin
                    factorType:= [ctetBoolean];
                    preproc_consume(_ID);
                    read_factor:='1';
                  end
                else
                if (m_mac in current_settings.modeswitches) and (current_scanner.preproc_pattern='FALSE') then
                  begin
                    factorType:= [ctetBoolean];
                    preproc_consume(_ID);
                    read_factor:='0';
                  end
                else
                  begin
                    hs:=preproc_substitutedtoken(factorType, eval);

                    { Default is to return the original symbol }
                    read_factor:=hs;
                    if eval and ([m_delphi,m_objfpc]*current_settings.modeswitches<>[]) and (ctetString in factorType) then
                      if searchsym(current_scanner.preproc_pattern,srsym,srsymtable) then
                        begin
                          case srsym.typ of
                            constsym :
                              begin
                                with tconstsym(srsym) do
                                  begin
                                    case consttyp of
                                      constord :
                                        begin
                                          case constdef.typ of
                                            orddef:
                                              begin
                                                if is_integer(constdef) then
                                                  begin
                                                    read_factor:=tostr(value.valueord);
                                                    factorType:= [ctetInteger];
                                                  end
                                                else if is_boolean(constdef) then
                                                  begin
                                                    read_factor:=tostr(value.valueord);
                                                    factorType:= [ctetBoolean];
                                                  end
                                                else if is_char(constdef) then
                                                  begin
                                                    read_factor:=char(qword(value.valueord));
                                                    factorType:= [ctetString];
                                                  end
                                              end;
                                            enumdef:
                                              begin
                                                read_factor:=tostr(value.valueord);
                                                factorType:= [ctetInteger];
                                              end;
                                          end;
                                        end;
                                      conststring :
                                        begin
                                          read_factor := upper(pchar(value.valueptr));
                                          factorType:= [ctetString];
                                        end;
                                      constset :
                                        begin
                                          hs:=',';
                                          for l:=0 to 255 do
                                            if l in pconstset(tconstsym(srsym).value.valueptr)^ then
                                              hs:=hs+tostr(l)+',';
                                          read_factor := hs;
                                          factorType:= [ctetSet];
                                        end;
                                    end;
                                  end;
                              end;
                            enumsym :
                              begin
                                read_factor:=tostr(tenumsym(srsym).value);
                                factorType:= [ctetInteger];
                              end;
                          end;
                        end;
                    preproc_consume(_ID);
                    current_scanner.skipspace;
                  end
             end
           else if current_scanner.preproc_token =_LKLAMMER then
             begin
                preproc_consume(_LKLAMMER);
                read_factor:=read_expr(factorType, eval);
                preproc_consume(_RKLAMMER);
             end
           else if current_scanner.preproc_token = _LECKKLAMMER then
             begin
               preproc_consume(_LECKKLAMMER);
               read_factor := ',';
               while current_scanner.preproc_token = _ID do
               begin
                 read_factor := read_factor+read_factor(setElemType, eval)+',';
                 if current_scanner.preproc_token = _COMMA then
                   preproc_consume(_COMMA);
               end;
               // TODO Add check of setElemType
               preproc_consume(_RECKKLAMMER);
               factorType:= [ctetSet];
             end
           else
             Message(scan_e_error_in_preproc_expr);
        end;

        function read_term(var termType: TCTETypeSet; eval : Boolean) : string;
        var
           hs1,hs2 : string;
           l1,l2 : longint;
           w : integer;
           termType2: TCTETypeSet;
        begin
          hs1:=read_factor(termType, eval);
          repeat
            if (current_scanner.preproc_token<>_ID) then
              break;
            if current_scanner.preproc_pattern<>'AND' then
              break;

            val(hs1,l1,w);
            if l1=0 then
              eval:= false; {Short circuit evaluation of OR}

            if eval then
               begin
                {Check if first expr is boolean. Must be done here, after we know
                 it is an AND expression.}
                if not (ctetBoolean in termType) then
                  CTEError(termType, [ctetBoolean], 'AND');
                termType:= [ctetBoolean];
              end;

            preproc_consume(_ID);
            hs2:=read_factor(termType2, eval);

            if eval then
              begin
                if not (ctetBoolean in termType2) then
                  CTEError(termType2, [ctetBoolean], 'AND');

                val(hs2,l2,w);
                if (l1<>0) and (l2<>0) then
                  hs1:='1'
                else
                  hs1:='0';
              end;
           until false;
           read_term:=hs1;
        end;


        function read_simple_expr(var simpleExprType: TCTETypeSet; eval : Boolean) : string;
        var
           hs1,hs2 : string;
           l1,l2 : longint;
           w : integer;
           simpleExprType2: TCTETypeSet;
        begin
          hs1:=read_term(simpleExprType, eval);
          repeat
            if (current_scanner.preproc_token<>_ID) then
              break;
            if current_scanner.preproc_pattern<>'OR' then
              break;

            val(hs1,l1,w);
            if l1<>0 then
              eval:= false; {Short circuit evaluation of OR}

            if eval then
              begin
                {Check if first expr is boolean. Must be done here, after we know
                 it is an OR expression.}
                if not (ctetBoolean in simpleExprType) then
                  CTEError(simpleExprType, [ctetBoolean], 'OR');
                simpleExprType:= [ctetBoolean];
              end;

            preproc_consume(_ID);
            hs2:=read_term(simpleExprType2, eval);

            if eval then
              begin
                if not (ctetBoolean in simpleExprType2) then
                  CTEError(simpleExprType2, [ctetBoolean], 'OR');

                val(hs2,l2,w);
                if (l1<>0) or (l2<>0) then
                  hs1:='1'
                else
                  hs1:='0';
              end;
          until false;
          read_simple_expr:=hs1;
        end;

        function read_expr(var exprType: TCTETypeSet; eval : Boolean) : string;
        var
           hs1,hs2 : string;
           b : boolean;
           op : ttoken;
           w : integer;
           l1,l2 : longint;
           exprType2: TCTETypeSet;
        begin
           hs1:=read_simple_expr(exprType, eval);
           op:=current_scanner.preproc_token;
           if (op = _ID) and (current_scanner.preproc_pattern = 'IN') then
             op := _IN;
           if not (op in [_IN,_EQ,_NE,_LT,_GT,_LTE,_GTE]) then
             begin
                read_expr:=hs1;
                exit;
             end;

           if (op = _IN) then
             preproc_consume(_ID)
           else
             preproc_consume(op);
           hs2:=read_simple_expr(exprType2, eval);

           if eval then
             begin
               if op = _IN then
                 begin
                   if exprType2 <> [ctetSet] then
                     CTEError(exprType2, [ctetSet], 'IN');
                   if exprType = [ctetSet] then
                     CTEError(exprType, setelementdefs, 'IN');

                  if is_number(hs1) and is_number(hs2) then
                    Message(scan_e_preproc_syntax_error)
                  else if hs2[1] = ',' then
                    b:=pos(','+hs1+',', hs2) > 0   { TODO For integer sets, perhaps check for numeric equivalence so that 0 = 00 }
                  else
                    Message(scan_e_preproc_syntax_error);
                 end
               else
                 begin
                   if (exprType * exprType2) = [] then
                     CTEError(exprType2, exprType, '"'+hs1+' '+tokeninfo^[op].str+' '+hs2+'"');

                   if is_number(hs1) and is_number(hs2) then
                     begin
                       val(hs1,l1,w);
                       val(hs2,l2,w);
                       case op of
                         _EQ :
                           b:=l1=l2;
                         _NE :
                           b:=l1<>l2;
                         _LT :
                           b:=l1<l2;
                         _GT :
                           b:=l1>l2;
                         _GTE :
                           b:=l1>=l2;
                         _LTE :
                           b:=l1<=l2;
                       end;
                     end
                   else
                     begin
                       case op of
                         _EQ:
                           b:=hs1=hs2;
                         _NE :
                           b:=hs1<>hs2;
                         _LT :
                           b:=hs1<hs2;
                         _GT :
                            b:=hs1>hs2;
                         _GTE :
                            b:=hs1>=hs2;
                         _LTE :
                           b:=hs1<=hs2;
                       end;
                     end;
                 end;
              end
           else
             b:= false; {Just to have something}

           if b then
             read_expr:='1'
           else
             read_expr:='0';
           exprType:= [ctetBoolean];
        end;

     begin
        current_scanner.skipspace;
        { start preproc expression scanner }
        current_scanner.preproc_token:=current_scanner.readpreproc;
        parse_compiler_expr:=read_expr(compileExprType, true);
     end;

    function boolean_compile_time_expr(var valuedescr: String): Boolean;
      var
        hs : string;
        exprType: TCTETypeSet;
      begin
        hs:=parse_compiler_expr(exprType);
        if (exprType * [ctetBoolean]) = [] then
          CTEError(exprType, [ctetBoolean], 'IF or ELSEIF');
        boolean_compile_time_expr:= hs <> '0';
        valuedescr:= hs;
      end;

    procedure dir_if;
      begin
        current_scanner.ifpreprocstack(pp_if,@boolean_compile_time_expr, scan_c_if_found);
      end;

    procedure dir_elseif;
      begin
        current_scanner.elseifpreprocstack(@boolean_compile_time_expr);
      end;

    procedure dir_define_impl(macstyle: boolean);
      var
        hs  : string;
        bracketcount : longint;
        mac : tmacro;
        macropos : longint;
        macrobuffer : pmacrobuffer;
      begin
        current_scanner.skipspace;
        hs:=current_scanner.readid;
        mac:=tmacro(search_macro(hs));
        if not assigned(mac) or (mac.owner <> current_module.localmacrosymtable) then
          begin
            mac:=tmacro.create(hs);
            mac.defined:=true;
            current_module.localmacrosymtable.insert(mac);
          end
        else
          begin
            mac.defined:=true;
            mac.is_compiler_var:=false;
          { delete old definition }
            if assigned(mac.buftext) then
             begin
               freemem(mac.buftext,mac.buflen);
               mac.buftext:=nil;
             end;
          end;
        Message1(parser_c_macro_defined,mac.name);
        mac.is_used:=true;
        if (cs_support_macro in current_settings.moduleswitches) then
          begin
             current_scanner.skipspace;

             if not macstyle then
               begin
                 { may be a macro? }
                 if c <> ':' then
                   exit;
                 current_scanner.readchar;
                 if c <> '=' then
                   exit;
                 current_scanner.readchar;
                 current_scanner.skipspace;
               end;

             { key words are never substituted }
             if is_keyword(hs) then
               Message(scan_e_keyword_cant_be_a_macro);

             new(macrobuffer);
             macropos:=0;
             { parse macro, brackets are counted so it's possible
               to have a $ifdef etc. in the macro }
             bracketcount:=0;
             repeat
               case c of
                 '}' :
                   if (bracketcount=0) then
                    break
                   else
                    dec(bracketcount);
                 '{' :
                   inc(bracketcount);
                 #10,#13 :
                   current_scanner.linebreak;
                 #26 :
                   current_scanner.end_of_file;
               end;
               macrobuffer^[macropos]:=c;
               inc(macropos);
               if macropos>=maxmacrolen then
                 Message(scan_f_macro_buffer_overflow);
               current_scanner.readchar;
             until false;

             { free buffer of macro ?}
             if assigned(mac.buftext) then
               freemem(mac.buftext,mac.buflen);
             { get new mem }
             getmem(mac.buftext,macropos);
             mac.buflen:=macropos;
             { copy the text }
             move(macrobuffer^,mac.buftext^,macropos);
             dispose(macrobuffer);
          end
        else
          begin
           { check if there is an assignment, then we need to give a
             warning }
             current_scanner.skipspace;
             if c=':' then
              begin
                current_scanner.readchar;
                if c='=' then
                  Message(scan_w_macro_support_turned_off);
              end;
          end;
      end;

    procedure dir_define;
      begin
        dir_define_impl(false);
      end;

    procedure dir_definec;
      begin
        dir_define_impl(true);
      end;

    procedure dir_setc;
      var
        hs  : string;
        mac : tmacro;
        exprType: TCTETypeSet;
        l : longint;
        w : integer;
      begin
        current_scanner.skipspace;
        hs:=current_scanner.readid;
        mac:=tmacro(search_macro(hs));
        if not assigned(mac) or
           (mac.owner <> current_module.localmacrosymtable) then
          begin
            mac:=tmacro.create(hs);
            mac.defined:=true;
            mac.is_compiler_var:=true;
            current_module.localmacrosymtable.insert(mac);
          end
        else
          begin
            mac.defined:=true;
            mac.is_compiler_var:=true;
          { delete old definition }
            if assigned(mac.buftext) then
             begin
               freemem(mac.buftext,mac.buflen);
               mac.buftext:=nil;
             end;
          end;
        Message1(parser_c_macro_defined,mac.name);
        mac.is_used:=true;

        { key words are never substituted }
        if is_keyword(hs) then
          Message(scan_e_keyword_cant_be_a_macro);

        { macro assignment can be both := and = }
        current_scanner.skipspace;
        if c=':' then
          current_scanner.readchar;
        if c='=' then
          begin
             current_scanner.readchar;
             hs:= parse_compiler_expr(exprType);
             if (exprType * [ctetBoolean, ctetInteger]) = [] then
               CTEError(exprType, [ctetBoolean, ctetInteger], 'SETC');

             if length(hs) <> 0 then
               begin
                 {If we are absolutely shure it is boolean, translate
                  to TRUE/FALSE to increase possibility to do future type check}
                 if exprType = [ctetBoolean] then
                   begin
                     val(hs,l,w);
                     if l<>0 then
                       hs:='TRUE'
                     else
                       hs:='FALSE';
                   end;
                 Message2(parser_c_macro_set_to,mac.name,hs);
                 { free buffer of macro ?}
                 if assigned(mac.buftext) then
                   freemem(mac.buftext,mac.buflen);
                 { get new mem }
                 getmem(mac.buftext,length(hs));
                 mac.buflen:=length(hs);
                 { copy the text }
                 move(hs[1],mac.buftext^,mac.buflen);
               end
             else
               Message(scan_e_preproc_syntax_error);
          end
        else
          Message(scan_e_preproc_syntax_error);
      end;


    procedure dir_undef;
      var
        hs  : string;
        mac : tmacro;
      begin
        current_scanner.skipspace;
        hs:=current_scanner.readid;
        mac:=tmacro(search_macro(hs));
        if not assigned(mac) or
           (mac.owner <> current_module.localmacrosymtable) then
          begin
             mac:=tmacro.create(hs);
             mac.defined:=false;
             current_module.localmacrosymtable.insert(mac);
          end
        else
          begin
             mac.defined:=false;
             mac.is_compiler_var:=false;
             { delete old definition }
             if assigned(mac.buftext) then
               begin
                  freemem(mac.buftext,mac.buflen);
                  mac.buftext:=nil;
               end;
          end;
        Message1(parser_c_macro_undefined,mac.name);
        mac.is_used:=true;
      end;

    procedure dir_include;

        function findincludefile(const path,name:TCmdStr;var foundfile:TCmdStr):boolean;
        var
          found  : boolean;
          hpath  : TCmdStr;
        begin
          (* look for the include file
           If path was absolute and specified as part of {$I } then
            1. specified path
           else
            1. path of current inputfile,current dir
            2. local includepath
            3. global includepath

            -- Check mantis #13461 before changing this *)
           found:=false;
           foundfile:='';
           hpath:='';
           if path_absolute(path) then
             begin
               found:=FindFile(name,path,true,foundfile);
             end
           else
             begin
               hpath:=current_scanner.inputfile.path+';'+CurDirRelPath(source_info);
               found:=FindFile(path+name, hpath,true,foundfile);
               if not found then
                 found:=current_module.localincludesearchpath.FindFile(path+name,true,foundfile);
               if not found  then
                 found:=includesearchpath.FindFile(path+name,true,foundfile);
             end;
           result:=found;
        end;

      var
        foundfile : TCmdStr;
        path,
        name,
        hs    : tpathstr;
        args  : string;
        hp    : tinputfile;
        found : boolean;
        macroIsString : boolean;
      begin
        current_scanner.skipspace;
        args:=current_scanner.readcomment;
        hs:=GetToken(args,' ');
        if hs='' then
         exit;
        if (hs[1]='%') then
         begin
         { case insensitive }
           hs:=upper(hs);
         { remove %'s }
           Delete(hs,1,1);
           if hs[length(hs)]='%' then
            Delete(hs,length(hs),1);
         { save old }
           path:=hs;
         { first check for internal macros }
           macroIsString:=true;
           if hs='TIME' then
            hs:=gettimestr
           else
            if hs='DATE' then
             hs:=getdatestr
           else
            if hs='FILE' then
             hs:=current_module.sourcefiles.get_file_name(current_filepos.fileindex)
           else
            if hs='LINE' then
             hs:=tostr(current_filepos.line)
           else
            if hs='LINENUM' then
              begin
                hs:=tostr(current_filepos.line);
                macroIsString:=false;
              end
           else
            if hs='FPCVERSION' then
             hs:=version_string
           else
            if hs='FPCDATE' then
             hs:=date_string
           else
            if hs='FPCTARGET' then
             hs:=target_cpu_string
           else
            if hs='FPCTARGETCPU' then
             hs:=target_cpu_string
           else
            if hs='FPCTARGETOS' then
             hs:=target_info.shortname
           else
             hs:=GetEnvironmentVariable(hs);
           if hs='' then
            Message1(scan_w_include_env_not_found,path);
           { make it a stringconst }
           if macroIsString then
             hs:=''''+hs+'''';
           current_scanner.substitutemacro(path,@hs[1],length(hs),
             current_scanner.line_no,current_scanner.inputfile.ref_index);
         end
        else
         begin
           hs:=FixFileName(hs);
           path:=ExtractFilePath(hs);
           name:=ExtractFileName(hs);
           { Special case for Delphi compatibility: '*' has to be replaced
             by the file name of the current source file.  }
           if (length(name)>=1) and
              (name[1]='*') then
             name:=ChangeFileExt(current_module.sourcefiles.get_file_name(current_filepos.fileindex),'')+ExtractFileExt(name);

           { try to find the file }
           found:=findincludefile(path,name,foundfile);
           if (ExtractFileExt(name)='') then
            begin
              { try default extensions .inc , .pp and .pas }
              if (not found) then
               found:=findincludefile(path,ChangeFileExt(name,'.inc'),foundfile);
              if (not found) then
               found:=findincludefile(path,ChangeFileExt(name,sourceext),foundfile);
              if (not found) then
               found:=findincludefile(path,ChangeFileExt(name,pasext),foundfile);
            end;
           if current_scanner.inputfilecount<max_include_nesting then
             begin
               inc(current_scanner.inputfilecount);
               { we need to reread the current char }
               dec(current_scanner.inputpointer);
               { shutdown current file }
               current_scanner.tempcloseinputfile;
               { load new file }
               hp:=do_openinputfile(foundfile);
               current_scanner.addfile(hp);
               current_module.sourcefiles.register_file(hp);
               if (not found) then
                Message1(scan_f_cannot_open_includefile,hs);
              if (not current_scanner.openinputfile) then
                Message1(scan_f_cannot_open_includefile,hs);
               Message1(scan_t_start_include_file,current_scanner.inputfile.path+current_scanner.inputfile.name);
               current_scanner.reload;
             end
           else
             Message(scan_f_include_deep_ten);
         end;
      end;


{*****************************************************************************
                            Preprocessor writing
*****************************************************************************}

{$ifdef PREPROCWRITE}
    constructor tpreprocfile.create(const fn:string);
      begin
      { open outputfile }
        assign(f,fn);
        {$push}{$I-}
         rewrite(f);
        {$pop}
        if ioresult<>0 then
         Comment(V_Fatal,'can''t create file '+fn);
        getmem(buf,preprocbufsize);
        settextbuf(f,buf^,preprocbufsize);
      { reset }
        eolfound:=false;
        spacefound:=false;
      end;


    destructor tpreprocfile.destroy;
      begin
        close(f);
        freemem(buf,preprocbufsize);
      end;


    procedure tpreprocfile.add(const s:string);
      begin
        write(f,s);
      end;

    procedure tpreprocfile.addspace;
      begin
        if eolfound then
         begin
           writeln(f,'');
           eolfound:=false;
           spacefound:=false;
         end
        else
         if spacefound then
          begin
            write(f,' ');
            spacefound:=false;
          end;
      end;
{$endif PREPROCWRITE}


{*****************************************************************************
                              TPreProcStack
*****************************************************************************}

    constructor tpreprocstack.create(atyp : preproctyp;a:boolean;n:tpreprocstack);
      begin
        accept:=a;
        typ:=atyp;
        next:=n;
      end;

{*****************************************************************************
                              TReplayStack
*****************************************************************************}
    constructor treplaystack.Create(atoken:ttoken;asettings:tsettings;
      atokenbuf:tdynamicarray;anext:treplaystack;achange_endian : boolean);
      begin
        token:=atoken;
        settings:=asettings;
        tokenbuf:=atokenbuf;
        change_endian:=achange_endian;
        next:=anext;
      end;

{*****************************************************************************
                              TDirectiveItem
*****************************************************************************}

    constructor TDirectiveItem.Create(AList:TFPHashObjectList;const n:string;p:tdirectiveproc);
      begin
        inherited Create(AList,n);
        is_conditional:=false;
        proc:=p;
      end;


    constructor TDirectiveItem.CreateCond(AList:TFPHashObjectList;const n:string;p:tdirectiveproc);
      begin
        inherited Create(AList,n);
        is_conditional:=true;
        proc:=p;
      end;

{****************************************************************************
                                TSCANNERFILE
 ****************************************************************************}

    constructor tscannerfile.create(const fn:string; is_macro: boolean = false);
      begin
        inputfile:=do_openinputfile(fn);
        if is_macro then
          inputfile.is_macro:=true;
        if assigned(current_module) then
          current_module.sourcefiles.register_file(inputfile);
      { reset localinput }
        c:=#0;
        inputbuffer:=nil;
        inputpointer:=nil;
        inputstart:=0;
      { reset scanner }
        preprocstack:=nil;
        replaystack:=nil;
        tokenbuf_change_endian:=false;
        comment_level:=0;
        yylexcount:=0;
        block_type:=bt_general;
        line_no:=0;
        lastlinepos:=0;
        lasttokenpos:=0;
        nexttokenpos:=0;
        lasttoken:=NOTOKEN;
        nexttoken:=NOTOKEN;
        lastasmgetchar:=#0;
        ignoredirectives:=TFPHashList.Create;
        in_asm_string:=false;
      end;


    procedure tscannerfile.firstfile;
      begin
      { load block }
        if not openinputfile then
          Message1(scan_f_cannot_open_input,inputfile.name);
        reload;
      end;


    destructor tscannerfile.destroy;
      begin
        if assigned(current_module) and
           (current_module.state=ms_compiled) and
           (status.errorcount=0) then
          checkpreprocstack
        else
          begin
            while assigned(preprocstack) do
             poppreprocstack;
          end;
        while assigned(replaystack) do
          popreplaystack;
        if not inputfile.closed then
          closeinputfile;
        if inputfile.is_macro then
          inputfile.free;
        ignoredirectives.free;
      end;


    function tscannerfile.openinputfile:boolean;
      begin
        openinputfile:=inputfile.open;
      { load buffer }
        inputbuffer:=inputfile.buf;
        inputpointer:=inputfile.buf;
        inputstart:=inputfile.bufstart;
      { line }
        line_no:=0;
        lastlinepos:=0;
        lasttokenpos:=0;
        nexttokenpos:=0;
      end;


    procedure tscannerfile.closeinputfile;
      begin
        inputfile.close;
      { reset buffer }
        inputbuffer:=nil;
        inputpointer:=nil;
        inputstart:=0;
      { reset line }
        line_no:=0;
        lastlinepos:=0;
        lasttokenpos:=0;
        nexttokenpos:=0;
      end;


    function tscannerfile.tempopeninputfile:boolean;
      begin
        if inputfile.is_macro then
          exit;
        tempopeninputfile:=inputfile.tempopen;
      { reload buffer }
        inputbuffer:=inputfile.buf;
        inputpointer:=inputfile.buf;
        inputstart:=inputfile.bufstart;
      end;


    procedure tscannerfile.tempcloseinputfile;
      begin
        if inputfile.closed or inputfile.is_macro then
         exit;
        inputfile.setpos(inputstart+(inputpointer-inputbuffer));
        inputfile.tempclose;
      { reset buffer }
        inputbuffer:=nil;
        inputpointer:=nil;
        inputstart:=0;
      end;


    procedure tscannerfile.saveinputfile;
      begin
        inputfile.saveinputpointer:=inputpointer;
        inputfile.savelastlinepos:=lastlinepos;
        inputfile.saveline_no:=line_no;
      end;


    procedure tscannerfile.restoreinputfile;
      begin
        inputbuffer:=inputfile.buf;
        inputpointer:=inputfile.saveinputpointer;
        lastlinepos:=inputfile.savelastlinepos;
        line_no:=inputfile.saveline_no;
        if not inputfile.is_macro then
          parser_current_file:=inputfile.name;
      end;


    procedure tscannerfile.nextfile;
      var
        to_dispose : tinputfile;
      begin
        if assigned(inputfile.next) then
         begin
           if inputfile.is_macro then
             to_dispose:=inputfile
           else
             begin
               to_dispose:=nil;
               dec(inputfilecount);
             end;
           { we can allways close the file, no ? }
           inputfile.close;
           inputfile:=inputfile.next;
           if assigned(to_dispose) then
             to_dispose.free;
           restoreinputfile;
         end;
      end;


    procedure tscannerfile.startrecordtokens(buf:tdynamicarray);
      begin
        if not assigned(buf) then
          internalerror(200511172);
        if assigned(recordtokenbuf) then
          internalerror(200511173);
        recordtokenbuf:=buf;
        fillchar(last_settings,sizeof(last_settings),0);
        last_message:=nil;
        fillchar(last_filepos,sizeof(last_filepos),0);
      end;


    procedure tscannerfile.stoprecordtokens;
      begin
        if not assigned(recordtokenbuf) then
          internalerror(200511174);
        recordtokenbuf:=nil;
      end;


    procedure tscannerfile.writetoken(t : ttoken);
      var
        b : byte;
      begin
        if ord(t)>$7f then
          begin
            b:=(ord(t) shr 8) or $80;
            recordtokenbuf.write(b,1);
          end;
        b:=ord(t) and $ff;
        recordtokenbuf.write(b,1);
      end;

    procedure tscannerfile.tokenwritesizeint(val : sizeint);
      begin
        recordtokenbuf.write(val,sizeof(sizeint));
      end;

    function tscannerfile.tokenreadsizeint : sizeint;
      var
        val : sizeint;
      begin
        replaytokenbuf.read(val,sizeof(sizeint));
        if tokenbuf_change_endian then
          val:=swapendian(val);
        result:=val;
      end;

    function tscannerfile.tokenreadlongword : longword;
      var
        val : longword;
      begin
        replaytokenbuf.read(val,sizeof(longword));
        if tokenbuf_change_endian then
          val:=swapendian(val);
        result:=val;
      end;

    function tscannerfile.tokenreadlongint : longint;
      var
        val : longint;
      begin
        replaytokenbuf.read(val,sizeof(longint));
        if tokenbuf_change_endian then
          val:=swapendian(val);
        result:=val;
      end;

    function tscannerfile.tokenreadshortint : shortint;
      var
        val : shortint;
      begin
        replaytokenbuf.read(val,sizeof(shortint));
        result:=val;
      end;

    function tscannerfile.tokenreadbyte : byte;
      var
        val : byte;
      begin
        replaytokenbuf.read(val,sizeof(byte));
        result:=val;
      end;

    function tscannerfile.tokenreadsmallint : smallint;
      var
        val : smallint;
      begin
        replaytokenbuf.read(val,sizeof(smallint));
        if tokenbuf_change_endian then
          val:=swapendian(val);
        result:=val;
      end;

    function tscannerfile.tokenreadword : word;
      var
        val : word;
      begin
        replaytokenbuf.read(val,sizeof(word));
        if tokenbuf_change_endian then
          val:=swapendian(val);
        result:=val;
      end;

   function tscannerfile.tokenreadenum(size : longint) : longword;
   begin
     if size=1 then
       result:=tokenreadbyte
     else if size=2 then
       result:=tokenreadword
     else if size=4 then
       result:=tokenreadlongword;
   end;

   procedure tscannerfile.tokenreadset(var b;size : longint);
   var
     i : longint;
   begin
     replaytokenbuf.read(b,size);
     if tokenbuf_change_endian then
       for i:=0 to size-1 do
         Pbyte(@b)[i]:=reverse_byte(Pbyte(@b)[i]);
   end;


    procedure tscannerfile.tokenreadsettings(var asettings : tsettings; expected_size : longint);

    {    This procedure
       needs to be changed whenever
       globals.tsettings type is changed,
       the problem is that no error will appear
       before tests with generics are tested. PM }

       var
         startpos, endpos : longword;
      begin
        { WARNING all those fields need to be in the correct
        order otherwise cross_endian PPU reading will fail }
        startpos:=replaytokenbuf.pos;
        with asettings do
          begin
            alignment.procalign:=tokenreadlongint;
            alignment.loopalign:=tokenreadlongint;
            alignment.jumpalign:=tokenreadlongint;
            alignment.constalignmin:=tokenreadlongint;
            alignment.constalignmax:=tokenreadlongint;
            alignment.varalignmin:=tokenreadlongint;
            alignment.varalignmax:=tokenreadlongint;
            alignment.localalignmin:=tokenreadlongint;
            alignment.localalignmax:=tokenreadlongint;
            alignment.recordalignmin:=tokenreadlongint;
            alignment.recordalignmax:=tokenreadlongint;
            alignment.maxCrecordalign:=tokenreadlongint;
            tokenreadset(globalswitches,sizeof(globalswitches));
            tokenreadset(targetswitches,sizeof(targetswitches));
            tokenreadset(moduleswitches,sizeof(moduleswitches));
            tokenreadset(localswitches,sizeof(localswitches));
            tokenreadset(modeswitches,sizeof(modeswitches));
            tokenreadset(optimizerswitches,sizeof(optimizerswitches));
            tokenreadset(genwpoptimizerswitches,sizeof(genwpoptimizerswitches));
            tokenreadset(dowpoptimizerswitches,sizeof(dowpoptimizerswitches));
            tokenreadset(debugswitches,sizeof(debugswitches));
            { 0: old behaviour for sets <=256 elements
              >0: round to this size }
            setalloc:=tokenreadshortint;
            packenum:=tokenreadshortint;

            packrecords:=tokenreadshortint;
            maxfpuregisters:=tokenreadshortint;


            cputype:=tcputype(tokenreadenum(sizeof(tcputype)));
            optimizecputype:=tcputype(tokenreadenum(sizeof(tcputype)));
            fputype:=tfputype(tokenreadenum(sizeof(tfputype)));
            asmmode:=tasmmode(tokenreadenum(sizeof(tasmmode)));
            interfacetype:=tinterfacetypes(tokenreadenum(sizeof(tinterfacetypes)));
            defproccall:=tproccalloption(tokenreadenum(sizeof(tproccalloption)));
            { tstringencoding is word type,
              thus this should be OK here }
            sourcecodepage:=tstringEncoding(tokenreadword);

            minfpconstprec:=tfloattype(tokenreadenum(sizeof(tfloattype)));

            disabledircache:=boolean(tokenreadbyte);
{$if defined(ARM) or defined(AVR)}
            controllertype:=tcontrollertype(tokenreadenum(sizeof(tcontrollertype)));
{$endif defined(ARM) or defined(AVR)}
           endpos:=replaytokenbuf.pos;
           if endpos-startpos<>expected_size then
             Comment(V_Error,'Wrong size of Settings read-in');
         end;
     end;


    procedure tscannerfile.recordtoken;
      var
        t : ttoken;
        s : tspecialgenerictoken;
        len,val,msgnb,copy_size : sizeint;
        b : byte;
        pmsg : pmessagestaterecord;
      begin
        if not assigned(recordtokenbuf) then
          internalerror(200511176);
        t:=_GENERICSPECIALTOKEN;
        { settings changed? }
        { last field pmessage is handled separately below in
          ST_LOADMESSAGES }
        if CompareByte(current_settings,last_settings,
             sizeof(current_settings)-sizeof(pointer))<>0 then
          begin
            { use a special token to record it }
            s:=ST_LOADSETTINGS;
            writetoken(t);
            recordtokenbuf.write(s,1);
            copy_size:=sizeof(current_settings)-sizeof(pointer);
            tokenwritesizeint(copy_size);
            recordtokenbuf.write(current_settings,copy_size);
            last_settings:=current_settings;
          end;

        if current_settings.pmessage<>last_message then
          begin
            { use a special token to record it }
            s:=ST_LOADMESSAGES;
            writetoken(t);
            recordtokenbuf.write(s,1);
            msgnb:=0;
            pmsg:=current_settings.pmessage;
            while assigned(pmsg) do
              begin
                if msgnb=high(sizeint) then
                  { Too many messages }
                  internalerror(2011090401);
                inc(msgnb);
                pmsg:=pmsg^.next;
              end;
            tokenwritesizeint(msgnb);
            pmsg:=current_settings.pmessage;
            while assigned(pmsg) do
              begin
                { What about endianess here? }
                val:=pmsg^.value;
                tokenwritesizeint(val);
                val:=ord(pmsg^.state);
                tokenwritesizeint(val);
                pmsg:=pmsg^.next;
              end;
            last_message:=current_settings.pmessage;
          end;

        { file pos changes? }
        if current_tokenpos.line<>last_filepos.line then
          begin
            s:=ST_LINE;
            writetoken(t);
            recordtokenbuf.write(s,1);
            recordtokenbuf.write(current_tokenpos.line,sizeof(current_tokenpos.line));
            last_filepos.line:=current_tokenpos.line;
          end;
        if current_tokenpos.column<>last_filepos.column then
          begin
            s:=ST_COLUMN;
            writetoken(t);
            { can the column be written packed? }
            if current_tokenpos.column<$80 then
              begin
                b:=$80 or current_tokenpos.column;
                recordtokenbuf.write(b,1);
              end
            else
              begin
                recordtokenbuf.write(s,1);
                recordtokenbuf.write(current_tokenpos.column,sizeof(current_tokenpos.column));
              end;
            last_filepos.column:=current_tokenpos.column;
          end;
        if current_tokenpos.fileindex<>last_filepos.fileindex then
          begin
            s:=ST_FILEINDEX;
            writetoken(t);
            recordtokenbuf.write(s,1);
            recordtokenbuf.write(current_tokenpos.fileindex,sizeof(current_tokenpos.fileindex));
            last_filepos.fileindex:=current_tokenpos.fileindex;
          end;

        writetoken(token);
        if token<>_GENERICSPECIALTOKEN then
          writetoken(idtoken);
        case token of
          _CWCHAR,
          _CWSTRING :
            begin
              tokenwritesizeint(patternw^.len);
              recordtokenbuf.write(patternw^.data^,patternw^.len*sizeof(tcompilerwidechar));
            end;
          _CSTRING:
            begin
              len:=length(cstringpattern);
              tokenwritesizeint(len);
              recordtokenbuf.write(cstringpattern[1],length(cstringpattern));
            end;
          _CCHAR,
          _INTCONST,
          _REALNUMBER :
            begin
              { pexpr.pas messes with pattern in case of negative integer consts,
                see around line 2562 the comment of JM; remove the - before recording it
                                                     (FK)
              }
              if (token=_INTCONST) and (pattern[1]='-') then
                delete(pattern,1,1);
              recordtokenbuf.write(pattern[0],1);
              recordtokenbuf.write(pattern[1],length(pattern));
            end;
          _ID :
            begin
              recordtokenbuf.write(orgpattern[0],1);
              recordtokenbuf.write(orgpattern[1],length(orgpattern));
            end;
        end;
      end;


    procedure tscannerfile.startreplaytokens(buf:tdynamicarray; achange_endian : boolean);
      begin
        if not assigned(buf) then
          internalerror(200511175);
        { save current token }
        if token in [_CWCHAR,_CWSTRING,_CCHAR,_CSTRING,_INTCONST,_REALNUMBER,_ID] then
          internalerror(200511178);
        replaystack:=treplaystack.create(token,current_settings,
          replaytokenbuf,replaystack,tokenbuf_change_endian);
        if assigned(inputpointer) then
          dec(inputpointer);
        { install buffer }
        replaytokenbuf:=buf;
        tokenbuf_change_endian:=achange_endian;

        { reload next token }
        replaytokenbuf.seek(0);
        replaytoken;
      end;


    function tscannerfile.readtoken: ttoken;
      var
        b,b2 : byte;
      begin
        replaytokenbuf.read(b,1);
        if (b and $80)<>0 then
          begin
            replaytokenbuf.read(b2,1);
            result:=ttoken(((b and $7f) shl 8) or b2);
          end
        else
          result:=ttoken(b);
      end;


    procedure tscannerfile.replaytoken;
      var
        wlen,mesgnb,copy_size : sizeint;
        specialtoken : tspecialgenerictoken;
        i : byte;
        pmsg,prevmsg : pmessagestaterecord;
      begin
        if not assigned(replaytokenbuf) then
          internalerror(200511177);
        { End of replay buffer? Then load the next char from the file again }
        if replaytokenbuf.pos>=replaytokenbuf.size then
          begin
            token:=replaystack.token;
            replaytokenbuf:=replaystack.tokenbuf;
            { restore compiler settings }
            current_settings:=replaystack.settings;
            popreplaystack;
            if assigned(inputpointer) then
              begin
                c:=inputpointer^;
                inc(inputpointer);
              end;
            exit;
          end;
        repeat
          { load token from the buffer }
          token:=readtoken;
          if token<>_GENERICSPECIALTOKEN then
            idtoken:=readtoken
          else
            idtoken:=_NOID;
          case token of
            _CWCHAR,
            _CWSTRING :
              begin
                wlen:=tokenreadsizeint;
                setlengthwidestring(patternw,wlen);
                replaytokenbuf.read(patternw^.data^,patternw^.len*sizeof(tcompilerwidechar));
                orgpattern:='';
                pattern:='';
                cstringpattern:='';
              end;
            _CSTRING:
              begin
                wlen:=tokenreadsizeint;
                setlength(cstringpattern,wlen);
                replaytokenbuf.read(cstringpattern[1],wlen);
                orgpattern:='';
                pattern:='';
              end;
            _CCHAR,
            _INTCONST,
            _REALNUMBER :
              begin
                replaytokenbuf.read(pattern[0],1);
                replaytokenbuf.read(pattern[1],length(pattern));
                orgpattern:='';
              end;
            _ID :
              begin
                replaytokenbuf.read(orgpattern[0],1);
                replaytokenbuf.read(orgpattern[1],length(orgpattern));
                pattern:=upper(orgpattern);
              end;
            _GENERICSPECIALTOKEN:
              begin
                replaytokenbuf.read(specialtoken,1);
                { packed column? }
                if (ord(specialtoken) and $80)<>0 then
                  begin
                      current_tokenpos.column:=ord(specialtoken) and $7f;

                      { don't generate invalid line info if no sources are available for the current module }
                      if not(get_module(current_filepos.moduleindex).sources_avail) then
                        current_tokenpos.column:=0;

                      current_filepos:=current_tokenpos;
                  end
                else
                  case specialtoken of
                    ST_LOADSETTINGS:
                      begin
                        copy_size:=tokenreadsizeint;
                        if copy_size <> sizeof(current_settings)-sizeof(pointer) then
                          internalerror(2011090501);
                        {
                        replaytokenbuf.read(current_settings,copy_size);
                        }
                        tokenreadsettings(current_settings,copy_size);
                      end;
                    ST_LOADMESSAGES:
                      begin
                        current_settings.pmessage:=nil;
                        mesgnb:=tokenreadsizeint;
                        if mesgnb>0 then
                          Comment(V_Error,'Message recordind not yet supported');
                        for i:=1 to mesgnb do
                          begin
                            new(pmsg);
                            if i=1 then
                              begin
                                current_settings.pmessage:=pmsg;
                                prevmsg:=nil;
                              end
                            else
                              prevmsg^.next:=pmsg;
                            replaytokenbuf.read(pmsg^.value,sizeof(longint));
                            replaytokenbuf.read(pmsg^.state,sizeof(tmsgstate));
                            pmsg^.next:=nil;
                            prevmsg:=pmsg;
                          end;
                      end;
                    ST_LINE:
                      begin
                        current_tokenpos.line:=tokenreadlongint;

                        { don't generate invalid line info if no sources are available for the current module }
                        if not(get_module(current_filepos.moduleindex).sources_avail) then
                          current_tokenpos.line:=0;

                        current_filepos:=current_tokenpos;
                      end;
                    ST_COLUMN:
                      begin
                        current_tokenpos.column:=tokenreadword;
                        { don't generate invalid line info if no sources are available for the current module }
                        if not(get_module(current_filepos.moduleindex).sources_avail) then
                          current_tokenpos.column:=0;

                        current_filepos:=current_tokenpos;
                      end;
                    ST_FILEINDEX:
                      begin
                        current_tokenpos.fileindex:=tokenreadword;
                        { don't generate invalid line info if no sources are available for the current module }
                        if not(get_module(current_filepos.moduleindex).sources_avail) then
                          begin
                            current_tokenpos.column:=0;
                            current_tokenpos.line:=0;
                          end;

                        current_filepos:=current_tokenpos;
                      end;
                    else
                      internalerror(2006103010);
                  end;
                continue;
              end;
          end;
          break;
        until false;
      end;


    procedure tscannerfile.addfile(hp:tinputfile);
      begin
        saveinputfile;
        { add to list }
        hp.next:=inputfile;
        inputfile:=hp;
        { load new inputfile }
        restoreinputfile;
      end;


    procedure tscannerfile.reload;
      begin
        with inputfile do
         begin
           { when nothing more to read then leave immediatly, so we
             don't change the current_filepos and leave it point to the last
             char }
           if (c=#26) and (not assigned(next)) then
            exit;
           repeat
           { still more to read?, then change the #0 to a space so its seen
             as a seperator, this can't be used for macro's which can change
             the place of the #0 in the buffer with tempopen }
             if (c=#0) and (bufsize>0) and
                not(inputfile.is_macro) and
                (inputpointer-inputbuffer<bufsize) then
              begin
                c:=' ';
                inc(inputpointer);
                exit;
              end;
           { can we read more from this file ? }
             if (c<>#26) and (not endoffile) then
              begin
                readbuf;
                inputpointer:=buf;
                inputbuffer:=buf;
                inputstart:=bufstart;
              { first line? }
                if line_no=0 then
                 begin
                   c:=inputpointer^;
                   { eat utf-8 signature? }
                   if (ord(inputpointer^)=$ef) and
                     (ord((inputpointer+1)^)=$bb) and
                     (ord((inputpointer+2)^)=$bf) then
                     begin
                       (* we don't support including files with an UTF-8 bom
                          inside another file that wasn't encoded as UTF-8
                          already (we don't support {$codepage xxx} switches in
                          the middle of a file either) *)
                       if (current_settings.sourcecodepage<>CP_UTF8) and
                          not current_module.in_global then
                         Message(scanner_f_illegal_utf8_bom);
                       inc(inputpointer,3);
                       message(scan_c_switching_to_utf8);
                       current_settings.sourcecodepage:=CP_UTF8;
                       include(current_settings.moduleswitches,cs_explicit_codepage);
                     end;

                   line_no:=1;
                   if cs_asm_source in current_settings.globalswitches then
                     inputfile.setline(line_no,inputstart+inputpointer-inputbuffer);
                 end;
              end
             else
              begin
              { load eof position in tokenpos/current_filepos }
                gettokenpos;
              { close file }
                closeinputfile;
              { no next module, than EOF }
                if not assigned(inputfile.next) then
                 begin
                   c:=#26;
                   exit;
                 end;
              { load next file and reopen it }
                nextfile;
                tempopeninputfile;
              { status }
                Message1(scan_t_back_in,inputfile.name);
              end;
           { load next char }
             c:=inputpointer^;
             inc(inputpointer);
           until c<>#0; { if also end, then reload again }
         end;
      end;


    procedure tscannerfile.substitutemacro(const macname:string;p:pchar;len,line,fileindex:longint);
      var
        hp : tinputfile;
      begin
        { save old postion }
        dec(inputpointer);
        tempcloseinputfile;
      { create macro 'file' }
        { use special name to dispose after !! }
        hp:=do_openinputfile('_Macro_.'+macname);
        addfile(hp);
        with inputfile do
         begin
           setmacro(p,len);
         { local buffer }
           inputbuffer:=buf;
           inputpointer:=buf;
           inputstart:=bufstart;
           ref_index:=fileindex;
         end;
      { reset line }
        line_no:=line;
        lastlinepos:=0;
        lasttokenpos:=0;
        nexttokenpos:=0;
      { load new c }
        c:=inputpointer^;
        inc(inputpointer);
      end;


    procedure tscannerfile.do_gettokenpos(out tokenpos: longint; out filepos: tfileposinfo);
      begin
        tokenpos:=inputstart+(inputpointer-inputbuffer);
        filepos.line:=line_no;
        filepos.column:=tokenpos-lastlinepos;
        filepos.fileindex:=inputfile.ref_index;
        filepos.moduleindex:=current_module.unit_index;
      end;


    procedure tscannerfile.gettokenpos;
    { load the values of tokenpos and lasttokenpos }
      begin
        do_gettokenpos(lasttokenpos,current_tokenpos);
        current_filepos:=current_tokenpos;
      end;


    procedure tscannerfile.cachenexttokenpos;
      begin
        do_gettokenpos(nexttokenpos,next_filepos);
      end;


    procedure tscannerfile.setnexttoken;
      begin
        token:=nexttoken;
        nexttoken:=NOTOKEN;
        lasttokenpos:=nexttokenpos;
        current_tokenpos:=next_filepos;
        current_filepos:=current_tokenpos;
        nexttokenpos:=0;
      end;


    procedure tscannerfile.savetokenpos;
      begin
        oldlasttokenpos:=lasttokenpos;
        oldcurrent_filepos:=current_filepos;
        oldcurrent_tokenpos:=current_tokenpos;
      end;


    procedure tscannerfile.restoretokenpos;
      begin
        lasttokenpos:=oldlasttokenpos;
        current_filepos:=oldcurrent_filepos;
        current_tokenpos:=oldcurrent_tokenpos;
      end;


    procedure tscannerfile.inc_comment_level;
      begin
         if (m_nested_comment in current_settings.modeswitches) then
           inc(comment_level)
         else
           comment_level:=1;
         if (comment_level>1) then
          begin
             savetokenpos;
             gettokenpos; { update for warning }
             Message1(scan_w_comment_level,tostr(comment_level));
             restoretokenpos;
          end;
      end;


    procedure tscannerfile.dec_comment_level;
      begin
         if (m_nested_comment in current_settings.modeswitches) then
           dec(comment_level)
         else
           comment_level:=0;
      end;


    procedure tscannerfile.linebreak;
      var
         cur : char;
      begin
        with inputfile do
         begin
           if (byte(inputpointer^)=0) and not(endoffile) then
             begin
               cur:=c;
               reload;
               if byte(cur)+byte(c)<>23 then
                 dec(inputpointer);
             end
           else
             begin
               { Support all combination of #10 and #13 as line break }
               if (byte(inputpointer^)+byte(c)=23) then
                 inc(inputpointer);
             end;
           { Always return #10 as line break }
           c:=#10;
           { increase line counters }
           lastlinepos:=inputstart+(inputpointer-inputbuffer);
           inc(line_no);
           { update linebuffer }
           if cs_asm_source in current_settings.globalswitches then
             inputfile.setline(line_no,lastlinepos);
           { update for status and call the show status routine,
             but don't touch current_filepos ! }
           savetokenpos;
           gettokenpos; { update for v_status }
           inc(status.compiledlines);
           ShowStatus;
           restoretokenpos;
         end;
      end;


    procedure tscannerfile.illegal_char(c:char);
      var
        s : string;
      begin
        if c in [#32..#255] then
          s:=''''+c+''''
        else
          s:='#'+tostr(ord(c));
        Message2(scan_f_illegal_char,s,'$'+hexstr(ord(c),2));
      end;


    procedure tscannerfile.end_of_file;
      begin
        checkpreprocstack;
        Message(scan_f_end_of_file);
      end;

  {-------------------------------------------
           IF Conditional Handling
  -------------------------------------------}

    procedure tscannerfile.checkpreprocstack;
      begin
      { check for missing ifdefs }
        while assigned(preprocstack) do
         begin
           Message4(scan_e_endif_expected,preprocstring[preprocstack.typ],preprocstack.name,
             preprocstack.owner.inputfile.name,tostr(preprocstack.line_nb));
           poppreprocstack;
         end;
      end;


    procedure tscannerfile.poppreprocstack;
      var
        hp : tpreprocstack;
      begin
        if assigned(preprocstack) then
         begin
           Message1(scan_c_endif_found,preprocstack.name);
           hp:=preprocstack.next;
           preprocstack.free;
           preprocstack:=hp;
         end
        else
         Message(scan_e_endif_without_if);
      end;


    procedure tscannerfile.ifpreprocstack(atyp : preproctyp;compile_time_predicate:tcompile_time_predicate;messid:longint);
      var
        condition: Boolean;
        valuedescr: String;
      begin
        if (preprocstack=nil) or preprocstack.accept then
          condition:= compile_time_predicate(valuedescr)
        else
          begin
            condition:= false;
            valuedescr:= '';
          end;
        preprocstack:=tpreprocstack.create(atyp, condition, preprocstack);
        preprocstack.name:=valuedescr;
        preprocstack.line_nb:=line_no;
        preprocstack.owner:=self;
        if preprocstack.accept then
          Message2(messid,preprocstack.name,'accepted')
        else
          Message2(messid,preprocstack.name,'rejected');
      end;

    procedure tscannerfile.elsepreprocstack;
      begin
        if assigned(preprocstack) and
           (preprocstack.typ<>pp_else) then
         begin
           if (preprocstack.typ=pp_elseif) then
             preprocstack.accept:=false
           else
             if (not(assigned(preprocstack.next)) or (preprocstack.next.accept)) then
               preprocstack.accept:=not preprocstack.accept;
           preprocstack.typ:=pp_else;
           preprocstack.line_nb:=line_no;
           if preprocstack.accept then
            Message2(scan_c_else_found,preprocstack.name,'accepted')
           else
            Message2(scan_c_else_found,preprocstack.name,'rejected');
         end
        else
         Message(scan_e_endif_without_if);
      end;

    procedure tscannerfile.elseifpreprocstack(compile_time_predicate:tcompile_time_predicate);
      var
        valuedescr: String;
      begin
        if assigned(preprocstack) and
           (preprocstack.typ in [pp_if,pp_elseif]) then
         begin
           { when the branch is accepted we use pp_elseif so we know that
             all the next branches need to be rejected. when this branch is still
             not accepted then leave it at pp_if }
           if (preprocstack.typ=pp_elseif) then
             preprocstack.accept:=false
           else if (preprocstack.typ=pp_if) and preprocstack.accept then
               begin
                 preprocstack.accept:=false;
                 preprocstack.typ:=pp_elseif;
               end
           else if (not(assigned(preprocstack.next)) or (preprocstack.next.accept))
                   and compile_time_predicate(valuedescr) then
               begin
                 preprocstack.name:=valuedescr;
                 preprocstack.accept:=true;
                 preprocstack.typ:=pp_elseif;
               end;

           preprocstack.line_nb:=line_no;
           if preprocstack.accept then
             Message2(scan_c_else_found,preprocstack.name,'accepted')
           else
             Message2(scan_c_else_found,preprocstack.name,'rejected');
         end
        else
         Message(scan_e_endif_without_if);
      end;


    procedure tscannerfile.popreplaystack;
      var
        hp : treplaystack;
      begin
        if assigned(replaystack) then
         begin
           hp:=replaystack.next;
           replaystack.free;
           replaystack:=hp;
           if assigned (replaystack) then
             tokenbuf_change_endian:=replaystack.change_endian
           else
             tokenbuf_change_endian:=false;
         end;
      end;

    procedure tscannerfile.handleconditional(p:tdirectiveitem);
      begin
        savetokenpos;
        repeat
          current_scanner.gettokenpos;
          Message1(scan_d_handling_switch,'$'+p.name);
          p.proc();
          { accept the text ? }
          if (current_scanner.preprocstack=nil) or current_scanner.preprocstack.accept then
           break
          else
           begin
             current_scanner.gettokenpos;
             Message(scan_c_skipping_until);
             repeat
               current_scanner.skipuntildirective;
               if not (m_mac in current_settings.modeswitches) then
                 p:=tdirectiveitem(turbo_scannerdirectives.Find(current_scanner.readid))
               else
                 p:=tdirectiveitem(mac_scannerdirectives.Find(current_scanner.readid));
             until assigned(p) and (p.is_conditional);
             current_scanner.gettokenpos;
           end;
        until false;
        restoretokenpos;
      end;


    procedure tscannerfile.handledirectives;
      var
         t  : tdirectiveitem;
         hs : string;
      begin
         gettokenpos;
         readchar; {Remove the $}
         hs:=readid;
         { handle empty directive }
         if hs='' then
           begin
             Message1(scan_w_illegal_switch,'$');
             exit;
           end;
{$ifdef PREPROCWRITE}
         if parapreprocess then
          begin
            t:=Get_Directive(hs);
            if not(is_conditional(t) or (t=_DIR_DEFINE) or (t=_DIR_UNDEF)) then
             begin
               preprocfile^.AddSpace;
               preprocfile^.Add('{$'+hs+current_scanner.readcomment+'}');
               exit;
             end;
          end;
{$endif PREPROCWRITE}
         { skip this directive? }
         if (ignoredirectives.find(hs)<>nil) then
          begin
            if (comment_level>0) then
             readcomment;
            { we've read the whole comment }
            aktcommentstyle:=comment_none;
            exit;
          end;
         { Check for compiler switches }
         while (length(hs)=1) and (c in ['-','+']) do
          begin
            Message1(scan_d_handling_switch,'$'+hs+c);
            HandleSwitch(hs[1],c);
            current_scanner.readchar; {Remove + or -}
            if c=',' then
             begin
               current_scanner.readchar;   {Remove , }
               { read next switch, support $v+,$+}
               hs:=current_scanner.readid;
               if (hs='') then
                begin
                  if (c='$') and (m_fpc in current_settings.modeswitches) then
                   begin
                     current_scanner.readchar;  { skip $ }
                     hs:=current_scanner.readid;
                   end;
                  if (hs='') then
                   Message1(scan_w_illegal_directive,'$'+c);
                end;
             end
            else
             hs:='';
          end;
         { directives may follow switches after a , }
         if hs<>'' then
          begin
            if not (m_mac in current_settings.modeswitches) then
              t:=tdirectiveitem(turbo_scannerdirectives.Find(hs))
            else
              t:=tdirectiveitem(mac_scannerdirectives.Find(hs));

            if assigned(t) then
             begin
               if t.is_conditional then
                handleconditional(t)
               else
                begin
                  Message1(scan_d_handling_switch,'$'+hs);
                  t.proc();
                end;
             end
            else
             begin
               current_scanner.ignoredirectives.Add(hs,nil);
               Message1(scan_w_illegal_directive,'$'+hs);
             end;
            { conditionals already read the comment }
            if (current_scanner.comment_level>0) then
             current_scanner.readcomment;
            { we've read the whole comment }
            aktcommentstyle:=comment_none;
          end;
      end;


    procedure tscannerfile.readchar;
      begin
        c:=inputpointer^;
        if c=#0 then
          reload
        else
          inc(inputpointer);
      end;


    procedure tscannerfile.readstring;
      var
        i : longint;
        err : boolean;
      begin
        err:=false;
        i:=0;
        repeat
          case c of
            '_',
            '0'..'9',
            'A'..'Z' :
              begin
                if i<255 then
                 begin
                   inc(i);
                   orgpattern[i]:=c;
                   pattern[i]:=c;
                 end
                else
                 begin
                   if not err then
                     begin
                       Message(scan_e_string_exceeds_255_chars);
                       err:=true;
                     end;
                 end;
                c:=inputpointer^;
                inc(inputpointer);
              end;
            'a'..'z' :
              begin
                if i<255 then
                 begin
                   inc(i);
                   orgpattern[i]:=c;
                   pattern[i]:=chr(ord(c)-32)
                 end
                else
                 begin
                   if not err then
                     begin
                       Message(scan_e_string_exceeds_255_chars);
                       err:=true;
                     end;
                 end;
                c:=inputpointer^;
                inc(inputpointer);
              end;
            #0 :
              reload;
            else
              break;
          end;
        until false;
        orgpattern[0]:=chr(i);
        pattern[0]:=chr(i);
      end;


    procedure tscannerfile.readnumber;
      var
        base,
        i  : longint;
      begin
        case c of
          '%' :
            begin
              readchar;
              base:=2;
              pattern[1]:='%';
              i:=1;
            end;
          '&' :
            begin
              readchar;
              base:=8;
              pattern[1]:='&';
              i:=1;
            end;
          '$' :
            begin
              readchar;
              base:=16;
              pattern[1]:='$';
              i:=1;
            end;
          else
            begin
              base:=10;
              i:=0;
            end;
        end;
        while ((base>=10) and (c in ['0'..'9'])) or
              ((base=16) and (c in ['A'..'F','a'..'f'])) or
              ((base=8) and (c in ['0'..'7'])) or
              ((base=2) and (c in ['0'..'1'])) do
         begin
           if i<255 then
            begin
              inc(i);
              pattern[i]:=c;
            end;
           readchar;
         end;
        pattern[0]:=chr(i);
      end;


    function tscannerfile.readid:string;
      begin
        readstring;
        readid:=pattern;
      end;


    function tscannerfile.readval:longint;
      var
        l : longint;
        w : integer;
      begin
        readnumber;
        val(pattern,l,w);
        readval:=l;
      end;


    function tscannerfile.readval_asstring:string;
      begin
        readnumber;
        readval_asstring:=pattern;
      end;


    function tscannerfile.readcomment:string;
      var
        i : longint;
      begin
        i:=0;
        repeat
          case c of
            '{' :
              begin
                if aktcommentstyle=comment_tp then
                  inc_comment_level;
              end;
            '}' :
              begin
                if aktcommentstyle=comment_tp then
                  begin
                    readchar;
                    dec_comment_level;
                    if comment_level=0 then
                      break
                    else
                      continue;
                  end;
              end;
            '*' :
              begin
                if aktcommentstyle=comment_oldtp then
                  begin
                    readchar;
                    if c=')' then
                      begin
                        readchar;
                        dec_comment_level;
                        break;
                      end
                    else
                    { Add both characters !!}
                      if (i<255) then
                        begin
                          inc(i);
                          readcomment[i]:='*';
                          if (i<255) then
                            begin
                              inc(i);
                              readcomment[i]:=c;
                            end;
                        end;
                  end
                else
                { Not old TP comment, so add...}
                  begin
                    if (i<255) then
                      begin
                        inc(i);
                        readcomment[i]:='*';
                      end;
                  end;
              end;
            #10,#13 :
              linebreak;
            #26 :
              end_of_file;
            else
              begin
                if (i<255) then
                  begin
                    inc(i);
                    readcomment[i]:=c;
                  end;
              end;
          end;
          readchar;
        until false;
        readcomment[0]:=chr(i);
      end;


    function tscannerfile.readquotedstring:string;
      var
        i : longint;
        msgwritten : boolean;
      begin
        i:=0;
        msgwritten:=false;
        if (c='''') then
          begin
            repeat
              readchar;
              case c of
                #26 :
                  end_of_file;
                #10,#13 :
                  Message(scan_f_string_exceeds_line);
                '''' :
                  begin
                    readchar;
                    if c<>'''' then
                     break;
                  end;
              end;
              if i<255 then
                begin
                  inc(i);
                  result[i]:=c;
                end
              else
                begin
                  if not msgwritten then
                    begin
                      Message(scan_e_string_exceeds_255_chars);
                      msgwritten:=true;
                    end;
                 end;
            until false;
          end;
        result[0]:=chr(i);
      end;


    function tscannerfile.readstate:char;
      var
        state : char;
      begin
        state:=' ';
        if c=' ' then
         begin
           current_scanner.skipspace;
           current_scanner.readid;
           if pattern='ON' then
            state:='+'
           else
            if pattern='OFF' then
             state:='-';
         end
        else
         state:=c;
        if not (state in ['+','-']) then
         Message(scan_e_wrong_switch_toggle);
        readstate:=state;
      end;


    function tscannerfile.readstatedefault:char;
      var
        state : char;
      begin
        state:=' ';
        if c=' ' then
         begin
           current_scanner.skipspace;
           current_scanner.readid;
           if pattern='ON' then
            state:='+'
           else
            if pattern='OFF' then
             state:='-'
            else
             if pattern='DEFAULT' then
              state:='*';
         end
        else
         state:=c;
        if not (state in ['+','-','*']) then
         Message(scan_e_wrong_switch_toggle_default);
        readstatedefault:=state;
      end;


    procedure tscannerfile.skipspace;
      begin
        repeat
          case c of
            #26 :
              begin
                reload;
                if (c=#26) and not assigned(inputfile.next) then
                  break;
                continue;
              end;
            #10,
            #13 :
              linebreak;
            #9,#11,#12,' ' :
              ;
            else
              break;
          end;
          readchar;
        until false;
      end;


    procedure tscannerfile.skipuntildirective;
      var
        found : longint;
        next_char_loaded : boolean;
      begin
         found:=0;
         next_char_loaded:=false;
         repeat
           case c of
             #10,
             #13 :
               linebreak;
             #26 :
               begin
                 reload;
                 if (c=#26) and not assigned(inputfile.next) then
                   end_of_file;
                 continue;
               end;
             '{' :
               begin
                 if (aktcommentstyle in [comment_tp,comment_none]) then
                   begin
                     aktcommentstyle:=comment_tp;
                     if (comment_level=0) then
                       found:=1;
                     inc_comment_level;
                   end;
               end;
             '*' :
               begin
                 if (aktcommentstyle=comment_oldtp) then
                   begin
                     readchar;
                     if c=')' then
                       begin
                         dec_comment_level;
                         found:=0;
                         aktcommentstyle:=comment_none;
                       end
                     else
                       next_char_loaded:=true;
                   end
                 else
                   found := 0;
               end;
             '}' :
               begin
                 if (aktcommentstyle=comment_tp) then
                   begin
                     dec_comment_level;
                     if (comment_level=0) then
                       aktcommentstyle:=comment_none;
                     found:=0;
                   end;
               end;
             '$' :
               begin
                 if found=1 then
                  found:=2;
               end;
             '''' :
               if (aktcommentstyle=comment_none) then
                begin
                  repeat
                    readchar;
                    case c of
                      #26 :
                        end_of_file;
                      #10,#13 :
                        break;
                      '''' :
                        begin
                          readchar;
                          if c<>'''' then
                           begin
                             next_char_loaded:=true;
                             break;
                           end;
                        end;
                    end;
                  until false;
                end;
             '(' :
               begin
                 if (aktcommentstyle=comment_none) then
                  begin
                    readchar;
                    if c='*' then
                     begin
                       readchar;
                       if c='$' then
                        begin
                          found:=2;
                          inc_comment_level;
                          aktcommentstyle:=comment_oldtp;
                        end
                       else
                        begin
                          skipoldtpcomment;
                          next_char_loaded:=true;
                        end;
                     end
                    else
                     next_char_loaded:=true;
                  end
                 else
                  found:=0;
               end;
             '/' :
               begin
                 if (aktcommentstyle=comment_none) then
                  begin
                    readchar;
                    if c='/' then
                     skipdelphicomment;
                    next_char_loaded:=true;
                  end
                 else
                  found:=0;
               end;
             else
               found:=0;
           end;
           if next_char_loaded then
             next_char_loaded:=false
           else
             readchar;
         until (found=2);
      end;


{****************************************************************************
                             Comment Handling
****************************************************************************}

    procedure tscannerfile.skipcomment;
      begin
        aktcommentstyle:=comment_tp;
        readchar;
        inc_comment_level;
      { handle compiler switches }
        if (c='$') then
         handledirectives;
      { handle_switches can dec comment_level,  }
        while (comment_level>0) do
         begin
           case c of
            '{' :
              inc_comment_level;
            '}' :
              dec_comment_level;
            #10,#13 :
              linebreak;
            #26 :
              begin
                reload;
                if (c=#26) and not assigned(inputfile.next) then
                  end_of_file;
                continue;
              end;
           end;
           readchar;
         end;
        aktcommentstyle:=comment_none;
      end;


    procedure tscannerfile.skipdelphicomment;
      begin
        aktcommentstyle:=comment_delphi;
        inc_comment_level;
        readchar;
        { this is not supported }
        if c='$' then
          Message(scan_w_wrong_styled_switch);
        { skip comment }
        while not (c in [#10,#13,#26]) do
          readchar;
        dec_comment_level;
        aktcommentstyle:=comment_none;
      end;


    procedure tscannerfile.skipoldtpcomment;
      var
        found : longint;
      begin
        aktcommentstyle:=comment_oldtp;
        inc_comment_level;
        { only load a char if last already processed,
          was cause of bug1634 PM }
        if c=#0 then
          readchar;
      { this is now supported }
        if (c='$') then
         handledirectives;
      { skip comment }
        while (comment_level>0) do
         begin
           found:=0;
           repeat
             case c of
               #26 :
                 begin
                   reload;
                   if (c=#26) and not assigned(inputfile.next) then
                     end_of_file;
                   continue;
                 end;
               #10,#13 :
                 begin
                   if found=4 then
                    inc_comment_level;
                   linebreak;
                   found:=0;
                 end;
               '*' :
                 begin
                   if found=3 then
                    found:=4
                   else
                    found:=1;
                 end;
               ')' :
                 begin
                   if found in [1,4] then
                    begin
                      dec_comment_level;
                      if comment_level=0 then
                       found:=2
                      else
                       found:=0;
                    end
                   else
                    found:=0;
                 end;
               '(' :
                 begin
                   if found=4 then
                    inc_comment_level;
                   found:=3;
                 end;
               else
                 begin
                   if found=4 then
                    inc_comment_level;
                   found:=0;
                 end;
             end;
             readchar;
           until (found=2);
         end;
        aktcommentstyle:=comment_none;
      end;



{****************************************************************************
                               Token Scanner
****************************************************************************}

    procedure tscannerfile.readtoken(allowrecordtoken:boolean);
      var
        code    : integer;
        len,
        low,high,mid : longint;
        w : word;
        m       : longint;
        mac     : tmacro;
        asciinr : string[33];
        iswidestring : boolean;
      label
         exit_label;
      begin
        flushpendingswitchesstate;

        { record tokens? }
        if allowrecordtoken and
           assigned(recordtokenbuf) then
          recordtoken;

        { replay tokens? }
        if assigned(replaytokenbuf) then
          begin
            replaytoken;
            goto exit_label;
          end;

      { was there already a token read, then return that token }
        if nexttoken<>NOTOKEN then
         begin
           setnexttoken;
           goto exit_label;
         end;

      { Skip all spaces and comments }
        repeat
          case c of
            '{' :
              skipcomment;
            #26 :
              begin
                reload;
                if (c=#26) and not assigned(inputfile.next) then
                  break;
              end;
            ' ',#9..#13 :
              begin
{$ifdef PREPROCWRITE}
                if parapreprocess then
                 begin
                   if c=#10 then
                    preprocfile.eolfound:=true
                   else
                    preprocfile.spacefound:=true;
                 end;
{$endif PREPROCWRITE}
                skipspace;
              end
            else
              break;
          end;
        until false;

      { Save current token position, for EOF its already loaded }
        if c<>#26 then
          gettokenpos;

      { Check first for a identifier/keyword, this is 20+% faster (PFV) }
        if c in ['A'..'Z','a'..'z','_'] then
         begin
           readstring;
           token:=_ID;
           idtoken:=_ID;
         { keyword or any other known token,
           pattern is always uppercased }
           if (pattern[1]<>'_') and (length(pattern) in [tokenlenmin..tokenlenmax]) then
            begin
              low:=ord(tokenidx^[length(pattern),pattern[1]].first);
              high:=ord(tokenidx^[length(pattern),pattern[1]].last);
              while low<high do
               begin
                 mid:=(high+low+1) shr 1;
                 if pattern<tokeninfo^[ttoken(mid)].str then
                  high:=mid-1
                 else
                  low:=mid;
               end;
              with tokeninfo^[ttoken(high)] do
                if pattern=str then
                  begin
                    if keyword in current_settings.modeswitches then
                      if op=NOTOKEN then
                        token:=ttoken(high)
                      else
                        token:=op;
                    idtoken:=ttoken(high);
                  end;
            end;
         { Only process identifiers and not keywords }
           if token=_ID then
            begin
            { this takes some time ... }
              if (cs_support_macro in current_settings.moduleswitches) then
               begin
                 mac:=tmacro(search_macro(pattern));
                 if assigned(mac) and (not mac.is_compiler_var) and (assigned(mac.buftext)) then
                  begin
                    if yylexcount<max_macro_nesting then
                     begin
                       mac.is_used:=true;
                       inc(yylexcount);
                       substitutemacro(pattern,mac.buftext,mac.buflen,
                         mac.fileinfo.line,mac.fileinfo.fileindex);
                     { handle empty macros }
                       if c=#0 then
                         reload;
                       readtoken(false);
                       { that's all folks }
                       dec(yylexcount);
                       exit;
                     end
                    else
                     Message(scan_w_macro_too_deep);
                  end;
               end;
            end;
         { return token }
           goto exit_label;
         end
        else
         begin
           idtoken:=_NOID;
           case c of

             '$' :
               begin
                 readnumber;
                 token:=_INTCONST;
                 goto exit_label;
               end;

             '%' :
               begin
                 if not(m_fpc in current_settings.modeswitches) then
                  Illegal_Char(c)
                 else
                  begin
                    readnumber;
                    token:=_INTCONST;
                    goto exit_label;
                  end;
               end;

             '&' :
               begin
                 if [m_fpc,m_delphi] * current_settings.modeswitches <> [] then
                  begin
                    readnumber;
                    if length(pattern)=1 then
                      begin
                        readstring;
                        token:=_ID;
                        idtoken:=_ID;
                      end
                    else
                      token:=_INTCONST;
                    goto exit_label;
                  end
                 else if m_mac in current_settings.modeswitches then
                  begin
                    readchar;
                    token:=_AMPERSAND;
                    goto exit_label;
                  end
                 else
                  Illegal_Char(c);
               end;

             '0'..'9' :
               begin
                 readnumber;
                 if (c in ['.','e','E']) then
                  begin
                  { first check for a . }
                    if c='.' then
                     begin
                       cachenexttokenpos;
                       readchar;
                       { is it a .. from a range? }
                       case c of
                         '.' :
                           begin
                             readchar;
                             token:=_INTCONST;
                             nexttoken:=_POINTPOINT;
                             goto exit_label;
                           end;
                         ')' :
                           begin
                             readchar;
                             token:=_INTCONST;
                             nexttoken:=_RECKKLAMMER;
                             goto exit_label;
                           end;
                       end;
                       { insert the number after the . }
                       pattern:=pattern+'.';
                       while c in ['0'..'9'] do
                        begin
                          pattern:=pattern+c;
                          readchar;
                        end;
                      end;
                  { E can also follow after a point is scanned }
                    if c in ['e','E'] then
                     begin
                       pattern:=pattern+'E';
                       readchar;
                       if c in ['-','+'] then
                        begin
                          pattern:=pattern+c;
                          readchar;
                        end;
                       if not(c in ['0'..'9']) then
                        Illegal_Char(c);
                       while c in ['0'..'9'] do
                        begin
                          pattern:=pattern+c;
                          readchar;
                        end;
                     end;
                    token:=_REALNUMBER;
                    goto exit_label;
                  end;
                 token:=_INTCONST;
                 goto exit_label;
               end;

             ';' :
               begin
                 readchar;
                 token:=_SEMICOLON;
                 goto exit_label;
               end;

             '[' :
               begin
                 readchar;
                 token:=_LECKKLAMMER;
                 goto exit_label;
               end;

             ']' :
               begin
                 readchar;
                 token:=_RECKKLAMMER;
                 goto exit_label;
               end;

             '(' :
               begin
                 readchar;
                 case c of
                   '*' :
                     begin
                       c:=#0;{Signal skipoldtpcomment to reload a char }
                       skipoldtpcomment;
                       readtoken(false);
                       exit;
                     end;
                   '.' :
                     begin
                       readchar;
                       token:=_LECKKLAMMER;
                       goto exit_label;
                     end;
                 end;
                 token:=_LKLAMMER;
                 goto exit_label;
               end;

             ')' :
               begin
                 readchar;
                 token:=_RKLAMMER;
                 goto exit_label;
               end;

             '+' :
               begin
                 readchar;
                 if (c='=') and (cs_support_c_operators in current_settings.moduleswitches) then
                  begin
                    readchar;
                    token:=_PLUSASN;
                    goto exit_label;
                  end;
                 token:=_PLUS;
                 goto exit_label;
               end;

             '-' :
               begin
                 readchar;
                 if (c='=') and (cs_support_c_operators in current_settings.moduleswitches) then
                  begin
                    readchar;
                    token:=_MINUSASN;
                    goto exit_label;
                  end;
                 token:=_MINUS;
                 goto exit_label;
               end;

             ':' :
               begin
                 readchar;
                 if c='=' then
                  begin
                    readchar;
                    token:=_ASSIGNMENT;
                    goto exit_label;
                  end;
                 token:=_COLON;
                 goto exit_label;
               end;

             '*' :
               begin
                 readchar;
                 if (c='=') and (cs_support_c_operators in current_settings.moduleswitches) then
                  begin
                    readchar;
                    token:=_STARASN;
                  end
                 else
                  if c='*' then
                   begin
                     readchar;
                     token:=_STARSTAR;
                   end
                 else
                  token:=_STAR;
                 goto exit_label;
               end;

             '/' :
               begin
                 readchar;
                 case c of
                   '=' :
                     begin
                       if (cs_support_c_operators in current_settings.moduleswitches) then
                        begin
                          readchar;
                          token:=_SLASHASN;
                          goto exit_label;
                        end;
                     end;
                   '/' :
                     begin
                       skipdelphicomment;
                       readtoken(false);
                       exit;
                     end;
                 end;
                 token:=_SLASH;
                 goto exit_label;
               end;

             '|' :
               if m_mac in current_settings.modeswitches then
                begin
                  readchar;
                  token:=_PIPE;
                  goto exit_label;
                end
               else
                Illegal_Char(c);

             '=' :
               begin
                 readchar;
                 token:=_EQ;
                 goto exit_label;
               end;

             '.' :
               begin
                 readchar;
                 case c of
                   '.' :
                     begin
                       readchar;
                       case c of
                         '.' :
                         begin
                           readchar;
                           token:=_POINTPOINTPOINT;
                           goto exit_label;
                         end;
                       else
                         begin
                           token:=_POINTPOINT;
                           goto exit_label;
                         end;
                       end;
                     end;
                   ')' :
                     begin
                       readchar;
                       token:=_RECKKLAMMER;
                       goto exit_label;
                     end;
                 end;
                 token:=_POINT;
                 goto exit_label;
               end;

             '@' :
               begin
                 readchar;
                 token:=_KLAMMERAFFE;
                 goto exit_label;
               end;

             ',' :
               begin
                 readchar;
                 token:=_COMMA;
                 goto exit_label;
               end;

             '''','#','^' :
               begin
                 len:=0;
                 cstringpattern:='';
                 iswidestring:=false;
                 if c='^' then
                  begin
                    readchar;
                    c:=upcase(c);
                    if (block_type in [bt_type,bt_const_type,bt_var_type]) or
                       (lasttoken=_ID) or (lasttoken=_NIL) or (lasttoken=_OPERATOR) or
                       (lasttoken=_RKLAMMER) or (lasttoken=_RECKKLAMMER) or (lasttoken=_CARET) then
                     begin
                       token:=_CARET;
                       goto exit_label;
                     end
                    else
                     begin
                       inc(len);
                       setlength(cstringpattern,256);
                       if c<#64 then
                         cstringpattern[len]:=chr(ord(c)+64)
                       else
                         cstringpattern[len]:=chr(ord(c)-64);
                       readchar;
                     end;
                  end;
                 repeat
                   case c of
                     '#' :
                       begin
                         readchar; { read # }
                         case c of
                           '$':
                             begin
                               readchar; { read leading $ }
                               asciinr:='$';
                               while (upcase(c) in ['A'..'F','0'..'9']) and (length(asciinr)<=5) do
                                 begin
                                   asciinr:=asciinr+c;
                                   readchar;
                                 end;
                             end;
                           '&':
                             begin
                               readchar; { read leading $ }
                               asciinr:='&';
                               while (upcase(c) in ['0'..'7']) and (length(asciinr)<=7) do
                                 begin
                                   asciinr:=asciinr+c;
                                   readchar;
                                 end;
                             end;
                           '%':
                             begin
                               readchar; { read leading $ }
                               asciinr:='%';
                               while (upcase(c) in ['0','1']) and (length(asciinr)<=17) do
                                 begin
                                   asciinr:=asciinr+c;
                                   readchar;
                                 end;
                             end;
                           else
                             begin
                               asciinr:='';
                               while (c in ['0'..'9']) and (length(asciinr)<=5) do
                                 begin
                                   asciinr:=asciinr+c;
                                   readchar;
                                 end;
                             end;
                         end;
                         val(asciinr,m,code);
                         if (asciinr='') or (code<>0) then
                           Message(scan_e_illegal_char_const)
                         else if (m<0) or (m>255) or (length(asciinr)>3) then
                           begin
                              if (m>=0) and (m<=65535) then
                                begin
                                  if not iswidestring then
                                   begin
                                     if len>0 then
                                       ascii2unicode(@cstringpattern[1],len,current_settings.sourcecodepage,patternw)
                                     else
                                       ascii2unicode(nil,len,current_settings.sourcecodepage,patternw);
                                     iswidestring:=true;
                                     len:=0;
                                   end;
                                  concatwidestringchar(patternw,tcompilerwidechar(m));
                                end
                              else
                                Message(scan_e_illegal_char_const)
                           end
                         else if iswidestring then
                           concatwidestringchar(patternw,asciichar2unicode(char(m)))
                         else
                           begin
                             if len>=length(cstringpattern) then
                               setlength(cstringpattern,length(cstringpattern)+256);
                              inc(len);
                              cstringpattern[len]:=chr(m);
                           end;
                       end;
                     '''' :
                       begin
                         repeat
                           readchar;
                           case c of
                             #26 :
                               end_of_file;
                             #10,#13 :
                               Message(scan_f_string_exceeds_line);
                             '''' :
                               begin
                                 readchar;
                                 if c<>'''' then
                                  break;
                               end;
                           end;
                           { interpret as utf-8 string? }
                           if (ord(c)>=$80) and (current_settings.sourcecodepage=CP_UTF8) then
                             begin
                               { convert existing string to an utf-8 string }
                               if not iswidestring then
                                 begin
                                   if len>0 then
                                     ascii2unicode(@cstringpattern[1],len,current_settings.sourcecodepage,patternw)
                                   else
                                     ascii2unicode(nil,len,current_settings.sourcecodepage,patternw);
                                   iswidestring:=true;
                                   len:=0;
                                 end;
                               { four or more chars aren't handled }
                               if (ord(c) and $f0)=$f0 then
                                 message(scan_e_utf8_bigger_than_65535)
                               { three chars }
                               else if (ord(c) and $e0)=$e0 then
                                 begin
                                   w:=ord(c) and $f;
                                   readchar;
                                   if (ord(c) and $c0)<>$80 then
                                     message(scan_e_utf8_malformed);
                                   w:=(w shl 6) or (ord(c) and $3f);
                                   readchar;
                                   if (ord(c) and $c0)<>$80 then
                                     message(scan_e_utf8_malformed);
                                   w:=(w shl 6) or (ord(c) and $3f);
                                   concatwidestringchar(patternw,w);
                                 end
                               { two chars }
                               else if (ord(c) and $c0)<>0 then
                                 begin
                                   w:=ord(c) and $1f;
                                   readchar;
                                   if (ord(c) and $c0)<>$80 then
                                     message(scan_e_utf8_malformed);
                                   w:=(w shl 6) or (ord(c) and $3f);
                                   concatwidestringchar(patternw,w);
                                 end
                               { illegal }
                               else if (ord(c) and $80)<>0 then
                                 message(scan_e_utf8_malformed)
                               else
                                 concatwidestringchar(patternw,tcompilerwidechar(c))
                             end
                           else if iswidestring then
                             begin
                               if current_settings.sourcecodepage=CP_UTF8 then
                                 concatwidestringchar(patternw,ord(c))
                               else
                                 concatwidestringchar(patternw,asciichar2unicode(c))
                             end
                           else
                             begin
                               if len>=length(cstringpattern) then
                                 setlength(cstringpattern,length(cstringpattern)+256);
                                inc(len);
                                cstringpattern[len]:=c;
                             end;
                         until false;
                       end;
                     '^' :
                       begin
                         readchar;
                         c:=upcase(c);
                         if c<#64 then
                          c:=chr(ord(c)+64)
                         else
                          c:=chr(ord(c)-64);

                         if iswidestring then
                           concatwidestringchar(patternw,asciichar2unicode(c))
                         else
                           begin
                             if len>=length(cstringpattern) then
                               setlength(cstringpattern,length(cstringpattern)+256);
                              inc(len);
                              cstringpattern[len]:=c;
                           end;

                         readchar;
                       end;
                     else
                      break;
                   end;
                 until false;
                 { strings with length 1 become const chars }
                 if iswidestring then
                   begin
                     if patternw^.len=1 then
                       token:=_CWCHAR
                     else
                       token:=_CWSTRING;
                   end
                 else
                   begin
                     setlength(cstringpattern,len);
                     if length(cstringpattern)=1 then
                       begin
                         token:=_CCHAR;
                         pattern:=cstringpattern;
                       end
                     else
                       token:=_CSTRING;
                   end;
                 goto exit_label;
               end;

             '>' :
               begin
                 readchar;
                 if (block_type in [bt_type,bt_var_type,bt_const_type]) then
                   token:=_RSHARPBRACKET
                 else
                   begin
                     case c of
                       '=' :
                         begin
                           readchar;
                           token:=_GTE;
                           goto exit_label;
                         end;
                       '>' :
                         begin
                           readchar;
                           token:=_OP_SHR;
                           goto exit_label;
                         end;
                       '<' :
                         begin { >< is for a symetric diff for sets }
                           readchar;
                           token:=_SYMDIF;
                           goto exit_label;
                         end;
                     end;
                     token:=_GT;
                   end;
                 goto exit_label;
               end;

             '<' :
               begin
                 readchar;
                 if (block_type in [bt_type,bt_var_type,bt_const_type]) then
                   token:=_LSHARPBRACKET
                 else
                   begin
                     case c of
                       '>' :
                         begin
                           readchar;
                           token:=_NE;
                           goto exit_label;
                         end;
                       '=' :
                         begin
                           readchar;
                           token:=_LTE;
                           goto exit_label;
                         end;
                       '<' :
                         begin
                           readchar;
                           token:=_OP_SHL;
                           goto exit_label;
                         end;
                     end;
                     token:=_LT;
                   end;
                 goto exit_label;
               end;

             #26 :
               begin
                 token:=_EOF;
                 checkpreprocstack;
                 goto exit_label;
               end;
             else
               Illegal_Char(c);
           end;
        end;
exit_label:
        lasttoken:=token;
      end;


    function tscannerfile.readpreproc:ttoken;
      begin
         skipspace;
         case c of
           '_',
           'A'..'Z',
           'a'..'z' :
             begin
               current_scanner.preproc_pattern:=readid;
               readpreproc:=_ID;
             end;
           '0'..'9' :
             begin
               current_scanner.preproc_pattern:=readval_asstring;
               { realnumber? }
               if c='.' then
                 begin
                   readchar;
                   while c in ['0'..'9'] do
                     begin
                       current_scanner.preproc_pattern:=current_scanner.preproc_pattern+c;
                       readchar;
                     end;
                 end;
               readpreproc:=_ID;
             end;
           '$','%','&' :
             begin
               current_scanner.preproc_pattern:=readval_asstring;
               readpreproc:=_ID;
             end;
           ',' :
             begin
               readchar;
               readpreproc:=_COMMA;
             end;
           '}' :
             begin
               readpreproc:=_END;
             end;
           '(' :
             begin
               readchar;
               readpreproc:=_LKLAMMER;
             end;
           ')' :
             begin
               readchar;
               readpreproc:=_RKLAMMER;
             end;
           '[' :
             begin
               readchar;
               readpreproc:=_LECKKLAMMER;
             end;
           ']' :
             begin
               readchar;
               readpreproc:=_RECKKLAMMER;
             end;
           '+' :
             begin
               readchar;
               readpreproc:=_PLUS;
             end;
           '-' :
             begin
               readchar;
               readpreproc:=_MINUS;
             end;
           '*' :
             begin
               readchar;
               readpreproc:=_STAR;
             end;
           '/' :
             begin
               readchar;
               readpreproc:=_SLASH;
             end;
           '=' :
             begin
               readchar;
               readpreproc:=_EQ;
             end;
           '>' :
             begin
               readchar;
               if c='=' then
                 begin
                   readchar;
                   readpreproc:=_GTE;
                 end
               else
                 readpreproc:=_GT;
             end;
           '<' :
             begin
               readchar;
               case c of
                 '>' :
                   begin
                     readchar;
                     readpreproc:=_NE;
                   end;
                 '=' :
                   begin
                     readchar;
                     readpreproc:=_LTE;
                   end;
                 else
                   readpreproc:=_LT;
               end;
             end;
           #26 :
             begin
               readpreproc:=_EOF;
               checkpreprocstack;
             end;
           else
             Illegal_Char(c);
         end;
      end;


    function tscannerfile.asmgetcharstart : char;
      begin
        { return first the character already
          available in c }
        lastasmgetchar:=c;
        result:=asmgetchar;
      end;


    function tscannerfile.asmgetchar : char;
      begin
         if lastasmgetchar<>#0 then
          begin
            c:=lastasmgetchar;
            lastasmgetchar:=#0;
          end
         else
          readchar;
         if in_asm_string then
           begin
             asmgetchar:=c;
             exit;
           end;
         repeat
           case c of
             // the { ... } is used in ARM assembler to define register sets,  so we can't used
             // it as comment, either (* ... *), /* ... */ or // ... should be used instead.
             // But compiler directives {$...} are allowed in ARM assembler.
             '{' :
               begin
{$ifdef arm}
                 readchar;
                 dec(inputpointer);
                 if c<>'$' then
                   begin
                     asmgetchar:='{';
                     exit;
                   end
                 else
{$endif arm}
                   skipcomment;
               end;
             #10,#13 :
               begin
                 linebreak;
                 asmgetchar:=c;
                 exit;
               end;
             #26 :
               begin
                 reload;
                 if (c=#26) and not assigned(inputfile.next) then
                   end_of_file;
                 continue;
               end;
             '/' :
               begin
                  readchar;
                  if c='/' then
                   skipdelphicomment
                  else
                   begin
                     asmgetchar:='/';
                     lastasmgetchar:=c;
                     exit;
                   end;
               end;
             '(' :
               begin
                  readchar;
                  if c='*' then
                   begin
                     c:=#0;{Signal skipoldtpcomment to reload a char }
                     skipoldtpcomment;
                   end
                  else
                   begin
                     asmgetchar:='(';
                     lastasmgetchar:=c;
                     exit;
                   end;
               end;
             else
               begin
                 asmgetchar:=c;
                 exit;
               end;
           end;
         until false;
      end;


{*****************************************************************************
                                   Helpers
*****************************************************************************}

    procedure AddDirective(const s:string; dm: tdirectivemode; p:tdirectiveproc);
      begin
        if dm in [directive_all, directive_turbo] then
          tdirectiveitem.create(turbo_scannerdirectives,s,p);
        if dm in [directive_all, directive_mac] then
          tdirectiveitem.create(mac_scannerdirectives,s,p);
      end;

    procedure AddConditional(const s:string; dm: tdirectivemode; p:tdirectiveproc);
      begin
        if dm in [directive_all, directive_turbo] then
          tdirectiveitem.createcond(turbo_scannerdirectives,s,p);
        if dm in [directive_all, directive_mac] then
          tdirectiveitem.createcond(mac_scannerdirectives,s,p);
      end;

{*****************************************************************************
                                Initialization
*****************************************************************************}

    procedure InitScanner;
      begin
        InitWideString(patternw);
        turbo_scannerdirectives:=TFPHashObjectList.Create;
        mac_scannerdirectives:=TFPHashObjectList.Create;

        { Common directives and conditionals }
        AddDirective('I',directive_all, @dir_include);
        AddDirective('DEFINE',directive_all, @dir_define);
        AddDirective('UNDEF',directive_all, @dir_undef);

        AddConditional('IF',directive_all, @dir_if);
        AddConditional('IFDEF',directive_all, @dir_ifdef);
        AddConditional('IFNDEF',directive_all, @dir_ifndef);
        AddConditional('ELSE',directive_all, @dir_else);
        AddConditional('ELSEIF',directive_all, @dir_elseif);
        AddConditional('ENDIF',directive_all, @dir_endif);

        { Directives and conditionals for all modes except mode macpas}
        AddDirective('INCLUDE',directive_turbo, @dir_include);
        AddDirective('LIBPREFIX',directive_turbo, @dir_libprefix);
        AddDirective('LIBSUFFIX',directive_turbo, @dir_libsuffix);
        AddDirective('EXTENSION',directive_turbo, @dir_extension);

        AddConditional('IFEND',directive_turbo, @dir_endif);
        AddConditional('IFOPT',directive_turbo, @dir_ifopt);

        { Directives and conditionals for mode macpas: }
        AddDirective('SETC',directive_mac, @dir_setc);
        AddDirective('DEFINEC',directive_mac, @dir_definec);
        AddDirective('UNDEFC',directive_mac, @dir_undef);

        AddConditional('IFC',directive_mac, @dir_if);
        AddConditional('ELSEC',directive_mac, @dir_else);
        AddConditional('ELIFC',directive_mac, @dir_elseif);
        AddConditional('ENDC',directive_mac, @dir_endif);
      end;


    procedure DoneScanner;
      begin
        turbo_scannerdirectives.Free;
        mac_scannerdirectives.Free;
        DoneWideString(patternw);
      end;

end.
