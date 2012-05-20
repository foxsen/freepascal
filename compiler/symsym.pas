{
    Copyright (c) 1998-2002 by Florian Klaempfl, Pierre Muller

    Implementation for the symbols types of the symtable

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
unit symsym;

{$i fpcdefs.inc}

interface

    uses
       { common }
       cutils,
       { target }
       globtype,globals,widestr,constexp,
       { symtable }
       symconst,symbase,symtype,symdef,defcmp,
       { ppu }
       ppu,finput,
       cclasses,symnot,
       { aasm }
       aasmbase,
       cpuinfo,cpubase,cgbase,cgutils,parabase
       ;

    type
       { this class is the base for all symbol objects }
       tstoredsym = class(tsym)
       public
          constructor create(st:tsymtyp;const n : string);
          constructor ppuload(st:tsymtyp;ppufile:tcompilerppufile);
          destructor destroy;override;
          procedure ppuwrite(ppufile:tcompilerppufile);virtual;
       end;

       tlabelsym = class(tstoredsym)
          used,
          defined,
          nonlocal : boolean;
          { points to the matching node, only valid resultdef pass is run and
            the goto<->label relation in the node tree is created, should
            be a tnode }
          code : pointer;

          { points to the jump buffer }
          jumpbuf : tstoredsym;

          { when the label is defined in an asm block, this points to the
            generated asmlabel }
          asmblocklabel : tasmlabel;
          constructor create(const n : string);
          constructor ppuload(ppufile:tcompilerppufile);
          procedure ppuwrite(ppufile:tcompilerppufile);override;
          function mangledname:TSymStr;override;
       end;

       tunitsym = class(Tstoredsym)
          module : tobject; { tmodule }
          constructor create(const n : string;amodule : tobject);
          constructor ppuload(ppufile:tcompilerppufile);
          destructor destroy;override;
          procedure ppuwrite(ppufile:tcompilerppufile);override;
       end;

       tnamespacesym = class(Tstoredsym)
          unitsym:tsym;
          unitsymderef:tderef;
          constructor create(const n : string);
          constructor ppuload(ppufile:tcompilerppufile);
          procedure ppuwrite(ppufile:tcompilerppufile);override;
          procedure buildderef;override;
          procedure deref;override;
       end;

       terrorsym = class(Tsym)
          constructor create;
       end;

       { tprocsym }

       tprocsym = class(tstoredsym)
       protected
          FProcdefList   : TFPObjectList;
          FProcdefDerefList : TFPList;
       public
          constructor create(const n : string);
          constructor ppuload(ppufile:tcompilerppufile);
          destructor destroy;override;
          { writes all declarations except the specified one }
          procedure write_parameter_lists(skipdef:tprocdef);
          { tests, if all procedures definitions are defined and not }
          { only forward                                             }
          procedure check_forward;
          procedure ppuwrite(ppufile:tcompilerppufile);override;
          procedure buildderef;override;
          procedure deref;override;
          function find_procdef_bytype(pt:Tproctypeoption):Tprocdef;
          function find_bytype_parameterless(pt:Tproctypeoption):Tprocdef;
          function find_procdef_bypara(para:TFPObjectList;retdef:tdef;cpoptions:tcompare_paras_options):Tprocdef;
          function find_procdef_bytype_and_para(pt:Tproctypeoption;para:TFPObjectList;retdef:tdef;cpoptions:tcompare_paras_options):Tprocdef;
          function find_procdef_byoptions(ops:tprocoptions): Tprocdef;
          function find_procdef_byprocvardef(d:Tprocvardef):Tprocdef;
          function find_procdef_assignment_operator(fromdef,todef:tdef;var besteq:tequaltype):Tprocdef;
          function find_procdef_enumerator_operator(fromdef,todef:tdef;var besteq:tequaltype):Tprocdef;
          property ProcdefList:TFPObjectList read FProcdefList;
       end;

       ttypesym = class(Tstoredsym)
       public
          typedef      : tdef;
          typedefderef : tderef;
          fprettyname : ansistring;
          constructor create(const n : string;def:tdef);
          constructor ppuload(ppufile:tcompilerppufile);
          procedure ppuwrite(ppufile:tcompilerppufile);override;
          procedure buildderef;override;
          procedure deref;override;
          function prettyname : string;override;
       end;

       tabstractvarsym = class(tstoredsym)
          varoptions    : tvaroptions;
          notifications : Tlinkedlist;
          varspez       : tvarspez;  { sets the type of access }
          varregable    : tvarregable;
          varstate      : tvarstate;
          { Has the address of this variable potentially escaped the }
          { block in which is was declared?                          }
          { could also be part of tabstractnormalvarsym, but there's }
          { one byte left here till the next 4 byte alignment        }
          addr_taken     : boolean;
          constructor create(st:tsymtyp;const n : string;vsp:tvarspez;def:tdef;vopts:tvaroptions);
          constructor ppuload(st:tsymtyp;ppufile:tcompilerppufile);
          destructor  destroy;override;
          procedure ppuwrite(ppufile:tcompilerppufile);override;
          procedure buildderef;override;
          procedure deref;override;
          function  getsize : asizeint;
          function  getpackedbitsize : longint;
          function  is_regvar(refpara: boolean):boolean;
          procedure trigger_notifications(what:Tnotification_flag);
          function register_notification(flags:Tnotification_flags;
                                         callback:Tnotification_callback):cardinal;
          procedure unregister_notification(id:cardinal);
        private
          _vardef     : tdef;
          vardefderef : tderef;

          procedure setvardef(def:tdef);
        public
          property vardef: tdef read _vardef write setvardef;
      end;

      tfieldvarsym = class(tabstractvarsym)
          fieldoffset   : asizeint;   { offset in record/object }
          externalname  : pshortstring;
{$ifdef symansistr}
          cachedmangledname: TSymStr; { mangled name for ObjC or Java }
{$else symansistr}
          cachedmangledname: pshortstring; { mangled name for ObjC or Java }
{$endif symansistr}
          constructor create(const n : string;vsp:tvarspez;def:tdef;vopts:tvaroptions);
          constructor ppuload(ppufile:tcompilerppufile);
          procedure ppuwrite(ppufile:tcompilerppufile);override;
          procedure set_externalname(const s:string);
          function mangledname:TSymStr;override;
          destructor destroy;override;
      end;

      tabstractnormalvarsym = class(tabstractvarsym)
          defaultconstsym : tsym;
          defaultconstsymderef : tderef;
          localloc      : TLocation; { register/reference for local var }
          initialloc    : TLocation; { initial location so it can still be initialized later after the location was changed by SSA }
          inparentfpstruct : boolean;   { migrated to a parentfpstruct because of nested access (not written to ppu, because not important and would change interface crc) }
          constructor create(st:tsymtyp;const n : string;vsp:tvarspez;def:tdef;vopts:tvaroptions);
          constructor ppuload(st:tsymtyp;ppufile:tcompilerppufile);
          procedure ppuwrite(ppufile:tcompilerppufile);override;
          procedure buildderef;override;
          procedure deref;override;
      end;

      tlocalvarsym = class(tabstractnormalvarsym)
          constructor create(const n : string;vsp:tvarspez;def:tdef;vopts:tvaroptions);
          constructor ppuload(ppufile:tcompilerppufile);
          procedure ppuwrite(ppufile:tcompilerppufile);override;
      end;

      tparavarsym = class(tabstractnormalvarsym)
          paraloc       : array[tcallercallee] of TCGPara;
          paranr        : word; { position of this parameter }
          { in MacPas mode, "univ" parameters mean that type checking should
            be disabled, except that the size of the passed parameter must
            match the size of the formal parameter }
          univpara      : boolean;
{$ifdef EXTDEBUG}
          eqval         : tequaltype;
{$endif EXTDEBUG}
          constructor create(const n : string;nr:word;vsp:tvarspez;def:tdef;vopts:tvaroptions);
          constructor ppuload(ppufile:tcompilerppufile);
          destructor destroy;override;
          procedure ppuwrite(ppufile:tcompilerppufile);override;
          function needs_finalization: boolean;
      end;

      tstaticvarsym = class(tabstractnormalvarsym)
      private
{$ifdef symansistr}
          _mangledbasename,
          _mangledname : TSymStr;
{$else symansistr}
          _mangledbasename,
          _mangledname : pshortstring;
{$endif symansistr}
      public
          section : ansistring;
          constructor create(const n : string;vsp:tvarspez;def:tdef;vopts:tvaroptions);
          constructor create_dll(const n : string;vsp:tvarspez;def:tdef);
          constructor create_C(const n: string; const mangled : TSymStr;vsp:tvarspez;def:tdef);
          constructor ppuload(ppufile:tcompilerppufile);
          destructor destroy;override;
          procedure ppuwrite(ppufile:tcompilerppufile);override;
          function mangledname:TSymStr;override;
          procedure set_mangledbasename(const s: TSymStr);
          function mangledbasename: TSymStr;
          procedure set_mangledname(const s:TSymStr);
          procedure set_raw_mangledname(const s:TSymStr);
      end;

      tabsolutevarsym = class(tabstractvarsym)
      public
         abstyp  : absolutetyp;
{$ifdef i386}
         absseg  : boolean;
{$endif i386}
         asmname : pshortstring;
         addroffset : aword;
         ref     : tpropaccesslist;
         constructor create(const n : string;def:tdef);
         constructor create_ref(const n : string;def:tdef;_ref:tpropaccesslist);
         destructor  destroy;override;
         constructor ppuload(ppufile:tcompilerppufile);
         procedure buildderef;override;
         procedure deref;override;
         function  mangledname : TSymStr;override;
         procedure ppuwrite(ppufile:tcompilerppufile);override;
      end;

       tpropaccesslisttypes=(palt_none,palt_read,palt_write,palt_stored);

       tpropertysym = class(Tstoredsym)
          propoptions   : tpropertyoptions;
          overriddenpropsym : tpropertysym;
          overriddenpropsymderef : tderef;
          propdef       : tdef;
          propdefderef  : tderef;
          indexdef      : tdef;
          indexdefderef : tderef;
          index,
          default       : longint;
          dispid        : longint;
          propaccesslist: array[tpropaccesslisttypes] of tpropaccesslist;
          parast : tsymtable;
          constructor create(const n : string);
          destructor  destroy;override;
          constructor ppuload(ppufile:tcompilerppufile);
          function  getsize : asizeint;
          procedure ppuwrite(ppufile:tcompilerppufile);override;
          procedure buildderef;override;
          procedure deref;override;
       end;

       tconstvalue = record
         case integer of
         0: (valueord : tconstexprint);
         1: (valueordptr : tconstptruint);
         2: (valueptr : pointer; len : longint);
       end;

       tconstsym = class(tstoredsym)
          constdef    : tdef;
          constdefderef : tderef;
          consttyp    : tconsttyp;
          value       : tconstvalue;
          constructor create_ord(const n : string;t : tconsttyp;v : tconstexprint;def:tdef);
          constructor create_ordptr(const n : string;t : tconsttyp;v : tconstptruint;def:tdef);
          constructor create_ptr(const n : string;t : tconsttyp;v : pointer;def:tdef);
          constructor create_string(const n : string;t : tconsttyp;str:pchar;l:longint);
          constructor create_wstring(const n : string;t : tconsttyp;pw:pcompilerwidestring);
          constructor ppuload(ppufile:tcompilerppufile);
          destructor  destroy;override;
          procedure buildderef;override;
          procedure deref;override;
          procedure ppuwrite(ppufile:tcompilerppufile);override;
       end;

       tenumsym = class(Tstoredsym)
          value      : longint;
          definition : tenumdef;
          definitionderef : tderef;
          constructor create(const n : string;def : tenumdef;v : longint);
          constructor ppuload(ppufile:tcompilerppufile);
          procedure ppuwrite(ppufile:tcompilerppufile);override;
          procedure buildderef;override;
          procedure deref;override;
       end;

       tsyssym = class(Tstoredsym)
          number : longint;
          constructor create(const n : string;l : longint);
          constructor ppuload(ppufile:tcompilerppufile);
          destructor  destroy;override;
          procedure ppuwrite(ppufile:tcompilerppufile);override;
       end;

    const
       maxmacrolen=16*1024;

    type
       pmacrobuffer = ^tmacrobuffer;
       tmacrobuffer = array[0..maxmacrolen-1] of char;

       tmacro = class(tstoredsym)
          {Normally true, but false when a previously defined macro is undef-ed}
          defined : boolean;
          {True if this is a mac style compiler variable, in which case no macro
           substitutions shall be done.}
          is_compiler_var : boolean;
          {Whether the macro was used. NOTE: A use of a macro which was never defined}
          {e. g. an IFDEF which returns false, will not be registered as used,}
          {since there is no place to register its use. }
          is_used : boolean;
          buftext : pchar;
          buflen  : longint;
          constructor create(const n : string);
          constructor ppuload(ppufile:tcompilerppufile);
          procedure ppuwrite(ppufile:tcompilerppufile);override;
          destructor  destroy;override;
          function GetCopy:tmacro;
       end;

    var
       generrorsym : tsym;

    { generate internal static field name based on regular field name }
    function internal_static_field_name(const fieldname: TSymStr): TSymStr;
    function get_high_value_sym(vs: tparavarsym):tsym; { marking it as inline causes IE 200311075 during loading from ppu file }

    procedure check_hints(const srsym: tsym; const symoptions: tsymoptions; const deprecatedmsg : pshortstring);

implementation

    uses
       { global }
       verbose,
       { target }
       systems,
       { symtable }
       defutil,symtable,
{$ifdef jvm}
       jvmdef,
{$endif}
       fmodule,
       { tree }
       node,
       { aasm }
       aasmtai,aasmdata,
       { codegen }
       paramgr,
       procinfo
       ;

{****************************************************************************
                               Helpers
****************************************************************************}

    function internal_static_field_name(const fieldname: TSymStr): TSymStr;
      begin
        result:='$_static_'+fieldname;
      end;


    function get_high_value_sym(vs: tparavarsym):tsym;
      begin
        result := tsym(vs.owner.Find('high'+vs.name));
      end;

    procedure check_hints(const srsym: tsym; const symoptions: tsymoptions; const deprecatedmsg : pshortstring);
      begin
        if not assigned(srsym) then
          internalerror(200602051);
        if sp_hint_deprecated in symoptions then
          if (sp_has_deprecated_msg in symoptions) and (deprecatedmsg <> nil) then
            Message2(sym_w_deprecated_symbol_with_msg,srsym.realname,deprecatedmsg^)
          else
            Message1(sym_w_deprecated_symbol,srsym.realname);
        if sp_hint_experimental in symoptions then
          Message1(sym_w_experimental_symbol,srsym.realname);
        if sp_hint_platform in symoptions then
          Message1(sym_w_non_portable_symbol,srsym.realname);
        if sp_hint_library in symoptions then
          Message1(sym_w_library_symbol,srsym.realname);
        if sp_hint_unimplemented in symoptions then
          Message1(sym_w_non_implemented_symbol,srsym.realname);
      end;



{****************************************************************************
                          TSYM (base for all symtypes)
****************************************************************************}

    constructor tstoredsym.create(st:tsymtyp;const n : string);
      begin
         inherited create(st,n);
         { Register in current_module }
         if assigned(current_module) then
           begin
             current_module.symlist.Add(self);
             SymId:=current_module.symlist.Count-1;
           end;
      end;


    constructor tstoredsym.ppuload(st:tsymtyp;ppufile:tcompilerppufile);
      begin
         SymId:=ppufile.getlongint;
         inherited Create(st,ppufile.getstring);
         { Register symbol }
         current_module.symlist[SymId]:=self;
         ppufile.getposinfo(fileinfo);
         visibility:=tvisibility(ppufile.getbyte);
         ppufile.getsmallset(symoptions);
         if sp_has_deprecated_msg in symoptions then
           deprecatedmsg:=stringdup(ppufile.getstring)
         else
           deprecatedmsg:=nil;
      end;


    procedure tstoredsym.ppuwrite(ppufile:tcompilerppufile);
      var
        oldintfcrc : boolean;
      begin
         ppufile.putlongint(SymId);
         ppufile.putstring(realname);
         ppufile.putposinfo(fileinfo);
         ppufile.putbyte(byte(visibility));
         { symoptions can differ between interface and implementation, except
           for overload (this is checked in pdecsub.proc_add_definition() )

           These differences can lead to compiler crashes, so ignore them.
           This does mean that changing e.g. the "deprecated" state of a symbol
           by itself will not trigger a recompilation of dependent units.
         }
         oldintfcrc:=ppufile.do_interface_crc;
         ppufile.do_interface_crc:=false;
         ppufile.putsmallset(symoptions);
         if sp_has_deprecated_msg in symoptions then
           ppufile.putstring(deprecatedmsg^);
         ppufile.do_interface_crc:=oldintfcrc;
      end;


    destructor tstoredsym.destroy;
      begin
        inherited destroy;
      end;


{****************************************************************************
                                 TLABELSYM
****************************************************************************}

    constructor tlabelsym.create(const n : string);
      begin
         inherited create(labelsym,n);
         used:=false;
         defined:=false;
         nonlocal:=false;
         code:=nil;
      end;


    constructor tlabelsym.ppuload(ppufile:tcompilerppufile);
      begin
         inherited ppuload(labelsym,ppufile);
         code:=nil;
         used:=false;
         nonlocal:=false;
         defined:=true;
      end;


    procedure tlabelsym.ppuwrite(ppufile:tcompilerppufile);
      begin
         if owner.symtabletype=globalsymtable then
           Message(sym_e_ill_label_decl)
         else
           begin
              inherited ppuwrite(ppufile);
              ppufile.writeentry(iblabelsym);
           end;
      end;


   function tlabelsym.mangledname:TSymStr;
     begin
       if not(defined) then
         begin
           defined:=true;
           if nonlocal then
             current_asmdata.getglobaljumplabel(asmblocklabel)
           else
             current_asmdata.getjumplabel(asmblocklabel);
         end;
       result:=asmblocklabel.name;
     end;

{****************************************************************************
                                  TUNITSYM
****************************************************************************}

    constructor tunitsym.create(const n : string;amodule : tobject);
      begin
         inherited create(unitsym,n);
         module:=amodule;
      end;

    constructor tunitsym.ppuload(ppufile:tcompilerppufile);

      begin
         inherited ppuload(unitsym,ppufile);
         module:=nil;
      end;

    destructor tunitsym.destroy;
      begin
         inherited destroy;
      end;

    procedure tunitsym.ppuwrite(ppufile:tcompilerppufile);
      begin
         inherited ppuwrite(ppufile);
         ppufile.writeentry(ibunitsym);
      end;

{****************************************************************************
                                TNAMESPACESYM
****************************************************************************}

    constructor tnamespacesym.create(const n : string);
      begin
         inherited create(namespacesym,n);
         unitsym:=nil;
      end;

    constructor tnamespacesym.ppuload(ppufile:tcompilerppufile);
      begin
         inherited ppuload(namespacesym,ppufile);
         ppufile.getderef(unitsymderef);
      end;

    procedure tnamespacesym.ppuwrite(ppufile:tcompilerppufile);
      begin
         inherited ppuwrite(ppufile);
         ppufile.putderef(unitsymderef);
         ppufile.writeentry(ibnamespacesym);
      end;

    procedure tnamespacesym.buildderef;
      begin
        inherited buildderef;
        unitsymderef.build(unitsym);
      end;

    procedure tnamespacesym.deref;
      begin
        inherited deref;
        unitsym:=tsym(unitsymderef.resolve);
      end;


{****************************************************************************
                                  TPROCSYM
****************************************************************************}

    constructor tprocsym.create(const n : string);
      begin
         inherited create(procsym,n);
         FProcdefList:=TFPObjectList.Create(false);
         FProcdefderefList:=nil;
         { the tprocdef have their own symoptions, make the procsym
           always visible }
         visibility:=vis_public;
      end;


    constructor tprocsym.ppuload(ppufile:tcompilerppufile);
      var
         pdderef : tderef;
         i,
         pdcnt : longint;
      begin
         inherited ppuload(procsym,ppufile);
         FProcdefList:=TFPObjectList.Create(false);
         FProcdefDerefList:=TFPList.Create;
         pdcnt:=ppufile.getword;
         for i:=1 to pdcnt do
          begin
            ppufile.getderef(pdderef);
            FProcdefDerefList.Add(Pointer(PtrInt(pdderef.dataidx)));
          end;
      end;


    destructor tprocsym.destroy;
      begin
        FProcdefList.Free;
        if assigned(FProcdefDerefList) then
          FProcdefDerefList.Free;
        inherited destroy;
      end;


    procedure tprocsym.ppuwrite(ppufile:tcompilerppufile);
      var
         i : longint;
         d : tderef;
      begin
         inherited ppuwrite(ppufile);
         ppufile.putword(FProcdefDerefList.Count);
         for i:=0 to FProcdefDerefList.Count-1 do
           begin
             d.dataidx:=PtrInt(FProcdefDerefList[i]);
             ppufile.putderef(d);
           end;
         ppufile.writeentry(ibprocsym);
      end;


    procedure tprocsym.write_parameter_lists(skipdef:tprocdef);
      var
        i  : longint;
        pd : tprocdef;
      begin
        for i:=0 to ProcdefList.Count-1 do
          begin
            pd:=tprocdef(ProcdefList[i]);
            if pd<>skipdef then
              MessagePos1(pd.fileinfo,sym_h_param_list,pd.fullprocname(false));
           end;
      end;


    procedure tprocsym.check_forward;
      var
        i  : longint;
        pd : tprocdef;
      begin
        for i:=0 to ProcdefList.Count-1 do
          begin
            pd:=tprocdef(ProcdefList[i]);
            if (pd.owner=owner) and (pd.forwarddef) then
              begin
                { For mode macpas. Make implicit externals (procedures declared in the interface
                  section which do not have a counterpart in the implementation)
                  to be an imported procedure }
                if (m_mac in current_settings.modeswitches) and
                   (pd.interfacedef) then
                  begin
                    pd.setmangledname(target_info.CPrefix+tprocdef(pd).procsym.realname);
                    if (not current_module.interface_only) then
                      MessagePos1(pd.fileinfo,sym_w_forward_not_resolved,pd.fullprocname(false));
                  end
                else
                  begin
                    MessagePos1(pd.fileinfo,sym_e_forward_not_resolved,pd.fullprocname(false));
                  end;
                { Turn further error messages off }
                pd.forwarddef:=false;
              end;
          end;
      end;


    procedure tprocsym.buildderef;
      var
        i  : longint;
        pd : tprocdef;
        d  : tderef;
      begin
        if not assigned(FProcdefDerefList) then
          FProcdefDerefList:=TFPList.Create
        else
          FProcdefDerefList.Clear;
        for i:=0 to ProcdefList.Count-1 do
          begin
            pd:=tprocdef(ProcdefList[i]);
            { only write the proc definitions that belong
              to this procsym and are in the global symtable }
            if pd.owner=owner then
              begin
                d.build(pd);
                FProcdefDerefList.Add(Pointer(PtrInt(d.dataidx)));
              end;
          end;
      end;


    procedure tprocsym.deref;
      var
        i  : longint;
        pd : tprocdef;
        d  : tderef;
      begin
        { Clear all procdefs }
        ProcdefList.Clear;
        if not assigned(FProcdefDerefList) then
          internalerror(200611031);
        for i:=0 to FProcdefDerefList.Count-1 do
          begin
            d.dataidx:=PtrInt(FProcdefDerefList[i]);
            pd:=tprocdef(d.resolve);
            ProcdefList.Add(pd);
          end;
      end;


    function Tprocsym.Find_procdef_bytype(pt:Tproctypeoption):Tprocdef;
      var
        i  : longint;
        pd : tprocdef;
      begin
        result:=nil;
        for i:=0 to ProcdefList.Count-1 do
          begin
            pd:=tprocdef(ProcdefList[i]);
            if pd.proctypeoption=pt then
              begin
                result:=pd;
                exit;
              end;
          end;
      end;


    function tprocsym.find_bytype_parameterless(pt: Tproctypeoption): Tprocdef;
      var
        i,j : longint;
        pd  : tprocdef;
        found : boolean;
      begin
        result:=nil;
        for i:=0 to ProcdefList.Count-1 do
          begin
            pd:=tprocdef(ProcdefList[i]);
            if (pd.proctypeoption=pt) then
              begin
                found:=true;
                for j:=0 to pd.paras.count-1 do
                  begin
                    if not(vo_is_hidden_para in tparavarsym(pd.paras[j]).varoptions) then
                      begin
                        found:=false;
                        break;
                      end;
                  end;
                if found then
                  begin
                    result:=pd;
                    exit;
                  end;
              end;
          end;
      end;


    function check_procdef_paras(pd:tprocdef;para:TFPObjectList;retdef:tdef;
                                            cpoptions:tcompare_paras_options): tprocdef;
      var
        eq: tequaltype;
      begin
        result:=nil;
        if assigned(retdef) then
          eq:=compare_defs(retdef,pd.returndef,nothingn)
        else
          eq:=te_equal;
        if (eq>=te_equal) or
           ((cpo_allowconvert in cpoptions) and (eq>te_incompatible)) then
          begin
            eq:=compare_paras(para,pd.paras,cp_value_equal_const,cpoptions);
            if (eq>=te_equal) or
               ((cpo_allowconvert in cpoptions) and (eq>te_incompatible)) then
              begin
                result:=pd;
                exit;
              end;
          end;
      end;


    function Tprocsym.Find_procdef_bypara(para:TFPObjectList;retdef:tdef;
                                            cpoptions:tcompare_paras_options):Tprocdef;
      var
        i  : longint;
        pd : tprocdef;
      begin
        result:=nil;
        for i:=0 to ProcdefList.Count-1 do
          begin
            pd:=tprocdef(ProcdefList[i]);
            result:=check_procdef_paras(pd,para,retdef,cpoptions);
            if assigned(result) then
              exit;
          end;
      end;


    function Tprocsym.find_procdef_bytype_and_para(pt:Tproctypeoption;
               para:TFPObjectList;retdef:tdef;cpoptions:tcompare_paras_options):Tprocdef;
      var
        i  : longint;
        pd : tprocdef;
      begin
        result:=nil;
        for i:=0 to ProcdefList.Count-1 do
          begin
            pd:=tprocdef(ProcdefList[i]);
            if pd.proctypeoption=pt then
              begin
                result:=check_procdef_paras(pd,para,retdef,cpoptions);
                if assigned(result) then
                  exit;
              end;
          end;
      end;


    function tprocsym.find_procdef_byoptions(ops: tprocoptions): Tprocdef;
      var
        i  : longint;
        pd : tprocdef;
      begin
        result:=nil;
        for i:=0 to ProcdefList.Count-1 do
          begin
            pd:=tprocdef(ProcdefList[i]);
            if ops * pd.procoptions = ops then
              begin
                result:=pd;
                exit;
              end;
          end;
      end;

    function Tprocsym.Find_procdef_byprocvardef(d:Tprocvardef):Tprocdef;
      var
        i  : longint;
        bestpd,
        pd : tprocdef;
        eq,besteq : tequaltype;
        sym: tsym;
        ps: tprocsym;
      begin
        { This function will return the pprocdef of pprocsym that
          is the best match for procvardef. When there are multiple
          matches it returns nil.}
        result:=nil;
        bestpd:=nil;
        besteq:=te_incompatible;
        ps:=self;
        repeat
          for i:=0 to ps.ProcdefList.Count-1 do
            begin
              pd:=tprocdef(ps.ProcdefList[i]);
              eq:=proc_to_procvar_equal(pd,d,false);
              if eq>=te_convert_l1 then
                begin
                  { multiple procvars with the same equal level }
                  if assigned(bestpd) and
                     (besteq=eq) then
                    exit;
                  if eq>besteq then
                    begin
                      besteq:=eq;
                      bestpd:=pd;
                    end;
                end;
            end;
          { maybe TODO: also search class helpers? -- this code is similar to
            what happens in htypechk in
            tcallcandidates.collect_overloads_in_struct: keep searching in
            parent types in case the currently found procdef is marked as
            "overload" and we haven't found a proper match yet }
          if assigned(ps.owner.defowner) and
             (ps.owner.defowner.typ=objectdef) and
             assigned(tobjectdef(ps.owner.defowner).childof) and
             (not assigned(bestpd) or
              (po_overload in bestpd.procoptions)) then
            begin
              sym:=tsym(tobjectdef(ps.owner.defowner).childof.symtable.find(ps.name));
              if assigned(sym) and
                 (sym.typ=procsym) then
                ps:=tprocsym(sym)
              else
                ps:=nil;
            end
          else
            ps:=nil;
        until (besteq>=te_equal) or
              not assigned(ps);
        result:=bestpd;
      end;


    function Tprocsym.Find_procdef_assignment_operator(fromdef,todef:tdef;var besteq:tequaltype):Tprocdef;
      var
        paraidx, realparamcount,
        i, j : longint;
        bestpd,
        hpd,
        pd : tprocdef;
        convtyp : tconverttype;
        eq      : tequaltype;
      begin
        { This function will return the pprocdef of pprocsym that
          is the best match for fromdef and todef. }
        result:=nil;
        bestpd:=nil;
        besteq:=te_incompatible;
        for i:=0 to ProcdefList.Count-1 do
          begin
            pd:=tprocdef(ProcdefList[i]);
            if (pd.owner.symtabletype=staticsymtable) and not pd.owner.iscurrentunit then
              continue;
            if (equal_defs(todef,pd.returndef) or
                { shortstrings of different lengths are ok as result }
                (is_shortstring(todef) and is_shortstring(pd.returndef))) and
               { the result type must be always really equal and not an alias,
                 if you mess with this code, check tw4093 }
               ((todef=pd.returndef) or
                (
                  not(df_unique in todef.defoptions) and
                  not(df_unique in pd.returndef.defoptions)
                )
               ) then
              begin
                paraidx:=0;
                { ignore vs_hidden parameters }
                while (paraidx<pd.paras.count) and
                      assigned(pd.paras[paraidx]) and
                      (vo_is_hidden_para in tparavarsym(pd.paras[paraidx]).varoptions) do
                  inc(paraidx);
                realparamcount:=0;
                for j := 0 to pd.paras.Count-1 do
                  if assigned(pd.paras[j]) and not (vo_is_hidden_para in tparavarsym(pd.paras[j]).varoptions) then
                    inc(realparamcount);
                if (paraidx<pd.paras.count) and
                   assigned(pd.paras[paraidx]) and
                   (realparamcount = 1) then
                  begin
                    eq:=compare_defs_ext(fromdef,tparavarsym(pd.paras[paraidx]).vardef,nothingn,convtyp,hpd,[]);

                    { alias? if yes, only l1 choice,
                      if you mess with this code, check tw4093 }
                    if (eq=te_exact) and
                       (fromdef<>tparavarsym(pd.paras[paraidx]).vardef) and
                       ((df_unique in fromdef.defoptions) or
                       (df_unique in tparavarsym(pd.paras[paraidx]).vardef.defoptions)) then
                      eq:=te_convert_l1;

                    if eq=te_exact then
                      begin
                        besteq:=eq;
                        result:=pd;
                        exit;
                      end;
                    if eq>besteq then
                      begin
                        bestpd:=pd;
                        besteq:=eq;
                      end;
                  end;
              end;
          end;
        result:=bestpd;
      end;

      function Tprocsym.find_procdef_enumerator_operator(fromdef,todef:tdef;var besteq:tequaltype):Tprocdef;
      var
        paraidx, realparamcount,
        i, j : longint;
        bestpd,
        hpd,
        pd : tprocdef;
        current : tpropertysym;
        convtyp : tconverttype;
        eq      : tequaltype;
      begin
        { This function will return the pprocdef of pprocsym that
          is the best match for fromdef and todef. }
        result:=nil;
        bestpd:=nil;
        besteq:=te_incompatible;
        for i:=0 to ProcdefList.Count-1 do
          begin
            pd:=tprocdef(ProcdefList[i]);
            if (pd.owner.symtabletype=staticsymtable) and not pd.owner.iscurrentunit then
              continue;
            if not (is_class_or_interface_or_object(pd.returndef) or is_record(pd.returndef)) then
              continue;
            current := tpropertysym(tabstractrecorddef(pd.returndef).search_enumerator_current);
            if (current = nil) then
              continue;
            // compare current result def with the todef
            if (equal_defs(todef, current.propdef) or
                { shortstrings of different lengths are ok as result }
                (is_shortstring(todef) and is_shortstring(current.propdef))) and
               { the result type must be always really equal and not an alias,
                 if you mess with this code, check tw4093 }
               ((todef=current.propdef) or
                (
                  not(df_unique in todef.defoptions) and
                  not(df_unique in current.propdef.defoptions)
                )
               ) then
              begin
                paraidx:=0;
                { ignore vs_hidden parameters }
                while (paraidx<pd.paras.count) and
                      assigned(pd.paras[paraidx]) and
                      (vo_is_hidden_para in tparavarsym(pd.paras[paraidx]).varoptions) do
                  inc(paraidx);
                realparamcount:=0;
                for j := 0 to pd.paras.Count-1 do
                  if assigned(pd.paras[j]) and not (vo_is_hidden_para in tparavarsym(pd.paras[j]).varoptions) then
                    inc(realparamcount);
                if (paraidx<pd.paras.count) and
                   assigned(pd.paras[paraidx]) and
                   (realparamcount = 1) then
                  begin
                    eq:=compare_defs_ext(fromdef,tparavarsym(pd.paras[paraidx]).vardef,nothingn,convtyp,hpd,[]);

                    { alias? if yes, only l1 choice,
                      if you mess with this code, check tw4093 }
                    if (eq=te_exact) and
                       (fromdef<>tparavarsym(pd.paras[paraidx]).vardef) and
                       ((df_unique in fromdef.defoptions) or
                       (df_unique in tparavarsym(pd.paras[paraidx]).vardef.defoptions)) then
                      eq:=te_convert_l1;

                    if eq=te_exact then
                      begin
                        besteq:=eq;
                        result:=pd;
                        exit;
                      end;
                    if eq>besteq then
                      begin
                        bestpd:=pd;
                        besteq:=eq;
                      end;
                  end;
              end;
          end;
        result:=bestpd;
      end;


{****************************************************************************
                                  TERRORSYM
****************************************************************************}

    constructor terrorsym.create;
      begin
        inherited create(errorsym,'');
      end;

{****************************************************************************
                                TPROPERTYSYM
****************************************************************************}

    constructor tpropertysym.create(const n : string);
      var
        pap : tpropaccesslisttypes;
      begin
         inherited create(propertysym,n);
         propoptions:=[];
         index:=0;
         default:=0;
         propdef:=nil;
         indexdef:=nil;
         parast:=nil;
         for pap:=low(tpropaccesslisttypes) to high(tpropaccesslisttypes) do
           propaccesslist[pap]:=tpropaccesslist.create;
      end;


    constructor tpropertysym.ppuload(ppufile:tcompilerppufile);
      var
        pap : tpropaccesslisttypes;
      begin
         inherited ppuload(propertysym,ppufile);
         ppufile.getsmallset(propoptions);
         if ppo_overrides in propoptions then
           ppufile.getderef(overriddenpropsymderef);
         ppufile.getderef(propdefderef);
         index:=ppufile.getlongint;
         default:=ppufile.getlongint;
         ppufile.getderef(indexdefderef);
         for pap:=low(tpropaccesslisttypes) to high(tpropaccesslisttypes) do
           propaccesslist[pap]:=ppufile.getpropaccesslist;
         if [ppo_hasparameters,ppo_overrides]*propoptions=[ppo_hasparameters] then
           begin
             parast:=tparasymtable.create(nil,0);
             tparasymtable(parast).ppuload(ppufile);
           end
         else
           parast:=nil;
      end;


    destructor tpropertysym.destroy;
      var
        pap : tpropaccesslisttypes;
      begin
         for pap:=low(tpropaccesslisttypes) to high(tpropaccesslisttypes) do
           propaccesslist[pap].free;
         parast.free;
         inherited destroy;
      end;


    procedure tpropertysym.buildderef;
      var
        pap : tpropaccesslisttypes;
      begin
        propdefderef.build(propdef);
        indexdefderef.build(indexdef);
        for pap:=low(tpropaccesslisttypes) to high(tpropaccesslisttypes) do
          propaccesslist[pap].buildderef;
        if ppo_overrides in propoptions then
          overriddenpropsymderef.build(overriddenpropsym)
        else
        if ppo_hasparameters in propoptions then
          tparasymtable(parast).buildderef;
      end;


    procedure tpropertysym.deref;
      var
        pap : tpropaccesslisttypes;
      begin
        indexdef:=tdef(indexdefderef.resolve);
        propdef:=tdef(propdefderef.resolve);
        for pap:=low(tpropaccesslisttypes) to high(tpropaccesslisttypes) do
          propaccesslist[pap].resolve;

        if ppo_overrides in propoptions then
          begin
            overriddenpropsym:=tpropertysym(overriddenpropsymderef.resolve);
            if ppo_hasparameters in propoptions then
              parast:=overriddenpropsym.parast.getcopy;
          end
        else
        if ppo_hasparameters in propoptions then
          tparasymtable(parast).deref
      end;


    function tpropertysym.getsize : asizeint;
      begin
         getsize:=0;
      end;


    procedure tpropertysym.ppuwrite(ppufile:tcompilerppufile);
      var
        pap : tpropaccesslisttypes;
      begin
        inherited ppuwrite(ppufile);
        ppufile.putsmallset(propoptions);
        if ppo_overrides in propoptions then
          ppufile.putderef(overriddenpropsymderef);
        ppufile.putderef(propdefderef);
        ppufile.putlongint(index);
        ppufile.putlongint(default);
        ppufile.putderef(indexdefderef);
        for pap:=low(tpropaccesslisttypes) to high(tpropaccesslisttypes) do
          ppufile.putpropaccesslist(propaccesslist[pap]);
        ppufile.writeentry(ibpropertysym);
        if [ppo_hasparameters,ppo_overrides]*propoptions=[ppo_hasparameters] then
          tparasymtable(parast).ppuwrite(ppufile);
      end;


{****************************************************************************
                            TABSTRACTVARSYM
****************************************************************************}

    constructor tabstractvarsym.create(st:tsymtyp;const n : string;vsp:tvarspez;def:tdef;vopts:tvaroptions);
      begin
         inherited create(st,n);
         vardef:=def;
         varspez:=vsp;
         varstate:=vs_declared;
         varoptions:=vopts;
      end;


    constructor tabstractvarsym.ppuload(st:tsymtyp;ppufile:tcompilerppufile);
      begin
         inherited ppuload(st,ppufile);
         varstate:=vs_readwritten;
         varspez:=tvarspez(ppufile.getbyte);
         varregable:=tvarregable(ppufile.getbyte);
         addr_taken:=boolean(ppufile.getbyte);
         ppufile.getderef(vardefderef);
         ppufile.getsmallset(varoptions);
      end;


    destructor tabstractvarsym.destroy;
      begin
        if assigned(notifications) then
          notifications.destroy;
        inherited destroy;
      end;


    procedure tabstractvarsym.buildderef;
      begin
        vardefderef.build(vardef);
      end;


    procedure tabstractvarsym.deref;
      var
        oldvarregable: tvarregable;
      begin
        { setting the vardef also updates varregable. We just loaded this }
        { value from a ppu, so it must not be changed (e.g. tw7817a.pp/   }
        { tw7817b.pp: the address is taken of a local variable in an      }
        { inlined procedure -> must remain non-regable when inlining)     }
        oldvarregable:=varregable;
        vardef:=tdef(vardefderef.resolve);
        varregable:=oldvarregable;
      end;


    procedure tabstractvarsym.ppuwrite(ppufile:tcompilerppufile);
      var
        oldintfcrc : boolean;
      begin
         inherited ppuwrite(ppufile);
         ppufile.putbyte(byte(varspez));
         oldintfcrc:=ppufile.do_crc;
         ppufile.do_crc:=false;
         ppufile.putbyte(byte(varregable));
         ppufile.putbyte(byte(addr_taken));
         ppufile.do_crc:=oldintfcrc;
         ppufile.putderef(vardefderef);
         ppufile.putsmallset(varoptions);
      end;


    function tabstractvarsym.getsize : asizeint;
      begin
        if assigned(vardef) and
           ((vardef.typ<>arraydef) or
            is_dynamic_array(vardef) or
            (tarraydef(vardef).highrange>=tarraydef(vardef).lowrange)) then
          result:=vardef.size
        else
          result:=0;
      end;


    function  tabstractvarsym.getpackedbitsize : longint;
      begin
        { bitpacking is only done for ordinals }
        if not is_ordinal(vardef) then
          internalerror(2006082010);
        result:=vardef.packedbitsize;
      end;


    function tabstractvarsym.is_regvar(refpara: boolean):boolean;
      begin
        { Register variables are not allowed in the following cases:
           - regvars are disabled
           - exceptions are used (after an exception is raised the contents of the
               registers is not valid anymore)
           - it has a local copy
           - the value needs to be in memory (i.e. reference counted) }
        result:=(cs_opt_regvar in current_settings.optimizerswitches) and
                not(pi_has_assembler_block in current_procinfo.flags) and
                not(pi_uses_exceptions in current_procinfo.flags) and
                not(pi_has_interproclabel in current_procinfo.flags) and
                not(vo_has_local_copy in varoptions) and
                ((refpara and
                  (varregable <> vr_none)) or
                 (not refpara and
                  not(varregable in [vr_none,vr_addr])))
{$if not defined(powerpc) and not defined(powerpc64)}
                and ((vardef.typ <> recorddef) or
                     (varregable = vr_addr) or
                     not(varstate in [vs_written,vs_readwritten]));
{$endif}
      end;


    procedure tabstractvarsym.trigger_notifications(what:Tnotification_flag);

    var n:Tnotification;

    begin
        if assigned(notifications) then
          begin
            n:=Tnotification(notifications.first);
            while assigned(n) do
              begin
                if what in n.flags then
                  n.callback(what,self);
                n:=Tnotification(n.next);
              end;
          end;
    end;

    function Tabstractvarsym.register_notification(flags:Tnotification_flags;callback:
                                           Tnotification_callback):cardinal;

    var n:Tnotification;

    begin
      if not assigned(notifications) then
        notifications:=Tlinkedlist.create;
      n:=Tnotification.create(flags,callback);
      register_notification:=n.id;
      notifications.concat(n);
    end;

    procedure Tabstractvarsym.unregister_notification(id:cardinal);

    var n:Tnotification;

    begin
      if not assigned(notifications) then
        internalerror(200212311)
      else
        begin
            n:=Tnotification(notifications.first);
            while assigned(n) do
              begin
                if n.id=id then
                  begin
                    notifications.remove(n);
                    n.destroy;
                    exit;
                  end;
                n:=Tnotification(n.next);
              end;
            internalerror(200212311)
        end;
    end;


    procedure tabstractvarsym.setvardef(def:tdef);
      begin
        _vardef := def;
         { can we load the value into a register ? }
        if not assigned(owner) or
           (owner.symtabletype in [localsymtable,parasymtable]) or
           (
            (owner.symtabletype=staticsymtable) and
            not(cs_create_pic in current_settings.moduleswitches)
           ) then
          begin
            if tstoreddef(vardef).is_intregable then
              varregable:=vr_intreg
            else
{ $warning TODO: no fpu regvar in staticsymtable yet, need initialization with 0 }
              if {(
                  not assigned(owner) or
                  (owner.symtabletype<>staticsymtable)
                 ) and }
                 tstoreddef(vardef).is_fpuregable then
                 begin
                   if use_vectorfpu(vardef) then
                     varregable:=vr_mmreg
                   else
                     varregable:=vr_fpureg;
                 end;
          end;
      end;


{****************************************************************************
                               TFIELDVARSYM
****************************************************************************}

    constructor tfieldvarsym.create(const n : string;vsp:tvarspez;def:tdef;vopts:tvaroptions);
      begin
         inherited create(fieldvarsym,n,vsp,def,vopts);
         fieldoffset:=-1;
      end;


    constructor tfieldvarsym.ppuload(ppufile:tcompilerppufile);
      begin
         inherited ppuload(fieldvarsym,ppufile);
         fieldoffset:=ppufile.getaint;
         if (vo_has_mangledname in varoptions) then
           externalname:=stringdup(ppufile.getstring)
         else
           externalname:=nil;
      end;


    procedure tfieldvarsym.ppuwrite(ppufile:tcompilerppufile);
      begin
         inherited ppuwrite(ppufile);
         ppufile.putaint(fieldoffset);
         if (vo_has_mangledname in varoptions) then
           ppufile.putstring(externalname^);
         ppufile.writeentry(ibfieldvarsym);
      end;


    procedure tfieldvarsym.set_externalname(const s: string);
      begin
        { make sure it is recalculated }
{$ifdef symansistr}
        cachedmangledname:='';
{$else symansistr}
        stringdispose(cachedmangledname);
{$endif symansistr}
{$ifdef jvm}
        if is_java_class_or_interface(tdef(owner.defowner)) then
          begin
            externalname:=stringdup(s);
            include(varoptions,vo_has_mangledname);
          end
        else
{$endif jvm}
          internalerror(2011031201);
      end;


    function tfieldvarsym.mangledname:TSymStr;
      var
        srsym : tsym;
        srsymtable : tsymtable;
      begin
{$ifdef jvm}
        if is_java_class_or_interface(tdef(owner.defowner)) or
           (tdef(owner.defowner).typ=recorddef) then
          begin
            if cachedmangledname<>'' then
              result:=cachedmangledname
            else
              begin
                result:=jvmmangledbasename(self,false);
                jvmaddtypeownerprefix(owner,result);
                cachedmangledname:=result;
              end;
          end
        else
{$endif jvm}
        if sp_static in symoptions then
          begin
            if searchsym(lower(owner.name^)+'_'+name,srsym,srsymtable) then
              result:=srsym.mangledname
            { when generating the debug info for the module in which the }
            { symbol is defined, the localsymtable of that module is     }
            { already popped from the symtablestack                      }
            else if searchsym_in_module(current_module,lower(owner.name^)+'_'+name,srsym,srsymtable) then
              result:=srsym.mangledname
            else
              internalerror(2007012501);
          end
        else if is_objcclass(tdef(owner.defowner)) then
          begin
{$ifdef symansistr}
            if cachedmangledname<>'' then
              result:=cachedmangledname
{$else symansistr}
            if assigned(cachedmangledname) then
              result:=cachedmangledname^
{$endif symansistr}
            else
              begin
                result:=target_info.cprefix+'OBJC_IVAR_$_'+tobjectdef(owner.defowner).objextname^+'.'+RealName;
{$ifdef symansistr}
                cachedmangledname:=result;
{$else symansistr}
                cachedmangledname:=stringdup(result);
{$endif symansistr}
              end;
          end
        else
          result:=inherited mangledname;
      end;


    destructor tfieldvarsym.destroy;
      begin
{$ifndef symansistr}
        stringdispose(cachedmangledname);
{$endif symansistr}
        stringdispose(externalname);
        inherited destroy;
      end;


{****************************************************************************
                        TABSTRACTNORMALVARSYM
****************************************************************************}

    constructor tabstractnormalvarsym.create(st:tsymtyp;const n : string;vsp:tvarspez;def:tdef;vopts:tvaroptions);
      begin
         inherited create(st,n,vsp,def,vopts);
         fillchar(localloc,sizeof(localloc),0);
         fillchar(initialloc,sizeof(initialloc),0);
         defaultconstsym:=nil;
      end;


    constructor tabstractnormalvarsym.ppuload(st:tsymtyp;ppufile:tcompilerppufile);
      begin
         inherited ppuload(st,ppufile);
         fillchar(localloc,sizeof(localloc),0);
         fillchar(initialloc,sizeof(initialloc),0);
         ppufile.getderef(defaultconstsymderef);
      end;


    procedure tabstractnormalvarsym.buildderef;
      begin
        inherited buildderef;
        defaultconstsymderef.build(defaultconstsym);
      end;


    procedure tabstractnormalvarsym.deref;
      begin
        inherited deref;
        defaultconstsym:=tsym(defaultconstsymderef.resolve);
      end;


    procedure tabstractnormalvarsym.ppuwrite(ppufile:tcompilerppufile);
      begin
         inherited ppuwrite(ppufile);
         ppufile.putderef(defaultconstsymderef);
      end;


{****************************************************************************
                             Tstaticvarsym
****************************************************************************}

    constructor tstaticvarsym.create(const n : string;vsp:tvarspez;def:tdef;vopts:tvaroptions);
      begin
         inherited create(staticvarsym,n,vsp,def,vopts);
{$ifdef symansistr}
         _mangledname:='';
{$else symansistr}
         _mangledname:=nil;
{$endif symansistr}
      end;


    constructor tstaticvarsym.create_dll(const n : string;vsp:tvarspez;def:tdef);
      begin
         tstaticvarsym(self).create(n,vsp,def,[vo_is_dll_var]);
      end;


    constructor tstaticvarsym.create_C(const n: string; const mangled : TSymStr;vsp:tvarspez;def:tdef);
      begin
         tstaticvarsym(self).create(n,vsp,def,[]);
         set_mangledname(mangled);
      end;


    constructor tstaticvarsym.ppuload(ppufile:tcompilerppufile);
      begin
         inherited ppuload(staticvarsym,ppufile);
{$ifdef symansistr}
         if vo_has_mangledname in varoptions then
           _mangledname:=ppufile.getansistring
         else
           _mangledname:='';
{$else symansistr}
         if vo_has_mangledname in varoptions then
           _mangledname:=stringdup(ppufile.getstring)
         else
           _mangledname:=nil;
         if vo_has_section in varoptions then
           section:=ppufile.getansistring;
{$endif symansistr}
      end;


    destructor tstaticvarsym.destroy;
      begin
{$ifndef symansistr}
        if assigned(_mangledname) then
          begin
{$ifdef MEMDEBUG}
            memmanglednames.start;
{$endif MEMDEBUG}
            stringdispose(_mangledname);
{$ifdef MEMDEBUG}
            memmanglednames.stop;
{$endif MEMDEBUG}
          end;
        stringdispose(_mangledbasename);
{$endif}
        inherited destroy;
      end;


    procedure tstaticvarsym.ppuwrite(ppufile:tcompilerppufile);
      begin
         inherited ppuwrite(ppufile);
         { write mangledname rather than _mangledname in case the mangledname
           has not been calculated yet (can happen in case only the
           mangledbasename has been set) }
         if vo_has_mangledname in varoptions then
{$ifdef symansistr}
           ppufile.putansistring(mangledname);
{$else symansistr}
           ppufile.putstring(mangledname);
{$endif symansistr}
         if vo_has_section in varoptions then
           ppufile.putansistring(section);
         ppufile.writeentry(ibstaticvarsym);
      end;


    function tstaticvarsym.mangledname:TSymStr;
{$ifndef jvm}
      var
        usename,
        prefix : TSymStr;
{$endif jvm}
      begin
{$ifdef symansistr}
        if _mangledname='' then
{$else symansistr}
        if not assigned(_mangledname) then
{$endif symansistr}
          begin
{$ifdef jvm}
            if _mangledbasename='' then
              _mangledname:=jvmmangledbasename(self,false)
            else
              _mangledname:=jvmmangledbasename(self,_mangledbasename,false);
            jvmaddtypeownerprefix(owner,_mangledname);
{$else jvm}
            if (vo_is_typed_const in varoptions) then
              prefix:='TC'
            else
              prefix:='U';
  {$ifdef symansistr}
            if _mangledbasename='' then
              usename:=name
            else
              usename:=_mangledbasename;
  {$else symansistr}
            if not assigned(_mangledbasename) then
              usename:=name
            else
              usename:=_mangledbasename^;
  {$endif symansistr}
{$ifdef compress}
            {$error add ansistring support for symansistr}
            _mangledname:=stringdup(minilzw_encode(make_mangledname(prefix,owner,usename)));
{$else compress}
  {$ifdef symansistr}
           _mangledname:=make_mangledname(prefix,owner,usename);
  {$else symansistr}
           _mangledname:=stringdup(make_mangledname(prefix,owner,usename));
  {$endif symansistr}
{$endif compress}
{$endif jvm}
          end;
{$ifdef symansistr}
        result:=_mangledname;
{$else symansistr}
        result:=_mangledname^;
{$endif symansistr}
      end;


    procedure tstaticvarsym.set_mangledbasename(const s: TSymStr);
      begin
{$ifdef symansistr}
        _mangledbasename:=s;
        _mangledname:='';
{$else symansistr}
        stringdispose(_mangledname);
        stringdispose(_mangledbasename);
        _mangledbasename:=stringdup(s);
{$endif symansistr}
        include(varoptions,vo_has_mangledname);
      end;


    function tstaticvarsym.mangledbasename: TSymStr;
      begin
{$ifdef symansistr}
        result:=_mangledbasename;
{$else symansistr}
        if assigned(_mangledbasename) then
          result:=_mangledbasename^
        else
          result:='';
{$endif symansistr}
      end;


    procedure tstaticvarsym.set_mangledname(const s:TSymStr);
      begin
{$ifndef symansistr}
        stringdispose(_mangledname);
{$endif}
{$if defined(jvm)}
        _mangledname:=jvmmangledbasename(self,s,false);
        jvmaddtypeownerprefix(owner,_mangledname);
{$elseif defined(compress)}
        _mangledname:=stringdup(minilzw_encode(s));
{$else}
  {$ifdef symansistr}
        _mangledname:=s;
  {$else symansistr}
        _mangledname:=stringdup(s);
  {$endif symansistr}
{$endif}
        include(varoptions,vo_has_mangledname);
      end;


    procedure tstaticvarsym.set_raw_mangledname(const s: TSymStr);
      begin
{$ifndef symansistr}
        stringdispose(_mangledname);
        _mangledname:=stringdup(s);
{$else}
        _mangledname:=s;
{$endif}
        include(varoptions,vo_has_mangledname);
      end;


{****************************************************************************
                               TLOCALVARSYM
****************************************************************************}

    constructor tlocalvarsym.create(const n : string;vsp:tvarspez;def:tdef;vopts:tvaroptions);
      begin
         inherited create(localvarsym,n,vsp,def,vopts);
      end;


    constructor tlocalvarsym.ppuload(ppufile:tcompilerppufile);
      begin
         inherited ppuload(localvarsym,ppufile);
      end;


    procedure tlocalvarsym.ppuwrite(ppufile:tcompilerppufile);
      begin
         inherited ppuwrite(ppufile);
         ppufile.writeentry(iblocalvarsym);
      end;


{****************************************************************************
                              TPARAVARSYM
****************************************************************************}

    constructor tparavarsym.create(const n : string;nr:word;vsp:tvarspez;def:tdef;vopts:tvaroptions);
      begin
         inherited create(paravarsym,n,vsp,def,vopts);
         if (vsp in [vs_var,vs_value,vs_const,vs_constref]) and
            not(vo_is_funcret in vopts) then
           varstate := vs_initialised;
         paranr:=nr;
         paraloc[calleeside].init;
         paraloc[callerside].init;
      end;


    destructor tparavarsym.destroy;
      begin
        paraloc[calleeside].done;
        paraloc[callerside].done;
        inherited destroy;
      end;


    constructor tparavarsym.ppuload(ppufile:tcompilerppufile);
      var
        b : byte;
      begin
         inherited ppuload(paravarsym,ppufile);
         paranr:=ppufile.getword;
         univpara:=boolean(ppufile.getbyte);

         { The var state of parameter symbols is fixed after writing them so
           we write them to the unit file.
           This enables constant folding for inline procedures loaded from units
         }
         varstate:=tvarstate(ppufile.getbyte);

         paraloc[calleeside].init;
         paraloc[callerside].init;
         if vo_has_explicit_paraloc in varoptions then
           begin
             paraloc[callerside].alignment:=ppufile.getbyte;
             b:=ppufile.getbyte;
             if b<>sizeof(paraloc[callerside].location^) then
               internalerror(200411154);
             ppufile.getdata(paraloc[callerside].add_location^,sizeof(paraloc[callerside].location^));
             paraloc[callerside].size:=paraloc[callerside].location^.size;
             paraloc[callerside].intsize:=tcgsize2size[paraloc[callerside].size];
           end;
      end;


    procedure tparavarsym.ppuwrite(ppufile:tcompilerppufile);
      var
        oldintfcrc : boolean;
      begin
         inherited ppuwrite(ppufile);
         ppufile.putword(paranr);
         ppufile.putbyte(byte(univpara));

         { The var state of parameter symbols is fixed after writing them so
           we write them to the unit file.
           This enables constant folding for inline procedures loaded from units
         }
         oldintfcrc:=ppufile.do_crc;
         ppufile.do_crc:=false;
         ppufile.putbyte(ord(varstate));
         ppufile.do_crc:=oldintfcrc;

         if vo_has_explicit_paraloc in varoptions then
           begin
             paraloc[callerside].check_simple_location;
             ppufile.putbyte(sizeof(paraloc[callerside].alignment));
             ppufile.putbyte(sizeof(paraloc[callerside].location^));
             ppufile.putdata(paraloc[callerside].location^,sizeof(paraloc[callerside].location^));
           end;
         ppufile.writeentry(ibparavarsym);
      end;

    function tparavarsym.needs_finalization:boolean;
      begin
        result:=(varspez=vs_value) and
          (is_managed_type(vardef) or
            (
              (not (tabstractprocdef(owner.defowner).proccalloption in cdecl_pocalls)) and
              (not paramanager.use_stackalloc) and
              (is_open_array(vardef) or is_array_of_const(vardef))
            )
          );
      end;

{****************************************************************************
                               TABSOLUTEVARSYM
****************************************************************************}

    constructor tabsolutevarsym.create(const n : string;def:tdef);
      begin
        inherited create(absolutevarsym,n,vs_value,def,[]);
        ref:=nil;
      end;


    constructor tabsolutevarsym.create_ref(const n : string;def:tdef;_ref:tpropaccesslist);
      begin
        inherited create(absolutevarsym,n,vs_value,def,[]);
        ref:=_ref;
      end;


    destructor tabsolutevarsym.destroy;
      begin
        if assigned(ref) then
          ref.free;
        inherited destroy;
      end;


    constructor tabsolutevarsym.ppuload(ppufile:tcompilerppufile);
      begin
         inherited ppuload(absolutevarsym,ppufile);
         ref:=nil;
         asmname:=nil;
         abstyp:=absolutetyp(ppufile.getbyte);
{$ifdef i386}
         absseg:=false;
{$endif i386}
         case abstyp of
           tovar :
             ref:=ppufile.getpropaccesslist;
           toasm :
             asmname:=stringdup(ppufile.getstring);
           toaddr :
             begin
               addroffset:=ppufile.getaword;
{$ifdef i386}
               absseg:=boolean(ppufile.getbyte);
{$endif i386}
             end;
         end;
      end;


    procedure tabsolutevarsym.ppuwrite(ppufile:tcompilerppufile);
      begin
         inherited ppuwrite(ppufile);
         ppufile.putbyte(byte(abstyp));
         case abstyp of
           tovar :
             ppufile.putpropaccesslist(ref);
           toasm :
             ppufile.putstring(asmname^);
           toaddr :
             begin
               ppufile.putaword(addroffset);
{$ifdef i386}
               ppufile.putbyte(byte(absseg));
{$endif i386}
             end;
         end;
         ppufile.writeentry(ibabsolutevarsym);
      end;


    procedure tabsolutevarsym.buildderef;
      begin
        inherited buildderef;
        if (abstyp=tovar) then
          ref.buildderef;
      end;


    procedure tabsolutevarsym.deref;
      begin
         inherited deref;
         { own absolute deref }
         if (abstyp=tovar) then
           ref.resolve;
      end;


    function tabsolutevarsym.mangledname : TSymStr;
      begin
         case abstyp of
           toasm :
             mangledname:=asmname^;
           toaddr :
             mangledname:='$'+tostr(addroffset);
           else
             internalerror(200411062);
         end;
      end;


{****************************************************************************
                                  TCONSTSYM
****************************************************************************}

    constructor tconstsym.create_ord(const n : string;t : tconsttyp;v : tconstexprint;def:tdef);
      begin
         inherited create(constsym,n);
         fillchar(value, sizeof(value), #0);
         consttyp:=t;
         value.valueord:=v;
         constdef:=def;
      end;


    constructor tconstsym.create_ordptr(const n : string;t : tconsttyp;v : tconstptruint;def:tdef);
      begin
         inherited create(constsym,n);
         fillchar(value, sizeof(value), #0);
         consttyp:=t;
         value.valueordptr:=v;
         constdef:=def;
      end;


    constructor tconstsym.create_ptr(const n : string;t : tconsttyp;v : pointer;def:tdef);
      begin
         inherited create(constsym,n);
         fillchar(value, sizeof(value), #0);
         consttyp:=t;
         value.valueptr:=v;
         constdef:=def;
      end;


    constructor tconstsym.create_string(const n : string;t : tconsttyp;str:pchar;l:longint);
      begin
         inherited create(constsym,n);
         fillchar(value, sizeof(value), #0);
         consttyp:=t;
         value.valueptr:=str;
         constdef:=nil;
         value.len:=l;
      end;


    constructor tconstsym.create_wstring(const n : string;t : tconsttyp;pw:pcompilerwidestring);
      begin
         inherited create(constsym,n);
         fillchar(value, sizeof(value), #0);
         consttyp:=t;
         pcompilerwidestring(value.valueptr):=pw;
         constdef:=nil;
         value.len:=getlengthwidestring(pw);
      end;


    constructor tconstsym.ppuload(ppufile:tcompilerppufile);
      var
         pd : pbestreal;
         ps : pnormalset;
         pc : pchar;
         pw : pcompilerwidestring;
         i  : longint;
      begin
         inherited ppuload(constsym,ppufile);
         constdef:=nil;
         consttyp:=tconsttyp(ppufile.getbyte);
         fillchar(value, sizeof(value), #0);
         case consttyp of
           constord :
             begin
               ppufile.getderef(constdefderef);
               value.valueord:=ppufile.getexprint;
             end;
           constpointer :
             begin
               ppufile.getderef(constdefderef);
               value.valueordptr:=ppufile.getptruint;
             end;
           constwstring :
             begin
               initwidestring(pw);
               setlengthwidestring(pw,ppufile.getlongint);
               { don't use getdata, because the compilerwidechars may have to
                 be byteswapped
               }
{$if sizeof(tcompilerwidechar) = 2}
               for i:=0 to pw^.len-1 do
                 pw^.data[i]:=ppufile.getword;
{$elseif sizeof(tcompilerwidechar) = 4}
               for i:=0 to pw^.len-1 do
                 pw^.data[i]:=cardinal(ppufile.getlongint);
{$else}
              {$error Unsupported tcompilerwidechar size}
{$endif}
               pcompilerwidestring(value.valueptr):=pw;
             end;
           conststring,
           constresourcestring :
             begin
               value.len:=ppufile.getlongint;
               getmem(pc,value.len+1);
               ppufile.getdata(pc^,value.len);
               pc[value.len]:=#0;
               value.valueptr:=pc;
             end;
           constreal :
             begin
               ppufile.getderef(constdefderef);
               new(pd);
               pd^:=ppufile.getreal;
               value.valueptr:=pd;
             end;
           constset :
             begin
               ppufile.getderef(constdefderef);
               new(ps);
               ppufile.getnormalset(ps^);
               value.valueptr:=ps;
             end;
           constguid :
             begin
               new(pguid(value.valueptr));
               ppufile.getdata(value.valueptr^,sizeof(tguid));
             end;
           constnil : ;
           else
             Message1(unit_f_ppu_invalid_entry,tostr(ord(consttyp)));
         end;
      end;


    destructor tconstsym.destroy;
      begin
        case consttyp of
          conststring,
          constresourcestring :
            freemem(pchar(value.valueptr),value.len+1);
          constwstring :
            donewidestring(pcompilerwidestring(value.valueptr));
          constreal :
            dispose(pbestreal(value.valueptr));
          constset :
            dispose(pnormalset(value.valueptr));
          constguid :
            dispose(pguid(value.valueptr));
        end;
        inherited destroy;
      end;


    procedure tconstsym.buildderef;
      begin
        if consttyp in [constord,constreal,constpointer,constset] then
          constdefderef.build(constdef);
      end;


    procedure tconstsym.deref;
      begin
        if consttyp in [constord,constreal,constpointer,constset] then
          constdef:=tdef(constdefderef.resolve);
      end;


    procedure tconstsym.ppuwrite(ppufile:tcompilerppufile);
      begin
         inherited ppuwrite(ppufile);
         ppufile.putbyte(byte(consttyp));
         case consttyp of
           constnil : ;
           constord :
             begin
               ppufile.putderef(constdefderef);
               ppufile.putexprint(value.valueord);
             end;
           constpointer :
             begin
               ppufile.putderef(constdefderef);
               ppufile.putptruint(value.valueordptr);
             end;
           constwstring :
             begin
               ppufile.putlongint(getlengthwidestring(pcompilerwidestring(value.valueptr)));
               ppufile.putdata(pcompilerwidestring(value.valueptr)^.data^,pcompilerwidestring(value.valueptr)^.len*sizeof(tcompilerwidechar));
             end;
           conststring,
           constresourcestring :
             begin
               ppufile.putlongint(value.len);
               ppufile.putdata(pchar(value.valueptr)^,value.len);
             end;
           constreal :
             begin
               ppufile.putderef(constdefderef);
               ppufile.putreal(pbestreal(value.valueptr)^);
             end;
           constset :
             begin
               ppufile.putderef(constdefderef);
               ppufile.putnormalset(value.valueptr^);
             end;
           constguid :
             ppufile.putdata(value.valueptr^,sizeof(tguid));
         else
           internalerror(13);
         end;
        ppufile.writeentry(ibconstsym);
      end;


{****************************************************************************
                                  TENUMSYM
****************************************************************************}

    constructor tenumsym.create(const n : string;def : tenumdef;v : longint);
      begin
         inherited create(enumsym,n);
         definition:=def;
         value:=v;
      end;


    constructor tenumsym.ppuload(ppufile:tcompilerppufile);
      begin
         inherited ppuload(enumsym,ppufile);
         ppufile.getderef(definitionderef);
         value:=ppufile.getlongint;
      end;


    procedure tenumsym.buildderef;
      begin
         definitionderef.build(definition);
      end;


    procedure tenumsym.deref;
      begin
         definition:=tenumdef(definitionderef.resolve);
      end;

    procedure tenumsym.ppuwrite(ppufile:tcompilerppufile);
      begin
         inherited ppuwrite(ppufile);
         ppufile.putderef(definitionderef);
         ppufile.putlongint(value);
         ppufile.writeentry(ibenumsym);
      end;


{****************************************************************************
                                  TTYPESYM
****************************************************************************}

    constructor ttypesym.create(const n : string;def:tdef);

      begin
        inherited create(typesym,n);
        typedef:=def;
        { register the typesym for the definition }
        if assigned(typedef) and
           (typedef.typ<>errordef) and
           not(assigned(typedef.typesym)) then
         typedef.typesym:=self;
      end;


    constructor ttypesym.ppuload(ppufile:tcompilerppufile);
      begin
         inherited ppuload(typesym,ppufile);
         ppufile.getderef(typedefderef);
         fprettyname:=ppufile.getansistring;
      end;


    procedure ttypesym.buildderef;
      begin
        typedefderef.build(typedef);
      end;


    procedure ttypesym.deref;
      begin
        typedef:=tdef(typedefderef.resolve);
      end;


    procedure ttypesym.ppuwrite(ppufile:tcompilerppufile);
      begin
         inherited ppuwrite(ppufile);
         ppufile.putderef(typedefderef);
         ppufile.putansistring(fprettyname);
         ppufile.writeentry(ibtypesym);
      end;


    function ttypesym.prettyname : string;
      begin
        if fprettyname<>'' then
          result:=fprettyname
        else
          result:=inherited prettyname;
      end;


{****************************************************************************
                                  TSYSSYM
****************************************************************************}

    constructor tsyssym.create(const n : string;l : longint);
      begin
         inherited create(syssym,n);
         number:=l;
      end;

    constructor tsyssym.ppuload(ppufile:tcompilerppufile);
      begin
         inherited ppuload(syssym,ppufile);
         number:=ppufile.getlongint;
      end;

    destructor tsyssym.destroy;
      begin
        inherited destroy;
      end;

    procedure tsyssym.ppuwrite(ppufile:tcompilerppufile);
      begin
         inherited ppuwrite(ppufile);
         ppufile.putlongint(number);
         ppufile.writeentry(ibsyssym);
      end;


{*****************************************************************************
                                 TMacro
*****************************************************************************}

    constructor tmacro.create(const n : string);
      begin
         inherited create(macrosym,n);
         owner:=nil;
         defined:=false;
         is_used:=false;
         is_compiler_var:=false;
         buftext:=nil;
         buflen:=0;
      end;

    constructor tmacro.ppuload(ppufile:tcompilerppufile);
      begin
         inherited ppuload(macrosym,ppufile);
         defined:=boolean(ppufile.getbyte);
         is_compiler_var:=boolean(ppufile.getbyte);
         is_used:=false;
         buflen:= ppufile.getlongint;
         if buflen > 0 then
           begin
             getmem(buftext, buflen);
             ppufile.getdata(buftext^, buflen)
           end
         else
           buftext:=nil;
      end;

    destructor tmacro.destroy;
      begin
         if assigned(buftext) then
           freemem(buftext);
         inherited destroy;
      end;

    procedure tmacro.ppuwrite(ppufile:tcompilerppufile);
      begin
         inherited ppuwrite(ppufile);
         ppufile.putbyte(byte(defined));
         ppufile.putbyte(byte(is_compiler_var));
         ppufile.putlongint(buflen);
         if buflen > 0 then
           ppufile.putdata(buftext^,buflen);
         ppufile.writeentry(ibmacrosym);
      end;


    function tmacro.GetCopy:tmacro;
      var
        p : tmacro;
      begin
        p:=tmacro.create(realname);
        p.defined:=defined;
        p.is_used:=is_used;
        p.is_compiler_var:=is_compiler_var;
        p.buflen:=buflen;
        if assigned(buftext) then
          begin
            getmem(p.buftext,buflen);
            move(buftext^,p.buftext^,buflen);
          end;
        Result:=p;
      end;

end.
