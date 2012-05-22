{
    Copyright (c) 1998-2002 by Florian Klaempfl, Pierre Muller

    This unit handles the symbol tables

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
unit symtable;

{$i fpcdefs.inc}

interface

    uses
       { common }
       cutils,cclasses,
       { global }
       cpuinfo,globtype,tokens,
       { symtable }
       symconst,symbase,symtype,symdef,symsym,
       { ppu }
       ppu,
       { assembler }
       aasmtai,aasmdata
       ;


{****************************************************************************
                             Symtable types
****************************************************************************}

    type
       tstoredsymtable = class(TSymtable)
       private
          b_needs_init_final : boolean;
          procedure _needs_init_final(sym:TObject;arg:pointer);
          procedure check_forward(sym:TObject;arg:pointer);
          procedure labeldefined(sym:TObject;arg:pointer);
          procedure varsymbolused(sym:TObject;arg:pointer);
          procedure TestPrivate(sym:TObject;arg:pointer);
          procedure objectprivatesymbolused(sym:TObject;arg:pointer);
          procedure loaddefs(ppufile:tcompilerppufile);
          procedure loadsyms(ppufile:tcompilerppufile);
          procedure writedefs(ppufile:tcompilerppufile);
          procedure writesyms(ppufile:tcompilerppufile);
       public
          procedure insert(sym:TSymEntry;checkdup:boolean=true);override;
          procedure delete(sym:TSymEntry);override;
          { load/write }
          procedure ppuload(ppufile:tcompilerppufile);virtual;
          procedure ppuwrite(ppufile:tcompilerppufile);virtual;
          procedure buildderef;virtual;
          procedure buildderefimpl;virtual;
          procedure deref;virtual;
          procedure derefimpl;virtual;
          function  checkduplicate(var hashedid:THashedIDString;sym:TSymEntry):boolean;override;
          procedure allsymbolsused;
          procedure allprivatesused;
          procedure check_forwards;
          procedure checklabels;
          function  needs_init_final : boolean;
          procedure testfordefaultproperty(sym:TObject;arg:pointer);
       end;

       tabstractrecordsymtable = class(tstoredsymtable)
       public
          usefieldalignment,     { alignment to use for fields (PACKRECORDS value), C_alignment is C style }
          recordalignment,       { alignment desired when inserting this record }
          fieldalignment,        { alignment current alignment used when fields are inserted }
          padalignment : shortint;   { size to a multiple of which the symtable has to be rounded up }
          constructor create(const n:string;usealign:shortint);
          procedure ppuload(ppufile:tcompilerppufile);override;
          procedure ppuwrite(ppufile:tcompilerppufile);override;
          procedure alignrecord(fieldoffset:asizeint;varalign:shortint);
          procedure addfield(sym:tfieldvarsym;vis:tvisibility);
          procedure addalignmentpadding;
          procedure insertdef(def:TDefEntry);override;
          function is_packed: boolean;
          function has_single_field(out sym:tfieldvarsym): boolean;
          function get_unit_symtable: tsymtable;
        protected
          { size in bytes including padding }
          _datasize      : asizeint;
          { size in bits of the data in case of bitpacked record. Only important during construction, }
          { no need to save in/restore from ppu file. datasize is always (databitsize+7) div 8.       }
          databitsize    : asizeint;
          { size in bytes of padding }
          _paddingsize   : word;
          procedure setdatasize(val: asizeint);
        public
          function iscurrentunit: boolean; override;
          property datasize : asizeint read _datasize write setdatasize;
          property paddingsize: word read _paddingsize write _paddingsize;
       end;

       trecordsymtable = class(tabstractrecordsymtable)
       public
          constructor create(const n:string;usealign:shortint);
          procedure insertunionst(unionst : trecordsymtable;offset : longint);
       end;

       tObjectSymtable = class(tabstractrecordsymtable)
       public
          constructor create(adefowner:tdef;const n:string;usealign:shortint);
          function  checkduplicate(var hashedid:THashedIDString;sym:TSymEntry):boolean;override;
       end;

       { tabstractlocalsymtable }

       tabstractlocalsymtable = class(tstoredsymtable)
       public
          procedure ppuwrite(ppufile:tcompilerppufile);override;
          function count_locals:longint;
       end;

       tlocalsymtable = class(tabstractlocalsymtable)
       public
          constructor create(adefowner:tdef;level:byte);
          function checkduplicate(var hashedid:THashedIDString;sym:TSymEntry):boolean;override;
       end;

       { tparasymtable }

       tparasymtable = class(tabstractlocalsymtable)
       public
          readonly: boolean;
          constructor create(adefowner:tdef;level:byte);
          function checkduplicate(var hashedid:THashedIDString;sym:TSymEntry):boolean;override;
          procedure insertdef(def:TDefEntry);override;
       end;

       tabstractuniTSymtable = class(tstoredsymtable)
       public
          constructor create(const n : string;id:word);
          function checkduplicate(var hashedid:THashedIDString;sym:TSymEntry):boolean;override;
          function iscurrentunit:boolean;override;
          procedure insertunit(sym:TSymEntry);
       end;

       tglobalsymtable = class(tabstractuniTSymtable)
       public
          unittypecount : word;
          constructor create(const n : string;id:word);
          procedure ppuload(ppufile:tcompilerppufile);override;
          procedure ppuwrite(ppufile:tcompilerppufile);override;
       end;

       tstaticsymtable = class(tabstractuniTSymtable)
       public
          constructor create(const n : string;id:word);
          procedure ppuload(ppufile:tcompilerppufile);override;
          procedure ppuwrite(ppufile:tcompilerppufile);override;
          function  checkduplicate(var hashedid:THashedIDString;sym:TSymEntry):boolean;override;
       end;

       tspecializesymtable = class(tglobalsymtable)
       public
          constructor create(const n : string;id:word);
          function iscurrentunit:boolean;override;
       end;

       twithsymtable = class(TSymtable)
          withrefnode : tobject; { tnode }
          constructor create(aowner:tdef;ASymList:TFPHashObjectList;refnode:tobject{tnode});
          destructor  destroy;override;
          procedure clear;override;
          procedure insertdef(def:TDefEntry);override;
        end;

       tstt_excepTSymtable = class(TSymtable)
       public
          constructor create;
       end;

       tmacrosymtable = class(tstoredsymtable)
       public
          constructor create(exported: boolean);
       end;

       { tenumsymtable }

       tenumsymtable = class(tstoredsymtable)
       public
          procedure insert(sym: TSymEntry; checkdup: boolean = true); override;
          constructor create(adefowner:tdef);
       end;

       { tarraysymtable }

       tarraysymtable = class(tstoredsymtable)
       public
          procedure insertdef(def:TDefEntry);override;
          constructor create(adefowner:tdef);
       end;

    var
       systemunit     : tglobalsymtable; { pointer to the system unit }


{****************************************************************************
                             Functions
****************************************************************************}

{*** Misc ***}
    function  FullTypeName(def,otherdef:tdef):string;
    function generate_nested_name(symtable:tsymtable;delimiter:string):string;
    procedure incompatibletypes(def1,def2:tdef);
    procedure hidesym(sym:TSymEntry);
    procedure duplicatesym(var hashedid:THashedIDString;dupsym,origsym:TSymEntry);
    function handle_generic_dummysym(sym:TSymEntry;var symoptions:tsymoptions):boolean;

{*** Search ***}
    procedure addsymref(sym:tsym);
    function  is_owned_by(childdef,ownerdef:tdef):boolean;
    function  sym_is_owned_by(childsym:tsym;symtable:tsymtable):boolean;
    function  defs_belong_to_same_generic(def1,def2:tdef):boolean;
    function  get_generic_in_hierarchy_by_name(srsym:tsym;def:tdef):tdef;
    function  return_specialization_of_generic(nesteddef,genericdef:tdef;out resultdef:tdef):boolean;
    function  is_visible_for_object(symst:tsymtable;symvisibility:tvisibility;contextobjdef:tabstractrecorddef):boolean;
    function  is_visible_for_object(pd:tprocdef;contextobjdef:tabstractrecorddef):boolean;
    function  is_visible_for_object(sym:tsym;contextobjdef:tabstractrecorddef):boolean;
    function  searchsym(const s : TIDString;out srsym:tsym;out srsymtable:TSymtable):boolean;
    function  searchsym_maybe_with_symoption(const s : TIDString;out srsym:tsym;out srsymtable:TSymtable;searchoption:boolean;option:tsymoption):boolean;
    { searches for a symbol with the given name that has the given option in
      symoptions set }
    function  searchsym_with_symoption(const s : TIDString;out srsym:tsym;out srsymtable:TSymtable;option:tsymoption):boolean;
    function  searchsym_type(const s : TIDString;out srsym:tsym;out srsymtable:TSymtable):boolean;
    function  searchsym_in_module(pm:pointer;const s : TIDString;out srsym:tsym;out srsymtable:TSymtable):boolean;
    function  searchsym_in_named_module(const unitname, symname: TIDString; out srsym: tsym; out srsymtable: tsymtable): boolean;
    function  searchsym_in_class(classh: tobjectdef; contextclassh:tabstractrecorddef;const s : TIDString;out srsym:tsym;out srsymtable:TSymtable;searchhelper:boolean):boolean;
    function  searchsym_in_record(recordh:tabstractrecorddef;const s : TIDString;out srsym:tsym;out srsymtable:TSymtable):boolean;
    function  searchsym_in_class_by_msgint(classh:tobjectdef;msgid:longint;out srdef : tdef;out srsym:tsym;out srsymtable:TSymtable):boolean;
    function  searchsym_in_class_by_msgstr(classh:tobjectdef;const s:string;out srsym:tsym;out srsymtable:TSymtable):boolean;
    { searches symbols inside of a helper's implementation }
    function  searchsym_in_helper(classh,contextclassh:tobjectdef;const s: TIDString;out srsym:tsym;out srsymtable:TSymtable;aHasInherited:boolean):boolean;
    function  search_system_type(const s: TIDString): ttypesym;
    function  try_search_system_type(const s: TIDString): ttypesym;
    function  search_named_unit_globaltype(const unitname, typename: TIDString; throwerror: boolean): ttypesym;
    function  search_struct_member(pd : tabstractrecorddef;const s : string):tsym;
    function  search_assignment_operator(from_def,to_def:Tdef;explicit:boolean):Tprocdef;
    function  search_enumerator_operator(from_def,to_def:Tdef):Tprocdef;
    { searches for the helper definition that's currently active for pd }
    function  search_last_objectpascal_helper(pd,contextclassh : tabstractrecorddef;out odef : tobjectdef):boolean;
    { searches whether the symbol s is available in the currently active }
    { helper for pd }
    function  search_objectpascal_helper(pd,contextclassh : tabstractrecorddef;const s : string; out srsym: tsym; out srsymtable: tsymtable):boolean;
    function  search_objc_helper(pd : tobjectdef;const s : string; out srsym: tsym; out srsymtable: tsymtable):boolean;
    function  search_objc_method(const s : string; out srsym: tsym; out srsymtable: tsymtable):boolean;
    {Looks for macro s (must be given in upper case) in the macrosymbolstack, }
    {and returns it if found. Returns nil otherwise.}
    function  search_macro(const s : string):tsym;
    { Additionally to searching for a macro, also checks whether it's still }
    { actually defined (could be disable using "undef")                     }
    function  defined_macro(const s : string):boolean;

{*** Object Helpers ***}
    function search_default_property(pd : tabstractrecorddef) : tpropertysym;
    function maybe_find_real_class_definition(pd: tdef; erroronfailure: boolean): tdef;
    function find_real_class_definition(pd: tobjectdef; erroronfailure: boolean): tobjectdef;

{*** Macro Helpers ***}
    {If called initially, the following procedures manipulate macros in }
    {initialmacrotable, otherwise they manipulate system macros local to a module.}
    {Name can be given in any case (it will be converted to upper case).}
    procedure def_system_macro(const name : string);
    procedure set_system_macro(const name, value : string);
    procedure set_system_compvar(const name, value : string);
    procedure undef_system_macro(const name : string);

{*** symtable stack ***}
{ $ifdef DEBUG
    procedure test_symtablestack;
    procedure list_symtablestack;
 $endif DEBUG}

{$ifdef UNITALIASES}
    type
       punit_alias = ^tunit_alias;
       tunit_alias = object(TNamedIndexItem)
          newname : pshortstring;
          constructor init(const n:string);
          destructor  done;virtual;
       end;
    var
       unitaliases : pdictionary;

    procedure addunitalias(const n:string);
    function getunitalias(const n:string):string;
{$endif UNITALIASES}

{*** Init / Done ***}
    procedure IniTSymtable;
    procedure DoneSymtable;

    const
      overloaded_names : array [NOTOKEN..last_overloaded] of string[16] = (
    { NOTOKEN        }  'error',
    { _PLUS          }  'plus',
    { _MINUS         }  'minus',
    { _STAR          }  'star',
    { _SLASH         }  'slash',
    { _EQ            }  'equal',
    { _GT            }  'greater',
    { _LT            }  'lower',
    { _GTE           }  'greater_or_equal',
    { _LTE           }  'lower_or_equal',
    { _NE            }  'not_equal',
    { _SYMDIF        }  'sym_diff',
    { _STARSTAR      }  'starstar',
    { _OP_AS         }  'as',
    { _OP_IN         }  'in',
    { _OP_IS         }  'is',
    { _OP_OR         }  'or',
    { _OP_AND        }  'and',
    { _OP_DIV        }  'div',
    { _OP_MOD        }  'mod',
    { _OP_NOT        }  'not',
    { _OP_SHL        }  'shl',
    { _OP_SHR        }  'shr',
    { _OP_XOR        }  'xor',
    { _ASSIGNMENT    }  'assign',
    { _OP_EXPLICIT   }  'explicit',
    { _OP_ENUMERATOR }  'enumerator',
    { _OP_INC        }  'inc',
    { _OP_DEC        }  'dec');



implementation

    uses
      { global }
      verbose,globals,
      { target }
      systems,
      { symtable }
      symutil,defcmp,defutil,
      { module }
      fmodule,
      { codegen }
      procinfo
      ;


    var
      dupnr : longint; { unique number for duplicate symbols }

{*****************************************************************************
                             TStoredSymtable
*****************************************************************************}

    procedure tstoredsymtable.insert(sym:TSymEntry;checkdup:boolean=true);
      begin
        inherited insert(sym,checkdup);
      end;


    procedure tstoredsymtable.delete(sym:TSymEntry);
      begin
        inherited delete(sym);
      end;


    procedure tstoredsymtable.ppuload(ppufile:tcompilerppufile);
      begin
        { load the table's flags }
        if ppufile.readentry<>ibsymtableoptions then
          Message(unit_f_ppu_read_error);
        ppufile.getsmallset(tableoptions);

        { load definitions }
        loaddefs(ppufile);

        { load symbols }
        loadsyms(ppufile);
      end;


    procedure tstoredsymtable.ppuwrite(ppufile:tcompilerppufile);
      begin
         { write the table's flags }
         ppufile.putsmallset(tableoptions);
         ppufile.writeentry(ibsymtableoptions);

         { write definitions }
         writedefs(ppufile);

         { write symbols }
         writesyms(ppufile);
      end;


    procedure tstoredsymtable.loaddefs(ppufile:tcompilerppufile);
      var
        def : tdef;
        b   : byte;
      begin
         { load start of definition section, which holds the amount of defs }
         if ppufile.readentry<>ibstartdefs then
           Message(unit_f_ppu_read_error);
         { read definitions }
         repeat
           b:=ppufile.readentry;
           case b of
             ibpointerdef : def:=tpointerdef.ppuload(ppufile);
             ibarraydef : def:=tarraydef.ppuload(ppufile);
             iborddef : def:=torddef.ppuload(ppufile);
             ibfloatdef : def:=tfloatdef.ppuload(ppufile);
             ibprocdef : def:=tprocdef.ppuload(ppufile);
             ibshortstringdef : def:=tstringdef.loadshort(ppufile);
             iblongstringdef : def:=tstringdef.loadlong(ppufile);
             ibansistringdef : def:=tstringdef.loadansi(ppufile);
             ibwidestringdef : def:=tstringdef.loadwide(ppufile);
             ibunicodestringdef : def:=tstringdef.loadunicode(ppufile);
             ibrecorddef : def:=trecorddef.ppuload(ppufile);
             ibobjectdef : def:=tobjectdef.ppuload(ppufile);
             ibenumdef : def:=tenumdef.ppuload(ppufile);
             ibsetdef : def:=tsetdef.ppuload(ppufile);
             ibprocvardef : def:=tprocvardef.ppuload(ppufile);
             ibfiledef : def:=tfiledef.ppuload(ppufile);
             ibclassrefdef : def:=tclassrefdef.ppuload(ppufile);
             ibformaldef : def:=tformaldef.ppuload(ppufile);
             ibvariantdef : def:=tvariantdef.ppuload(ppufile);
             ibundefineddef : def:=tundefineddef.ppuload(ppufile);
             ibenddefs : break;
             ibend : Message(unit_f_ppu_read_error);
           else
             Message1(unit_f_ppu_invalid_entry,tostr(b));
           end;
           InsertDef(def);
         until false;
      end;


    procedure tstoredsymtable.loadsyms(ppufile:tcompilerppufile);
      var
        b   : byte;
        sym : tsym;
      begin
      { load start of definition section, which holds the amount of defs }
         if ppufile.readentry<>ibstartsyms then
          Message(unit_f_ppu_read_error);
         { now read the symbols }
         repeat
           b:=ppufile.readentry;
           case b of
                ibtypesym : sym:=ttypesym.ppuload(ppufile);
                ibprocsym : sym:=tprocsym.ppuload(ppufile);
               ibconstsym : sym:=tconstsym.ppuload(ppufile);
           ibstaticvarsym : sym:=tstaticvarsym.ppuload(ppufile);
            iblocalvarsym : sym:=tlocalvarsym.ppuload(ppufile);
             ibparavarsym : sym:=tparavarsym.ppuload(ppufile);
            ibfieldvarsym : sym:=tfieldvarsym.ppuload(ppufile);
         ibabsolutevarsym : sym:=tabsolutevarsym.ppuload(ppufile);
                ibenumsym : sym:=tenumsym.ppuload(ppufile);
            ibpropertysym : sym:=tpropertysym.ppuload(ppufile);
                ibunitsym : sym:=tunitsym.ppuload(ppufile);
               iblabelsym : sym:=tlabelsym.ppuload(ppufile);
                 ibsyssym : sym:=tsyssym.ppuload(ppufile);
               ibmacrosym : sym:=tmacro.ppuload(ppufile);
           ibnamespacesym : sym:=tnamespacesym.ppuload(ppufile);
                ibendsyms : break;
                    ibend : Message(unit_f_ppu_read_error);
           else
             Message1(unit_f_ppu_invalid_entry,tostr(b));
           end;
           Insert(sym,false);
         until false;
      end;


    procedure tstoredsymtable.writedefs(ppufile:tcompilerppufile);
      var
        i   : longint;
        def : tstoreddef;
      begin
        { each definition get a number, write then the amount of defs to the
          ibstartdef entry }
        ppufile.putlongint(DefList.count);
        ppufile.writeentry(ibstartdefs);
        { now write the definition }
        for i:=0 to DefList.Count-1 do
          begin
            def:=tstoreddef(DefList[i]);
            def.ppuwrite(ppufile);
          end;
        { write end of definitions }
        ppufile.writeentry(ibenddefs);
      end;


    procedure tstoredsymtable.writesyms(ppufile:tcompilerppufile);
      var
        i   : longint;
        sym : Tstoredsym;
      begin
        { each definition get a number, write then the amount of syms and the
          datasize to the ibsymdef entry }
        ppufile.putlongint(SymList.count);
        ppufile.writeentry(ibstartsyms);
        { foreach is used to write all symbols }
        for i:=0 to SymList.Count-1 do
          begin
            sym:=tstoredsym(SymList[i]);
            sym.ppuwrite(ppufile);
          end;
        { end of symbols }
        ppufile.writeentry(ibendsyms);
      end;


    procedure tstoredsymtable.buildderef;
      var
        i   : longint;
        def : tstoreddef;
        sym : tstoredsym;
      begin
        { interface definitions }
        for i:=0 to DefList.Count-1 do
          begin
            def:=tstoreddef(DefList[i]);
            def.buildderef;
          end;
        { interface symbols }
        for i:=0 to SymList.Count-1 do
          begin
            sym:=tstoredsym(SymList[i]);
            sym.buildderef;
          end;
      end;


    procedure tstoredsymtable.buildderefimpl;
      var
        i   : longint;
        def : tstoreddef;
      begin
        { implementation definitions }
        for i:=0 to DefList.Count-1 do
          begin
            def:=tstoreddef(DefList[i]);
            def.buildderefimpl;
          end;
      end;


    procedure tstoredsymtable.deref;
      var
        i   : longint;
        def : tstoreddef;
        sym : tstoredsym;
      begin
        { first deref the interface ttype symbols. This is needs
          to be done before the interface defs are derefed, because
          the interface defs can contain references to the type symbols
          which then already need to contain a resolved typedef field (PFV) }
        for i:=0 to SymList.Count-1 do
          begin
            sym:=tstoredsym(SymList[i]);
            if sym.typ=typesym then
              sym.deref;
          end;
        { interface definitions }
        for i:=0 to DefList.Count-1 do
          begin
            def:=tstoreddef(DefList[i]);
            def.deref;
          end;
        { interface symbols }
        for i:=0 to SymList.Count-1 do
          begin
            sym:=tstoredsym(SymList[i]);
            if sym.typ<>typesym then
              sym.deref;
          end;
      end;


    procedure tstoredsymtable.derefimpl;
      var
        i   : longint;
        def : tstoreddef;
      begin
        { implementation definitions }
        for i:=0 to DefList.Count-1 do
          begin
            def:=tstoreddef(DefList[i]);
            def.derefimpl;
          end;
      end;


    function tstoredsymtable.checkduplicate(var hashedid:THashedIDString;sym:TSymEntry):boolean;
      var
        hsym : tsym;
      begin
        hsym:=tsym(FindWithHash(hashedid));
        if assigned(hsym) then
          DuplicateSym(hashedid,sym,hsym);
        result:=assigned(hsym);
      end;


{**************************************
             Callbacks
**************************************}

    procedure TStoredSymtable.check_forward(sym:TObject;arg:pointer);
      begin
         if tsym(sym).typ=procsym then
           tprocsym(sym).check_forward
         { check also object method table            }
         { we needn't to test the def list          }
         { because each object has to have a type sym,
           only test objects declarations, not type renamings }
         else
          if (tsym(sym).typ=typesym) and
             assigned(ttypesym(sym).typedef) and
             (ttypesym(sym).typedef.typesym=ttypesym(sym)) and
             (ttypesym(sym).typedef.typ in [objectdef,recorddef]) then
           tabstractrecorddef(ttypesym(sym).typedef).check_forwards;
      end;


    procedure TStoredSymtable.labeldefined(sym:TObject;arg:pointer);
      begin
        if (tsym(sym).typ=labelsym) and
           not(tlabelsym(sym).defined) then
         begin
           if tlabelsym(sym).used then
            Message1(sym_e_label_used_and_not_defined,tlabelsym(sym).realname)
           else
            Message1(sym_w_label_not_defined,tlabelsym(sym).realname);
         end;
      end;


    procedure TStoredSymtable.varsymbolused(sym:TObject;arg:pointer);
      begin
         if (tsym(sym).typ in [staticvarsym,localvarsym,paravarsym,fieldvarsym]) and
            ((tsym(sym).owner.symtabletype in
             [parasymtable,localsymtable,ObjectSymtable,recordsymtable,staticsymtable])) then
           begin
            { unused symbol should be reported only if no                    }
            { error is reported                                              }
            { if the symbol is in a register it is used                      }
            { also don't count the value parameters which have local copies  }
            { also don't claim for high param of open parameters    (PM)     }
            { also don't complain about unused symbols in generic procedures }
            { and methods                                                    }
            if (Errorcount<>0) or
               ([vo_is_hidden_para,vo_is_funcret] * tabstractvarsym(sym).varoptions = [vo_is_hidden_para]) or
               (sp_internal in tsym(sym).symoptions) or
               ((assigned(tsym(sym).owner.defowner) and
                (tsym(sym).owner.defowner.typ=procdef) and
                (df_generic in tprocdef(tsym(sym).owner.defowner).defoptions))) then
              exit;
            if (tstoredsym(sym).refs=0) then
              begin
                 if (vo_is_funcret in tabstractvarsym(sym).varoptions) then
                   begin
                     { don't warn about the result of constructors }
                     if ((tsym(sym).owner.symtabletype<>localsymtable) or
                        (tprocdef(tsym(sym).owner.defowner).proctypeoption<>potype_constructor)) and
                        not(cs_opt_nodedfa in current_settings.optimizerswitches) then
                       MessagePos(tsym(sym).fileinfo,sym_w_function_result_not_set)
                   end
                 else if (tsym(sym).owner.symtabletype=parasymtable) then
                   MessagePos1(tsym(sym).fileinfo,sym_h_para_identifier_not_used,tsym(sym).prettyname)
                 else if (tsym(sym).owner.symtabletype in [ObjectSymtable,recordsymtable]) then
                   MessagePos2(tsym(sym).fileinfo,sym_n_private_identifier_not_used,tabstractrecorddef(tsym(sym).owner.defowner).GetTypeName,tsym(sym).prettyname)
                 else
                   MessagePos1(tsym(sym).fileinfo,sym_n_local_identifier_not_used,tsym(sym).prettyname);
              end
            else if tabstractvarsym(sym).varstate in [vs_written,vs_initialised] then
              begin
                 if (tsym(sym).owner.symtabletype=parasymtable) then
                   begin
                     if not(tabstractvarsym(sym).varspez in [vs_var,vs_out,vs_constref]) and
                        not(vo_is_funcret in tabstractvarsym(sym).varoptions) then
                       MessagePos1(tsym(sym).fileinfo,sym_h_para_identifier_only_set,tsym(sym).prettyname)
                   end
                 else if (tsym(sym).owner.symtabletype in [ObjectSymtable,recordsymtable]) then
                   MessagePos2(tsym(sym).fileinfo,sym_n_private_identifier_only_set,tabstractrecorddef(tsym(sym).owner.defowner).GetTypeName,tsym(sym).prettyname)
                 else if tabstractvarsym(sym).varoptions*[vo_is_funcret,vo_is_public,vo_is_external]=[] then
                   MessagePos1(tsym(sym).fileinfo,sym_n_local_identifier_only_set,tsym(sym).prettyname);
              end
            else if (tabstractvarsym(sym).varstate = vs_read_not_warned) and
                    ([vo_is_public,vo_is_external] * tabstractvarsym(sym).varoptions = []) then
              MessagePos1(tsym(sym).fileinfo,sym_w_identifier_only_read,tsym(sym).prettyname)
          end
        else if ((tsym(sym).owner.symtabletype in
              [ObjectSymtable,parasymtable,localsymtable,staticsymtable,recordsymtable])) then
          begin
           if (Errorcount<>0) or
              (sp_internal in tsym(sym).symoptions) then
             exit;
           { do not claim for inherited private fields !! }
           if (tsym(sym).refs=0) and (tsym(sym).owner.symtabletype in [ObjectSymtable,recordsymtable]) then
             case tsym(sym).typ of
               typesym:
                 MessagePos2(tsym(sym).fileinfo,sym_n_private_type_not_used,tabstractrecorddef(tsym(sym).owner.defowner).GetTypeName,tsym(sym).prettyname);
               constsym:
                 MessagePos2(tsym(sym).fileinfo,sym_n_private_const_not_used,tabstractrecorddef(tsym(sym).owner.defowner).GetTypeName,tsym(sym).prettyname);
               propertysym:
                 MessagePos2(tsym(sym).fileinfo,sym_n_private_property_not_used,tabstractrecorddef(tsym(sym).owner.defowner).GetTypeName,tsym(sym).prettyname);
             else
               MessagePos2(tsym(sym).fileinfo,sym_n_private_method_not_used,tabstractrecorddef(tsym(sym).owner.defowner).GetTypeName,tsym(sym).prettyname);
             end
           { units references are problematic }
           else
            begin
              if (tsym(sym).refs=0) and
                 not(tsym(sym).typ in [enumsym,unitsym,namespacesym]) and
                 not(is_funcret_sym(tsym(sym))) and
                 { don't complain about compiler generated syms for specializations, see also #13405 }
                 not((tsym(sym).typ=typesym) and (df_specialization in ttypesym(sym).typedef.defoptions) and
                    (pos('$',ttypesym(sym).Realname)<>0)) and
                 (
                  (tsym(sym).typ<>procsym) or
                  ((tsym(sym).owner.symtabletype=staticsymtable) and
                   not current_module.is_unit)
                 ) and
                 { don't complain about alias for hidden _cmd parameter to
                   obj-c methods }
                 not((tsym(sym).typ in [localvarsym,paravarsym,absolutevarsym]) and
                     (vo_is_msgsel in tabstractvarsym(sym).varoptions)) then
                MessagePos2(tsym(sym).fileinfo,sym_h_local_symbol_not_used,SymTypeName[tsym(sym).typ],tsym(sym).prettyname);
            end;
          end;
      end;


    procedure TStoredSymtable.TestPrivate(sym:TObject;arg:pointer);
      begin
        if tsym(sym).visibility in [vis_private,vis_strictprivate] then
          varsymbolused(sym,arg);
      end;


    procedure TStoredSymtable.objectprivatesymbolused(sym:TObject;arg:pointer);
      begin
         {
           Don't test simple object aliases PM
         }
         if (tsym(sym).typ=typesym) and
            (ttypesym(sym).typedef.typ in [objectdef,recorddef]) and
            (ttypesym(sym).typedef.typesym=tsym(sym)) then
           tabstractrecorddef(ttypesym(sym).typedef).symtable.SymList.ForEachCall(@TestPrivate,nil);
      end;


   procedure tstoredsymtable.testfordefaultproperty(sym:TObject;arg:pointer);
     begin
        if (tsym(sym).typ=propertysym) and
           (ppo_defaultproperty in tpropertysym(sym).propoptions) then
          ppointer(arg)^:=sym;
     end;


{***********************************************
           Process all entries
***********************************************}

    { checks, if all procsyms and methods are defined }
    procedure tstoredsymtable.check_forwards;
      begin
         SymList.ForEachCall(@check_forward,nil);
      end;


    procedure tstoredsymtable.checklabels;
      begin
         SymList.ForEachCall(@labeldefined,nil);
      end;


    procedure tstoredsymtable.allsymbolsused;
      begin
         SymList.ForEachCall(@varsymbolused,nil);
      end;


    procedure tstoredsymtable.allprivatesused;
      begin
         SymList.ForEachCall(@objectprivatesymbolused,nil);
      end;


    procedure TStoredSymtable._needs_init_final(sym:TObject;arg:pointer);
      begin
         if b_needs_init_final then
           exit;
         { don't check static symbols - they can be present in structures only and
           always have a reference to a symbol defined on unit level }
         if sp_static in tsym(sym).symoptions then
           exit;
         case tsym(sym).typ of
           fieldvarsym,
           staticvarsym,
           localvarsym,
           paravarsym :
             begin
               if assigned(tabstractvarsym(sym).vardef) and
                  is_managed_type(tabstractvarsym(sym).vardef) then
                 b_needs_init_final:=true;
             end;
         end;
      end;


    { returns true, if p contains data which needs init/final code }
    function tstoredsymtable.needs_init_final : boolean;
      begin
         b_needs_init_final:=false;
         SymList.ForEachCall(@_needs_init_final,nil);
         needs_init_final:=b_needs_init_final;
      end;


{****************************************************************************
                          TAbstractRecordSymtable
****************************************************************************}

    constructor tabstractrecordsymtable.create(const n:string;usealign:shortint);
      begin
        inherited create(n);
        moduleid:=current_module.moduleid;
        _datasize:=0;
        databitsize:=0;
        recordalignment:=1;
        usefieldalignment:=usealign;
        padalignment:=1;
        { recordalign C_alignment means C record packing, that starts
          with an alignment of 1 }
        case usealign of
          C_alignment,
          bit_alignment:
            fieldalignment:=1;
          mac68k_alignment:
            fieldalignment:=2;
          else
            fieldalignment:=usealign;
        end;
      end;


    procedure tabstractrecordsymtable.ppuload(ppufile:tcompilerppufile);
      begin
        if ppufile.readentry<>ibrecsymtableoptions then
          Message(unit_f_ppu_read_error);
        recordalignment:=shortint(ppufile.getbyte);
        usefieldalignment:=shortint(ppufile.getbyte);
        if (usefieldalignment=C_alignment) then
          fieldalignment:=shortint(ppufile.getbyte);
        inherited ppuload(ppufile);
      end;


    procedure tabstractrecordsymtable.ppuwrite(ppufile:tcompilerppufile);
      var
        oldtyp : byte;
      begin
         oldtyp:=ppufile.entrytyp;
         ppufile.entrytyp:=subentryid;
         { in case of classes using C alignment, the alignment of the parent
           affects the alignment of fields of the childs }
         ppufile.putbyte(byte(recordalignment));
         ppufile.putbyte(byte(usefieldalignment));
         if (usefieldalignment=C_alignment) then
           ppufile.putbyte(byte(fieldalignment));
         ppufile.writeentry(ibrecsymtableoptions);

         inherited ppuwrite(ppufile);

         ppufile.entrytyp:=oldtyp;
      end;


    function field2recordalignment(fieldoffs, fieldalign: asizeint): asizeint;
      begin
        { optimal alignment of the record when declaring a variable of this }
        { type is independent of the packrecords setting                    }
        if (fieldoffs mod fieldalign) = 0 then
          result:=fieldalign
        else if (fieldalign >= 16) and
                ((fieldoffs mod 16) = 0) and
                ((fieldalign mod 16) = 0) then
          result:=16
        else if (fieldalign >= 8) and
                ((fieldoffs mod 8) = 0) and
                ((fieldalign mod 8) = 0) then
          result:=8
        else if (fieldalign >= 4) and
                ((fieldoffs mod 4) = 0) and
                ((fieldalign mod 4) = 0) then
          result:=4
        else if (fieldalign >= 2) and
                ((fieldoffs mod 2) = 0) and
                ((fieldalign mod 2) = 0) then
          result:=2
        else
          result:=1;
      end;

    procedure tabstractrecordsymtable.alignrecord(fieldoffset:asizeint;varalign:shortint);
      var
        varalignrecord: shortint;
      begin
        case usefieldalignment of
          C_alignment:
            varalignrecord:=used_align(varalign,current_settings.alignment.recordalignmin,current_settings.alignment.maxCrecordalign);
          mac68k_alignment:
            varalignrecord:=2;
          else
            varalignrecord:=field2recordalignment(fieldoffset,varalign);
        end;
        recordalignment:=max(recordalignment,varalignrecord);
      end;

    procedure tabstractrecordsymtable.addfield(sym:tfieldvarsym;vis:tvisibility);
      var
        l      : asizeint;
        varalignfield,
        varalign : shortint;
        vardef : tdef;
      begin
        if (sym.owner<>self) then
          internalerror(200602031);
        if sym.fieldoffset<>-1 then
          internalerror(200602032);
        { set visibility for the symbol }
        sym.visibility:=vis;
        { this symbol can't be loaded to a register }
        sym.varregable:=vr_none;
        { Calculate field offset }
        l:=sym.getsize;
        vardef:=sym.vardef;
        varalign:=vardef.alignment;
{$if defined(powerpc) or defined(powerpc64)}
        { aix is really annoying: the recommended scalar alignment for both
          int64 and double is 64 bits, but in structs int64 has to be aligned
          to 8 bytes and double to 4 bytes }
        if (target_info.system in systems_aix) and
           is_double(vardef) then
          varalign:=4;
{$endif powerpc or powerpc64}

        case usefieldalignment of
          bit_alignment:
            begin
              { bitpacking only happens for ordinals, the rest is aligned at }
              { 1 byte (compatible with GPC/GCC)                             }
              if is_ordinal(vardef) then
                begin
                  sym.fieldoffset:=databitsize;
                  l:=sym.getpackedbitsize;
                end
              else
                begin
                  databitsize:=_datasize*8;
                  sym.fieldoffset:=databitsize;
                  if (l>high(asizeint) div 8) then
                    Message(sym_e_segment_too_large);
                  l:=l*8;
                end;
              if varalign=0 then
                varalign:=size_2_align(l);
              recordalignment:=max(recordalignment,field2recordalignment(databitsize mod 8,varalign));
              { bit packed records are limited to high(aint) bits }
              { instead of bytes to avoid double precision        }
              { arithmetic in offset calculations                 }
              if int64(l)>high(asizeint)-sym.fieldoffset then
                begin
                  Message(sym_e_segment_too_large);
                  _datasize:=high(asizeint);
                  databitsize:=high(asizeint);
                end
              else
                begin
                  databitsize:=sym.fieldoffset+l;
                  _datasize:=(databitsize+7) div 8;
                end;
              { rest is not applicable }
              exit;
            end;
          { Calc the alignment size for C style records }
          C_alignment:
            begin
              if (varalign>4) and
                ((varalign mod 4)<>0) and
                (vardef.typ=arraydef) then
                Message1(sym_w_wrong_C_pack,vardef.typename);
              if varalign=0 then
                varalign:=l;
              if (fieldalignment<current_settings.alignment.maxCrecordalign) then
                begin
                  if (varalign>16) and (fieldalignment<32) then
                    fieldalignment:=32
                  else if (varalign>12) and (fieldalignment<16) then
                    fieldalignment:=16
                  { 12 is needed for long double }
                  else if (varalign>8) and (fieldalignment<12) then
                    fieldalignment:=12
                  else if (varalign>4) and (fieldalignment<8) then
                    fieldalignment:=8
                  else if (varalign>2) and (fieldalignment<4) then
                    fieldalignment:=4
                  else if (varalign>1) and (fieldalignment<2) then
                    fieldalignment:=2;
                end;
              fieldalignment:=min(fieldalignment,current_settings.alignment.maxCrecordalign);
            end;
          mac68k_alignment:
            begin
              { mac68k alignment (C description):
                 * char is aligned to 1 byte
                 * everything else (except vector) is aligned to 2 bytes
                 * vector is aligned to 16 bytes
              }
              if l>1 then
                fieldalignment:=2
              else
                fieldalignment:=1;
              varalign:=2;
            end;
        end;
        if varalign=0 then
          varalign:=size_2_align(l);
        varalignfield:=used_align(varalign,current_settings.alignment.recordalignmin,fieldalignment);

        sym.fieldoffset:=align(_datasize,varalignfield);
        if l>high(asizeint)-sym.fieldoffset then
          begin
            Message(sym_e_segment_too_large);
            _datasize:=high(asizeint);
          end
        else
          _datasize:=sym.fieldoffset+l;
        { Calc alignment needed for this record }
        alignrecord(sym.fieldoffset,varalign);
      end;


    procedure tabstractrecordsymtable.addalignmentpadding;
      var
        padded_datasize: asizeint;
      begin
        { make the record size aligned correctly so it can be
          used as elements in an array. For C records we
          use the fieldalignment, because that is updated with the
          used alignment. }
        if (padalignment = 1) then
          case usefieldalignment of
            C_alignment:
              padalignment:=fieldalignment;
            { bitpacked }
            bit_alignment:
              padalignment:=1;
            { mac68k: always round to multiple of 2 }
            mac68k_alignment:
              padalignment:=2;
            { default/no packrecords specified }
            0:
              padalignment:=recordalignment
            { specific packrecords setting -> use as upper limit }
            else
              padalignment:=min(recordalignment,usefieldalignment);
          end;
        padded_datasize:=align(_datasize,padalignment);
        _paddingsize:=padded_datasize-_datasize;
        _datasize:=padded_datasize;
      end;


    procedure tabstractrecordsymtable.insertdef(def:TDefEntry);
      begin
        { Enums must also be available outside the record scope,
          insert in the owner of this symtable }
        if def.typ=enumdef then
          defowner.owner.insertdef(def)
        else
          inherited insertdef(def);
      end;


    function tabstractrecordsymtable.is_packed: boolean;
      begin
        result:=usefieldalignment=bit_alignment;
      end;


    function tabstractrecordsymtable.has_single_field(out sym: tfieldvarsym): boolean;
      var
        i: longint;
      begin
        result:=false;
        { If a record contains a union, it does not contain a "single
          non-composite field" in the context of certain ABIs requiring
          special treatment for such records }
        if (defowner.typ=recorddef) and
           trecorddef(defowner).isunion then
          exit;
        { a record/object can contain other things than fields }
        for i:=0 to SymList.Count-1 do
          begin
            if tsym(symlist[i]).typ=fieldvarsym then
              begin
                if result then
                  begin
                    result:=false;
                    exit;
                  end;
                result:=true;
                sym:=tfieldvarsym(symlist[i])
              end;
          end;
      end;

    function tabstractrecordsymtable.get_unit_symtable: tsymtable;
      begin
        result:=defowner.owner;
        while assigned(result) and (result.symtabletype in [ObjectSymtable,recordsymtable]) do
          result:=result.defowner.owner;
      end;

    procedure tabstractrecordsymtable.setdatasize(val: asizeint);
      begin
        _datasize:=val;
        if (usefieldalignment=bit_alignment) then
          { can overflow in non bitpacked records }
          databitsize:=val*8;
      end;

    function tabstractrecordsymtable.iscurrentunit: boolean;
      begin
        Result := Assigned(current_module) and (current_module.moduleid=moduleid);
      end;

{****************************************************************************
                              TRecordSymtable
****************************************************************************}

    constructor trecordsymtable.create(const n:string;usealign:shortint);
      begin
        inherited create(n,usealign);
        symtabletype:=recordsymtable;
      end;


   { this procedure is reserved for inserting case variant into
      a record symtable }
    { the offset is the location of the start of the variant
      and datasize and dataalignment corresponds to
      the complete size (see code in pdecl unit) PM }
    procedure trecordsymtable.insertunionst(unionst : trecordsymtable;offset : longint);
      var
        sym : tsym;
        def : tdef;
        i : integer;
        varalignrecord,varalign,
        storesize,storealign : aint;
        bitsize: tcgint;
      begin
        storesize:=_datasize;
        storealign:=fieldalignment;
        _datasize:=offset;
        if (usefieldalignment=bit_alignment) then
          databitsize:=offset*8;

        { We move the ownership of the defs and symbols to the new recordsymtable.
          The old unionsymtable keeps the references, but doesn't own the
          objects anymore }
        unionst.DefList.OwnsObjects:=false;
        unionst.SymList.OwnsObjects:=false;

        { copy symbols }
        for i:=0 to unionst.SymList.Count-1 do
          begin
            sym:=TSym(unionst.SymList[i]);
            if sym.typ<>fieldvarsym then
              internalerror(200601272);
            if tfieldvarsym(sym).fieldoffset=0 then
              include(tfieldvarsym(sym).varoptions,vo_is_first_field);

            { add to this record symtable }
//            unionst.SymList.List.List^[i].Data:=nil;
            sym.ChangeOwner(self);
            varalign:=tfieldvarsym(sym).vardef.alignment;
            if varalign=0 then
              varalign:=size_2_align(tfieldvarsym(sym).getsize);
            { retrieve size }
            if (usefieldalignment=bit_alignment) then
              begin
                { bit packed records are limited to high(aint) bits }
                { instead of bytes to avoid double precision        }
                { arithmetic in offset calculations                 }
                if is_ordinal(tfieldvarsym(sym).vardef) then
                  bitsize:=tfieldvarsym(sym).getpackedbitsize
                else
                  begin
                    bitsize:=tfieldvarsym(sym).getsize;
                    if (bitsize>high(asizeint) div 8) then
                      Message(sym_e_segment_too_large);
                    bitsize:=bitsize*8;
                  end;
                if bitsize>high(asizeint)-databitsize then
                  begin
                    Message(sym_e_segment_too_large);
                    _datasize:=high(asizeint);
                    databitsize:=high(asizeint);
                  end
                else
                  begin
                    databitsize:=tfieldvarsym(sym).fieldoffset+offset*8;
                    _datasize:=(databitsize+7) div 8;
                  end;
                tfieldvarsym(sym).fieldoffset:=databitsize;
              varalignrecord:=field2recordalignment(tfieldvarsym(sym).fieldoffset div 8,varalign);
              end
            else
              begin
                if tfieldvarsym(sym).getsize>high(asizeint)-_datasize then
                  begin
                    Message(sym_e_segment_too_large);
                    _datasize:=high(asizeint);
                  end
                else
                  _datasize:=tfieldvarsym(sym).fieldoffset+offset;
                { update address }
                tfieldvarsym(sym).fieldoffset:=_datasize;
                varalignrecord:=field2recordalignment(tfieldvarsym(sym).fieldoffset,varalign);
              end;
            { update alignment of this record }
            if (usefieldalignment<>C_alignment) and
               (usefieldalignment<>mac68k_alignment) then
              recordalignment:=max(recordalignment,varalignrecord);
          end;
        { update alignment for C records }
        if (usefieldalignment=C_alignment) and
           (usefieldalignment<>mac68k_alignment) then
          recordalignment:=max(recordalignment,unionst.recordalignment);
        { Register defs in the new record symtable }
        for i:=0 to unionst.DefList.Count-1 do
          begin
            def:=TDef(unionst.DefList[i]);
            def.ChangeOwner(self);
          end;
        _datasize:=storesize;
        fieldalignment:=storealign;
        { If a record contains a union, it does not contain a "single
          non-composite field" in the context of certain ABIs requiring
          special treatment for such records }
        if defowner.typ=recorddef then
          trecorddef(defowner).isunion:=true;
      end;


{****************************************************************************
                              TObjectSymtable
****************************************************************************}

    constructor tObjectSymtable.create(adefowner:tdef;const n:string;usealign:shortint);
      begin
        inherited create(n,usealign);
        symtabletype:=ObjectSymtable;
        defowner:=adefowner;
      end;


    function tObjectSymtable.checkduplicate(var hashedid:THashedIDString;sym:TSymEntry):boolean;
      var
         hsym : tsym;
      begin
         result:=false;
         if not assigned(defowner) then
           internalerror(200602061);

         { procsym and propertysym have special code
           to override values in inherited classes. For other
           symbols check for duplicates }
         if not(sym.typ in [procsym,propertysym]) then
           begin
              { but private ids can be reused }
              hsym:=search_struct_member(tobjectdef(defowner),hashedid.id);
              if assigned(hsym) and
                 (
                  (
                   not(m_delphi in current_settings.modeswitches) and
                   is_visible_for_object(hsym,tobjectdef(defowner))
                  ) or
                  (
                   { In Delphi, you can repeat members of a parent class. You can't }
                   { do this for objects however, and you (obviouly) can't          }
                   { declare two fields with the same name in a single class        }
                   (m_delphi in current_settings.modeswitches) and
                   (
                    is_object(tdef(defowner)) or
                    (hsym.owner = self)
                   )
                  )
                 ) then
                begin
                  DuplicateSym(hashedid,sym,hsym);
                  result:=true;
                end;
           end
         else
           result:=inherited checkduplicate(hashedid,sym);
      end;


{****************************************************************************
                          TAbstractLocalSymtable
****************************************************************************}

   procedure tabstractlocalsymtable.ppuwrite(ppufile:tcompilerppufile);
      var
        oldtyp : byte;
      begin
         oldtyp:=ppufile.entrytyp;
         ppufile.entrytyp:=subentryid;

         inherited ppuwrite(ppufile);

         ppufile.entrytyp:=oldtyp;
      end;


    function tabstractlocalsymtable.count_locals:longint;
      var
        i   : longint;
        sym : tsym;
      begin
        result:=0;
        for i:=0 to SymList.Count-1 do
          begin
            sym:=tsym(SymList[i]);
            { Count only varsyms, but ignore the funcretsym }
            if (tsym(sym).typ in [localvarsym,paravarsym]) and
               (tsym(sym)<>current_procinfo.procdef.funcretsym) and
               (not(vo_is_parentfp in tabstractvarsym(sym).varoptions) or
                (tstoredsym(sym).refs>0)) then
              inc(result);
         end;
      end;


{****************************************************************************
                              TLocalSymtable
****************************************************************************}

    constructor tlocalsymtable.create(adefowner:tdef;level:byte);
      begin
        inherited create('');
        defowner:=adefowner;
        symtabletype:=localsymtable;
        symtablelevel:=level;
      end;


    function tlocalsymtable.checkduplicate(var hashedid:THashedIDString;sym:TSymEntry):boolean;
      var
        hsym : tsym;
      begin
        if not assigned(defowner) or
           (defowner.typ<>procdef) then
          internalerror(200602042);

        result:=false;
        hsym:=tsym(FindWithHash(hashedid));
        if assigned(hsym) then
          begin
            { a local and the function can have the same
              name in TP and Delphi, but RESULT not }
            if (m_duplicate_names in current_settings.modeswitches) and
               (hsym.typ in [absolutevarsym,localvarsym]) and
               (vo_is_funcret in tabstractvarsym(hsym).varoptions) and
               not((m_result in current_settings.modeswitches) and
                   (vo_is_result in tabstractvarsym(hsym).varoptions)) then
              HideSym(hsym)
            else
              DuplicateSym(hashedid,sym,hsym);
            result:=true;
            exit;
          end;

        { check also parasymtable, this needs to be done here because
          of the special situation with the funcret sym that needs to be
          hidden for tp and delphi modes }
        hsym:=tsym(tabstractprocdef(defowner).parast.FindWithHash(hashedid));
        if assigned(hsym) then
          begin
            { a local and the function can have the same
              name in TP and Delphi, but RESULT not }
            if (m_duplicate_names in current_settings.modeswitches) and
               (sym.typ in [absolutevarsym,localvarsym]) and
               (vo_is_funcret in tabstractvarsym(sym).varoptions) and
               not((m_result in current_settings.modeswitches) and
                   (vo_is_result in tabstractvarsym(sym).varoptions)) then
              Hidesym(sym)
            else
              DuplicateSym(hashedid,sym,hsym);
            result:=true;
            exit;
          end;

        { check ObjectSymtable, skip this for funcret sym because
          that will always be positive because it has the same name
          as the procsym }
        if not is_funcret_sym(sym) and
           (defowner.typ=procdef) and
           assigned(tprocdef(defowner).struct) and
           (tprocdef(defowner).owner.defowner=tprocdef(defowner).struct) and
           (
            not(m_delphi in current_settings.modeswitches) or
            is_object(tprocdef(defowner).struct)
           ) then
          result:=tprocdef(defowner).struct.symtable.checkduplicate(hashedid,sym);
      end;


{****************************************************************************
                              TParaSymtable
****************************************************************************}

    constructor tparasymtable.create(adefowner:tdef;level:byte);
      begin
        inherited create('');
        readonly:=false;
        defowner:=adefowner;
        symtabletype:=parasymtable;
        symtablelevel:=level;
      end;


    function tparasymtable.checkduplicate(var hashedid:THashedIDString;sym:TSymEntry):boolean;
      begin
        result:=inherited checkduplicate(hashedid,sym);
        if result then
          exit;
        if not(m_duplicate_names in current_settings.modeswitches) and
           assigned(defowner) and (defowner.typ=procdef) and
           assigned(tprocdef(defowner).struct) and
           (tprocdef(defowner).owner.defowner=tprocdef(defowner).struct) and
           (
            not(m_delphi in current_settings.modeswitches) or
            is_object(tprocdef(defowner).struct)
           ) then
          result:=tprocdef(defowner).struct.symtable.checkduplicate(hashedid,sym);
      end;

    procedure tparasymtable.insertdef(def: TDefEntry);
      begin
        if readonly then
          defowner.owner.insertdef(def)
        else
          inherited insertdef(def);
      end;


{****************************************************************************
                         TAbstractUniTSymtable
****************************************************************************}

    constructor tabstractuniTSymtable.create(const n : string;id:word);
      begin
        inherited create(n);
        moduleid:=id;
      end;


    function tabstractuniTSymtable.checkduplicate(var hashedid:THashedIDString;sym:TSymEntry):boolean;
      var
        hsym : tsym;
      begin
        result:=false;
        hsym:=tsym(FindWithHash(hashedid));
        if assigned(hsym) then
          begin
            if (sym is tstoredsym) and handle_generic_dummysym(hsym,tstoredsym(sym).symoptions) then
              exit;
            if hsym.typ=symconst.namespacesym then
              begin
                case sym.typ of
                  symconst.namespacesym:;
                  symconst.unitsym:
                    begin
                      HideSym(sym); { if we add a unit and there is a namespace with the same name then hide the unit name and not the namespace }
                      tnamespacesym(hsym).unitsym:=tsym(sym);
                    end
                else
                  HideSym(hsym);
                end;
              end
            else
            { In delphi (contrary to TP) you can have a symbol with the same name as the
              unit, the unit can then not be accessed anymore using
              <unit>.<id>, so we can hide the symbol.
              Do the same if we add a namespace and there is a unit with the same name }
            if (hsym.typ=symconst.unitsym) and
               ((m_delphi in current_settings.modeswitches) or (sym.typ=symconst.namespacesym)) then
              begin
                HideSym(hsym);
                if sym.typ=symconst.namespacesym then
                  tnamespacesym(sym).unitsym:=tsym(hsym);
              end
            else
              DuplicateSym(hashedid,sym,hsym);
            result:=true;
            exit;
          end;
      end;

    function tabstractuniTSymtable.iscurrentunit:boolean;
      begin
        result:=assigned(current_module) and
                (
                 (current_module.globalsymtable=self) or
                 (current_module.localsymtable=self)
                );
      end;

    procedure tabstractuniTSymtable.insertunit(sym:TSymEntry);
      var
        p:integer;
        n,ns:string;
        oldsym:TSymEntry;
      begin
        insert(sym);
        n:=sym.realname;
        p:=pos('.',n);
        ns:='';
        while p>0 do
          begin
            if ns='' then
              ns:=copy(n,1,p-1)
            else
              ns:=ns+'.'+copy(n,1,p-1);
            system.delete(n,1,p);
            oldsym:=Find(upper(ns));
            if not Assigned(oldsym) or (oldsym.typ<>namespacesym) then
              insert(tnamespacesym.create(ns));
            p:=pos('.',n);
          end;
      end;

{****************************************************************************
                              TStaticSymtable
****************************************************************************}

    constructor tstaticsymtable.create(const n : string;id:word);
      begin
        inherited create(n,id);
        symtabletype:=staticsymtable;
        symtablelevel:=main_program_level;
        currentvisibility:=vis_private;
      end;


    procedure tstaticsymtable.ppuload(ppufile:tcompilerppufile);
      begin
        inherited ppuload(ppufile);

        { now we can deref the syms and defs }
        deref;
      end;


    procedure tstaticsymtable.ppuwrite(ppufile:tcompilerppufile);
      begin
        inherited ppuwrite(ppufile);
      end;


    function tstaticsymtable.checkduplicate(var hashedid:THashedIDString;sym:TSymEntry):boolean;
      begin
        result:=inherited checkduplicate(hashedid,sym);

        if not result and
           (current_module.localsymtable=self) and
           assigned(current_module.globalsymtable) then
          result:=tglobalsymtable(current_module.globalsymtable).checkduplicate(hashedid,sym);
      end;


{****************************************************************************
                              TGlobalSymtable
****************************************************************************}

    constructor tglobalsymtable.create(const n : string;id:word);
      begin
         inherited create(n,id);
         symtabletype:=globalsymtable;
         symtablelevel:=main_program_level;
      end;


    procedure tglobalsymtable.ppuload(ppufile:tcompilerppufile);
      begin
         inherited ppuload(ppufile);

         { now we can deref the syms and defs }
         deref;
      end;


    procedure tglobalsymtable.ppuwrite(ppufile:tcompilerppufile);
      begin
        { write the symtable entries }
        inherited ppuwrite(ppufile);
      end;


{*****************************************************************************
                             tspecializesymtable
*****************************************************************************}

    constructor tspecializesymtable.create(const n : string;id:word);
      begin
        inherited create(n,id);
        { the specialize symtable does not own the syms and defs as they are all
          moved to a different symtable before the symtable is destroyed; this
          avoids calls to "extract" }
        symlist.ownsobjects:=false;
        deflist.ownsobjects:=false;
      end;

    function tspecializesymtable.iscurrentunit: boolean;
      begin
        Result := true;
      end;


{****************************************************************************
                              TWITHSYMTABLE
****************************************************************************}

    constructor twithsymtable.create(aowner:tdef;ASymList:TFPHashObjectList;refnode:tobject{tnode});
      begin
         inherited create('');
         symtabletype:=withsymtable;
         withrefnode:=refnode;
         { Replace SymList with the passed symlist }
         SymList.free;
         SymList:=ASymList;
         defowner:=aowner;
      end;


    destructor twithsymtable.destroy;
      begin
        withrefnode.free;
        { Disable SymList because we don't Own it }
        SymList:=nil;
        inherited destroy;
      end;


    procedure twithsymtable.clear;
      begin
         { remove no entry from a withsymtable as it is only a pointer to the
           recorddef  or objectdef symtable }
      end;


    procedure twithsymtable.insertdef(def:TDefEntry);
      begin
        { Definitions can't be registered in the withsymtable
          because the withsymtable is removed after the with block.
          We can't easily solve it here because the next symtable in the
          stack is not known. }
        internalerror(200602046);
      end;

{****************************************************************************
                          TSTT_ExceptionSymtable
****************************************************************************}

    constructor tstt_excepTSymtable.create;
      begin
        inherited create('');
        symtabletype:=stt_excepTSymtable;
      end;


{****************************************************************************
                          TMacroSymtable
****************************************************************************}

    constructor tmacrosymtable.create(exported: boolean);
      begin
        inherited create('');
        if exported then
          symtabletype:=exportedmacrosymtable
        else
          symtabletype:=localmacrosymtable;
        symtablelevel:=main_program_level;
      end;

{****************************************************************************
                          TEnumSymtable
****************************************************************************}

    procedure tenumsymtable.insert(sym: TSymEntry; checkdup: boolean);
      var
        value: longint;
        def: tenumdef;
      begin
        // defowner = nil only when we are loading from ppu
        if defowner<>nil then
          begin
            { First entry? Then we need to set the minval }
            value:=tenumsym(sym).value;
            def:=tenumdef(defowner);
            if SymList.count=0 then
              begin
                if value>0 then
                  def.has_jumps:=true;
                def.setmin(value);
                def.setmax(value);
              end
            else
              begin
                { check for jumps }
                if value>def.max+1 then
                  def.has_jumps:=true;
                { update low and high }
                if def.min>value then
                  def.setmin(value);
                if def.max<value then
                  def.setmax(value);
              end;
          end;
        inherited insert(sym, checkdup);
      end;

    constructor tenumsymtable.create(adefowner: tdef);
      begin
        inherited Create('');
        symtabletype:=enumsymtable;
        defowner:=adefowner;
      end;

{****************************************************************************
                          TArraySymtable
****************************************************************************}

    procedure tarraysymtable.insertdef(def: TDefEntry);
      begin
        { Enums must also be available outside the record scope,
          insert in the owner of this symtable }
        if def.typ=enumdef then
          defowner.owner.insertdef(def)
        else
          inherited insertdef(def);
      end;

    constructor tarraysymtable.create(adefowner: tdef);
      begin
        inherited Create('');
        symtabletype:=arraysymtable;
        defowner:=adefowner;
      end;

{*****************************************************************************
                             Helper Routines
*****************************************************************************}

    function FullTypeName(def,otherdef:tdef):string;
      var
        s1,s2 : string;
      begin
        if def.typ in [objectdef,recorddef] then
          s1:=tabstractrecorddef(def).RttiName
        else
          s1:=def.typename;
        { When the names are the same try to include the unit name }
        if assigned(otherdef) and
           (def.owner.symtabletype in [globalsymtable,staticsymtable]) then
          begin
            s2:=otherdef.typename;
            if upper(s1)=upper(s2) then
              s1:=def.owner.realname^+'.'+s1;
          end;
        FullTypeName:=s1;
      end;

    function generate_nested_name(symtable:tsymtable;delimiter:string):string;
      begin
        result:='';
        while assigned(symtable) and (symtable.symtabletype in [ObjectSymtable,recordsymtable]) do
          begin
            if (result='') then
              result:=symtable.name^
            else
              result:=symtable.name^+delimiter+result;
            symtable:=symtable.defowner.owner;
          end;
      end;

    procedure incompatibletypes(def1,def2:tdef);
      begin
        { When there is an errordef there is already an error message show }
        if (def2.typ=errordef) or
           (def1.typ=errordef) then
          exit;
        CGMessage2(type_e_incompatible_types,FullTypeName(def1,def2),FullTypeName(def2,def1));
      end;


    procedure hidesym(sym:TSymEntry);
      begin
        sym.realname:='$hidden'+sym.realname;
        tsym(sym).visibility:=vis_hidden;
      end;


    procedure duplicatesym(var hashedid:THashedIDString;dupsym,origsym:TSymEntry);
      var
        st : TSymtable;
      begin
        Message1(sym_e_duplicate_id,tsym(origsym).realname);
        { Write hint where the original symbol was found }
        st:=finduniTSymtable(origsym.owner);
        with tsym(origsym).fileinfo do
          begin
            if assigned(st) and
               (st.symtabletype=globalsymtable) and
               st.iscurrentunit then
              Message2(sym_h_duplicate_id_where,current_module.sourcefiles.get_file_name(fileindex),tostr(line))
            else if assigned(st.name) then
              Message2(sym_h_duplicate_id_where,'unit '+st.name^,tostr(line));
          end;
        { Rename duplicate sym to an unreachable name, but it can be
          inserted in the symtable without errors }
        inc(dupnr);
        hashedid.id:='dup'+tostr(dupnr)+hashedid.id;
        if assigned(dupsym) then
          include(tsym(dupsym).symoptions,sp_implicitrename);
      end;

    function handle_generic_dummysym(sym:TSymEntry;var symoptions:tsymoptions):boolean;
      begin
        result:=false;
        if not assigned(sym) or not (sym is tstoredsym) then
          Internalerror(2011081101);
        { For generics a dummy symbol without the parameter count is created
          if such a symbol not yet exists so that different parts of the
          parser can find that symbol. If that symbol is still a
          undefineddef we replace the generic dummy symbol's
          name with a "dup" name and use the new symbol as the generic dummy
          symbol }
        if (sp_generic_dummy in tstoredsym(sym).symoptions) and
            (sym.typ=typesym) and (ttypesym(sym).typedef.typ=undefineddef) and
            (m_delphi in current_settings.modeswitches) then
          begin
            inc(dupnr);
            sym.Owner.SymList.Rename(upper(sym.realname),'dup_'+tostr(dupnr)+sym.realname);
            include(tsym(sym).symoptions,sp_implicitrename);
            { we need to find the new symbol now if checking for a dummy }
            include(symoptions,sp_generic_dummy);
            result:=true;
          end;
      end;

{*****************************************************************************
                                  Search
*****************************************************************************}

     procedure addsymref(sym:tsym);
       begin
         { symbol uses count }
         sym.IncRefCount;
         { unit uses count }
         if assigned(current_module) and
            (sym.owner.symtabletype=globalsymtable) then
             begin
               if tglobalsymtable(sym.owner).moduleid>=current_module.unitmapsize then
                 internalerror(200501152);
               inc(current_module.unitmap[tglobalsymtable(sym.owner).moduleid].refs);
             end;
       end;


    function is_owned_by(childdef,ownerdef:tdef):boolean;
      begin
        result:=childdef=ownerdef;
        if not result and assigned(childdef.owner.defowner) then
          result:=is_owned_by(tdef(childdef.owner.defowner),ownerdef);
      end;

    function sym_is_owned_by(childsym:tsym;symtable:tsymtable):boolean;
      begin
        result:=assigned(childsym) and (childsym.owner=symtable);
        if not result and assigned(childsym) and
            (childsym.owner.symtabletype in [objectsymtable,recordsymtable]) then
          result:=sym_is_owned_by(tabstractrecorddef(childsym.owner.defowner).typesym,symtable);
      end;

    function defs_belong_to_same_generic(def1, def2: tdef): boolean;
    begin
      result:=false;
      if not assigned(def1) or not assigned(def2) then
        exit;
      { for both defs walk to the topmost generic }
      while assigned(def1.owner.defowner) and (df_generic in tstoreddef(def1.owner.defowner).defoptions) do
        def1:=tdef(def1.owner.defowner);
      while assigned(def2.owner.defowner) and (df_generic in tstoreddef(def2.owner.defowner).defoptions) do
        def2:=tdef(def2.owner.defowner);
      result:=def1=def2;
    end;

    function get_generic_in_hierarchy_by_name(srsym: tsym; def: tdef): tdef;
      var
        uname : string;
      begin
        { TODO : check regarding arrays and records declared as their type }
        if not (def.typ in [recorddef,objectdef]) then
          internalerror(2012051501);
        uname:=upper(srsym.realname);
        repeat
          if uname=copy(tabstractrecorddef(def).objname^,1,pos('$',tabstractrecorddef(def).objname^)-1) then
            begin
              result:=def;
              exit;
            end;
          def:=tdef(def.owner.defowner);
        until not (def.typ in [recorddef,objectdef]);
        result:=nil;
      end;

    function return_specialization_of_generic(nesteddef,genericdef:tdef; out resultdef:tdef):boolean;
      begin
        { TODO : check regarding arrays and records declared as their type }
        if not (nesteddef.typ in [recorddef,objectdef]) then
          internalerror(2012051601);
        repeat
          if tstoreddef(nesteddef).genericdef=genericdef then
            begin
              resultdef:=nesteddef;
              result:=true;
              exit;
            end;
          nesteddef:=tdef(nesteddef.owner.defowner);
        until not assigned(nesteddef) or not (nesteddef.typ in [recorddef,objectdef]);
        resultdef:=nil;
        result:=false;
      end;

    function is_visible_for_object(symst:tsymtable;symvisibility:tvisibility;contextobjdef:tabstractrecorddef):boolean;
      var
        symownerdef : tabstractrecorddef;
      begin
        result:=false;

        { Get objdectdef owner of the symtable for the is_related checks }
        if not assigned(symst) or
           not (symst.symtabletype in [objectsymtable,recordsymtable]) then
          internalerror(200810285);
        symownerdef:=tabstractrecorddef(symst.defowner);
        case symvisibility of
          vis_private :
            begin
              { private symbols are allowed when we are in the same
                module as they are defined }
              result:=(
                       (symownerdef.owner.symtabletype in [globalsymtable,staticsymtable]) and
                       (symownerdef.owner.iscurrentunit)
                      ) or
                      ( // the case of specialize inside the generic declaration and nested types
                       (symownerdef.owner.symtabletype in [objectsymtable,recordsymtable]) and
                       (
                         assigned(current_structdef) and
                         (
                           (current_structdef=symownerdef) or
                           (current_structdef.owner.iscurrentunit)
                         )
                       ) or
                       (
                         not assigned(current_structdef) and
                         (symownerdef.owner.iscurrentunit)
                       )
                      );
            end;
          vis_strictprivate :
            begin
              result:=assigned(current_structdef) and
                      is_owned_by(current_structdef,symownerdef);
            end;
          vis_strictprotected :
            begin
               result:=(
                         assigned(current_structdef) and
                         (current_structdef.is_related(symownerdef) or
                         is_owned_by(current_structdef,symownerdef))
                       ) or
                       (
                         { helpers can access strict protected symbols }
                         is_objectpascal_helper(contextobjdef) and
                         tobjectdef(contextobjdef).extendeddef.is_related(symownerdef)
                       );
            end;
          vis_protected :
            begin
              { protected symbols are visible in the module that defines them and
                also visible to related objects. The related object must be defined
                in the current module }
              result:=(
                       (
                        (symownerdef.owner.symtabletype in [globalsymtable,staticsymtable]) and
                        (symownerdef.owner.iscurrentunit)
                       ) or
                       (
                        assigned(contextobjdef) and
                        (contextobjdef.owner.symtabletype in [globalsymtable,staticsymtable,ObjectSymtable]) and
                        (contextobjdef.owner.iscurrentunit) and
                        contextobjdef.is_related(symownerdef)
                       ) or
                       ( // the case of specialize inside the generic declaration and nested types
                        (symownerdef.owner.symtabletype in [objectsymtable,recordsymtable]) and
                        (
                          assigned(current_structdef) and
                          (
                            (current_structdef=symownerdef) or
                            (current_structdef.owner.iscurrentunit)
                          )
                        ) or
                        (
                          not assigned(current_structdef) and
                          (symownerdef.owner.iscurrentunit)
                        ) or
                        (
                          { helpers can access protected symbols }
                          is_objectpascal_helper(contextobjdef) and
                          tobjectdef(contextobjdef).extendeddef.is_related(symownerdef)
                        )
                       )
                      );
            end;
          vis_public,
          vis_published :
            result:=true;
        end;
      end;


    function is_visible_for_object(pd:tprocdef;contextobjdef:tabstractrecorddef):boolean;
      begin
        result:=is_visible_for_object(pd.owner,pd.visibility,contextobjdef);
      end;


    function is_visible_for_object(sym:tsym;contextobjdef:tabstractrecorddef):boolean;
      var
        i  : longint;
        pd : tprocdef;
      begin
        if sym.typ=procsym then
          begin
            { A procsym is visible, when there is at least one of the procdefs visible }
            result:=false;
            for i:=0 to tprocsym(sym).ProcdefList.Count-1 do
              begin
                pd:=tprocdef(tprocsym(sym).ProcdefList[i]);
                if (pd.owner=sym.owner) and
                   is_visible_for_object(pd,contextobjdef) then
                  begin
                    result:=true;
                    exit;
                  end;
              end;
          end
        else
          result:=is_visible_for_object(sym.owner,sym.visibility,contextobjdef);
      end;


    function  searchsym(const s : TIDString;out srsym:tsym;out srsymtable:TSymtable):boolean;
      begin
        result:=searchsym_maybe_with_symoption(s,srsym,srsymtable,false,sp_none);
      end;

    function  searchsym_maybe_with_symoption(const s : TIDString;out srsym:tsym;out srsymtable:TSymtable;searchoption:boolean;option:tsymoption):boolean;
      var
        hashedid   : THashedIDString;
        contextstructdef : tabstractrecorddef;
        stackitem  : psymtablestackitem;
      begin
        result:=false;
        hashedid.id:=s;
        stackitem:=symtablestack.stack;
        while assigned(stackitem) do
          begin
            srsymtable:=stackitem^.symtable;
            if (srsymtable.symtabletype=objectsymtable) then
              begin
                { TODO : implement the search for an option in classes as well }
                if searchoption then
                  begin
                    result:=false;
                    exit;
                  end;
                if searchsym_in_class(tobjectdef(srsymtable.defowner),tobjectdef(srsymtable.defowner),s,srsym,srsymtable,true) then
                  begin
                    result:=true;
                    exit;
                  end;
              end
            else
              begin
                srsym:=tsym(srsymtable.FindWithHash(hashedid));
                if assigned(srsym) then
                  begin
                    { use the class from withsymtable only when it is
                      defined in this unit }
                    if (srsymtable.symtabletype=withsymtable) and
                       assigned(srsymtable.defowner) and
                       (srsymtable.defowner.typ in [recorddef,objectdef]) and
                       (srsymtable.defowner.owner.symtabletype in [globalsymtable,staticsymtable,objectsymtable,recordsymtable]) and
                       (srsymtable.defowner.owner.iscurrentunit) then
                      contextstructdef:=tabstractrecorddef(srsymtable.defowner)
                    else
                      contextstructdef:=current_structdef;
                    if not (srsym.owner.symtabletype in [objectsymtable,recordsymtable]) or
                       is_visible_for_object(srsym,contextstructdef) and
                       (not searchoption or (option in srsym.symoptions)) then
                      begin
                        { we need to know if a procedure references symbols
                          in the static symtable, because then it can't be
                          inlined from outside this unit }
                        if assigned(current_procinfo) and
                           (srsym.owner.symtabletype=staticsymtable) then
                          include(current_procinfo.flags,pi_uses_static_symtable);
                        addsymref(srsym);
                        result:=true;
                        exit;
                      end;
                  end;
              end;
            stackitem:=stackitem^.next;
          end;
        srsym:=nil;
        srsymtable:=nil;
      end;

    function searchsym_with_symoption(const s: TIDString;out srsym:tsym;out
      srsymtable:TSymtable;option:tsymoption):boolean;
      begin
        result:=searchsym_maybe_with_symoption(s,srsym,srsymtable,true,option);
      end;

    function searchsym_type(const s : TIDString;out srsym:tsym;out srsymtable:TSymtable):boolean;
      var
        hashedid  : THashedIDString;
        stackitem : psymtablestackitem;
        classh : tobjectdef;
      begin
        result:=false;
        hashedid.id:=s;
        stackitem:=symtablestack.stack;
        while assigned(stackitem) do
          begin
            {
              It is not possible to have type symbols in:
                parameters
              Exception are classes, objects, records, generic definitions and specializations
              that have the parameterized types inserted in the symtable.
            }
            srsymtable:=stackitem^.symtable;
            if (srsymtable.symtabletype=ObjectSymtable) then
              begin
                classh:=tobjectdef(srsymtable.defowner);
                while assigned(classh) do
                  begin
                    srsymtable:=classh.symtable;
                    srsym:=tsym(srsymtable.FindWithHash(hashedid));
                     if assigned(srsym) and
                        not(srsym.typ in [fieldvarsym,paravarsym,propertysym,procsym,labelsym]) and
                        is_visible_for_object(srsym,current_structdef) then
                       begin
                        addsymref(srsym);
                        result:=true;
                        exit;
                      end;
                    classh:=classh.childof;
                  end;
              end
            else
              begin
                srsym:=tsym(srsymtable.FindWithHash(hashedid));
                if assigned(srsym) and
                   not(srsym.typ in [fieldvarsym,paravarsym,propertysym,procsym,labelsym]) and
                   (not (srsym.owner.symtabletype in [objectsymtable,recordsymtable]) or is_visible_for_object(srsym,current_structdef)) then
                  begin
                    { we need to know if a procedure references symbols
                      in the static symtable, because then it can't be
                      inlined from outside this unit }
                    if assigned(current_procinfo) and
                       (srsym.owner.symtabletype=staticsymtable) then
                      include(current_procinfo.flags,pi_uses_static_symtable);
                    addsymref(srsym);
                    result:=true;
                    exit;
                  end;
              end;
            stackitem:=stackitem^.next;
          end;
        result:=false;
        srsym:=nil;
        srsymtable:=nil;
      end;


    function searchsym_in_module(pm:pointer;const s : TIDString;out srsym:tsym;out srsymtable:TSymtable):boolean;
      var
        pmod : tmodule;
      begin
        pmod:=tmodule(pm);
        result:=false;
        if assigned(pmod.globalsymtable) then
          begin
            srsym:=tsym(pmod.globalsymtable.Find(s));
            if assigned(srsym) then
              begin
                srsymtable:=pmod.globalsymtable;
                addsymref(srsym);
                result:=true;
                exit;
              end;
          end;
        { If the module is the current unit we also need
          to search the local symtable }
        if (pmod=current_module) and
           assigned(pmod.localsymtable) then
          begin
            srsym:=tsym(pmod.localsymtable.Find(s));
            if assigned(srsym) then
              begin
                srsymtable:=pmod.localsymtable;
                addsymref(srsym);
                result:=true;
                exit;
              end;
          end;
        srsym:=nil;
        srsymtable:=nil;
      end;


    function searchsym_in_named_module(const unitname, symname: TIDString; out srsym: tsym; out srsymtable: tsymtable): boolean;
      var
        stackitem  : psymtablestackitem;
      begin
        result:=false;
        stackitem:=symtablestack.stack;
        while assigned(stackitem) do
          begin
            srsymtable:=stackitem^.symtable;
            if (srsymtable.symtabletype=globalsymtable) and
               (srsymtable.name^=unitname) then
              begin
                srsym:=tsym(srsymtable.find(symname));
                if not assigned(srsym) then
                  break;
                result:=true;
                exit;
              end;
            stackitem:=stackitem^.next;
          end;

        { If the module is the current unit we also need
          to search the local symtable }
        if assigned(current_module.localsymtable) and
           (current_module.localsymtable.name^=unitname) then
          begin
            srsymtable:=current_module.localsymtable;
            srsym:=tsym(srsymtable.find(symname));
            if assigned(srsym) then
              begin
                result:=true;
                exit;
              end;
          end;
      end;


    function maybe_find_real_class_definition(pd: tdef; erroronfailure: boolean): tdef;
      begin
        result:=pd;
        if pd.typ<>objectdef then
          exit;
        result:=find_real_class_definition(tobjectdef(pd),erroronfailure);
      end;


    function find_real_class_definition(pd: tobjectdef; erroronfailure: boolean): tobjectdef;
      var
        hashedid   : THashedIDString;
        stackitem  : psymtablestackitem;
        srsymtable : tsymtable;
        srsym      : tsym;
        formalname,
        foundname : shortstring;
        formalnameptr,
        foundnameptr: pshortstring;
      begin
        { not a formal definition -> return it }
        if not(oo_is_formal in pd.objectoptions) then
          begin
            result:=pd;
            exit;
          end;
        hashedid.id:=pd.typesym.name;
        stackitem:=symtablestack.stack;
        while assigned(stackitem) do
          begin
            srsymtable:=stackitem^.symtable;
            { ObjC classes can't appear in generics or as nested class
              definitions. Java classes can. }
            if not(srsymtable.symtabletype in [recordsymtable,parasymtable]) or
               (is_java_class_or_interface(pd) and
                (srsymtable.symtabletype=ObjectSymtable)) then
              begin
                srsym:=tsym(srsymtable.FindWithHash(hashedid));
                if assigned(srsym) and
                   (srsym.typ=typesym) and
                   (ttypesym(srsym).typedef.typ=objectdef) and
                   (tobjectdef(ttypesym(srsym).typedef).objecttype=pd.objecttype) and
                   not(oo_is_formal in tobjectdef(ttypesym(srsym).typedef).objectoptions) then
                  begin
                    if not(oo_is_forward in tobjectdef(ttypesym(srsym).typedef).objectoptions) then
                      begin
                        { the external name for the formal and the real
                          definition must match }
                        if assigned(tobjectdef(ttypesym(srsym).typedef).import_lib) or
                           assigned(pd.import_lib) then
                          begin
                            if assigned(pd.import_lib) then
                              formalname:=pd.import_lib^+'.'
                            else
                              formalname:='';
                            formalname:=formalname+pd.objextname^;
                            if assigned(tobjectdef(ttypesym(srsym).typedef).import_lib) then
                              foundname:=tobjectdef(ttypesym(srsym).typedef).import_lib^+'.'
                            else
                              foundname:='';
                            foundname:=foundname+tobjectdef(ttypesym(srsym).typedef).objextname^;

                            formalnameptr:=@formalname;
                            foundnameptr:=@foundname;
                          end
                        else
                          begin
                            formalnameptr:=pd.objextname;
                            foundnameptr:=tobjectdef(ttypesym(srsym).typedef).objextname;
                          end;
                        if foundnameptr^<>formalnameptr^ then
                          begin
                            MessagePos2(pd.typesym.fileinfo,sym_e_external_class_name_mismatch1,formalnameptr^,pd.typename);
                            MessagePos1(srsym.fileinfo,sym_e_external_class_name_mismatch2,foundnameptr^);
                          end;
                      end;
                    result:=tobjectdef(ttypesym(srsym).typedef);
                    if assigned(current_procinfo) and
                       (srsym.owner.symtabletype=staticsymtable) then
                      include(current_procinfo.flags,pi_uses_static_symtable);
                    addsymref(srsym);
                    exit;
                  end;
              end;
            stackitem:=stackitem^.next;
          end;
        { nothing found: optionally give an error and return the original
          (empty) one }
        if erroronfailure then
          Message1(sym_e_formal_class_not_resolved,pd.objrealname^);
        result:=pd;
      end;


    function searchsym_in_class(classh: tobjectdef;contextclassh:tabstractrecorddef;const s : TIDString;out srsym:tsym;out srsymtable:TSymtable;searchhelper:boolean):boolean;
      var
        hashedid : THashedIDString;
        orgclass : tobjectdef;
        i        : longint;
      begin
        orgclass:=classh;
        { in case this is a formal class, first find the real definition }
        if assigned(classh) then
          begin
            if (oo_is_formal in classh.objectoptions) then
              classh:=find_real_class_definition(classh,true);
            { The contextclassh is used for visibility. The classh must be equal to
              or be a parent of contextclassh. E.g. for inherited searches the classh is the
              parent or a class helper. }
            if not (contextclassh.is_related(classh) or
                (is_classhelper(contextclassh) and
                 assigned(tobjectdef(contextclassh).extendeddef) and
                (tobjectdef(contextclassh).extendeddef.typ=objectdef) and
                tobjectdef(contextclassh).extendeddef.is_related(classh))) then
              internalerror(200811161);
          end;
        result:=false;
        hashedid.id:=s;
        { an Objective-C  protocol or Java interface can inherit from multiple
          other protocols/interfaces -> use ImplementedInterfaces instead }
        if is_objcprotocol(classh) or
           is_javainterface(classh) then
          begin
            srsymtable:=classh.symtable;
            srsym:=tsym(srsymtable.FindWithHash(hashedid));
            if assigned(srsym) and
               is_visible_for_object(srsym,contextclassh) then
              begin
                addsymref(srsym);
                result:=true;
                exit;
              end;
            for i:=0 to classh.ImplementedInterfaces.count-1 do
              begin
                if searchsym_in_class(TImplementedInterface(classh.ImplementedInterfaces[i]).intfdef,contextclassh,s,srsym,srsymtable,false) then
                  begin
                    result:=true;
                    exit;
                  end;
              end;
          end
        else
        if is_objectpascal_helper(classh) then
          begin
            { helpers have their own obscure search logic... }
            result:=searchsym_in_helper(classh,tobjectdef(contextclassh),s,srsym,srsymtable,false);
            if result then
              exit;
          end
        else
          begin
            while assigned(classh) do
              begin
                { search for a class helper method first if this is an Object
                  Pascal class }
                if is_class(classh) and searchhelper then
                  begin
                    result:=search_objectpascal_helper(classh,contextclassh,s,srsym,srsymtable);
                    if result then
                      { if the procsym is overloaded we need to use the
                        "original" symbol; the helper symbol will be found when
                        searching for overloads }
                      if (srsym.typ<>procsym) or
                          not (sp_has_overloaded in tprocsym(srsym).symoptions) then
                        exit;
                  end;
                srsymtable:=classh.symtable;
                srsym:=tsym(srsymtable.FindWithHash(hashedid));
                if assigned(srsym) and
                   is_visible_for_object(srsym,contextclassh) then
                  begin
                    addsymref(srsym);
                    result:=true;
                    exit;
                  end;
                classh:=classh.childof;
              end;
          end;
        if is_objcclass(orgclass) then
          result:=search_objc_helper(orgclass,s,srsym,srsymtable)
        else
          begin
            srsym:=nil;
            srsymtable:=nil;
          end;
      end;

    function  searchsym_in_record(recordh:tabstractrecorddef;const s : TIDString;out srsym:tsym;out srsymtable:TSymtable):boolean;
      var
        hashedid : THashedIDString;
      begin
        result:=false;
        hashedid.id:=s;
        { search for a record helper method first }
        result:=search_objectpascal_helper(recordh,recordh,s,srsym,srsymtable);
        if result then
          { if the procsym is overloaded we need to use the
            "original" symbol; the helper symbol will be found when
            searching for overloads }
          if (srsym.typ<>procsym) or
              not (sp_has_overloaded in tprocsym(srsym).symoptions) then
            exit;
        srsymtable:=recordh.symtable;
        srsym:=tsym(srsymtable.FindWithHash(hashedid));
        if assigned(srsym) and is_visible_for_object(srsym,recordh) then
          begin
            addsymref(srsym);
            result:=true;
            exit;
          end;
        srsym:=nil;
        srsymtable:=nil;
      end;

    function searchsym_in_class_by_msgint(classh:tobjectdef;msgid:longint;out srdef : tdef;out srsym:tsym;out srsymtable:TSymtable):boolean;
      var
        def : tdef;
        i   : longint;
      begin
        { in case this is a formal class, first find the real definition }
        if assigned(classh) and
           (oo_is_formal in classh.objectoptions) then
          classh:=find_real_class_definition(classh,true);
        result:=false;
        def:=nil;
        while assigned(classh) do
          begin
            for i:=0 to classh.symtable.DefList.Count-1 do
              begin
                def:=tstoreddef(classh.symtable.DefList[i]);
                { Find also all hidden private methods to
                  be compatible with delphi, see tw6203 (PFV) }
                if (def.typ=procdef) and
                   (po_msgint in tprocdef(def).procoptions) and
                   (tprocdef(def).messageinf.i=msgid) then
                  begin
                    srdef:=def;
                    srsym:=tprocdef(def).procsym;
                    srsymtable:=classh.symtable;
                    addsymref(srsym);
                    result:=true;
                    exit;
                  end;
              end;
            classh:=classh.childof;
          end;
        srdef:=nil;
        srsym:=nil;
        srsymtable:=nil;
      end;


    function searchsym_in_class_by_msgstr(classh:tobjectdef;const s:string;out srsym:tsym;out srsymtable:TSymtable):boolean;
      var
        def : tdef;
        i   : longint;
      begin
        { in case this is a formal class, first find the real definition }
        if assigned(classh) and
           (oo_is_formal in classh.objectoptions) then
          classh:=find_real_class_definition(classh,true);
        result:=false;
        def:=nil;
        while assigned(classh) do
          begin
            for i:=0 to classh.symtable.DefList.Count-1 do
              begin
                def:=tstoreddef(classh.symtable.DefList[i]);
                { Find also all hidden private methods to
                  be compatible with delphi, see tw6203 (PFV) }
                if (def.typ=procdef) and
                   (po_msgstr in tprocdef(def).procoptions) and
                   (tprocdef(def).messageinf.str^=s) then
                  begin
                    srsym:=tprocdef(def).procsym;
                    srsymtable:=classh.symtable;
                    addsymref(srsym);
                    result:=true;
                    exit;
                  end;
              end;
            classh:=classh.childof;
          end;
        srsym:=nil;
        srsymtable:=nil;
      end;

    function searchsym_in_helper(classh,contextclassh:tobjectdef;const s: TIDString;out srsym:tsym;out srsymtable:TSymtable;aHasInherited:boolean):boolean;
      var
        hashedid      : THashedIDString;
        parentclassh  : tobjectdef;
      begin
        result:=false;
        if not is_objectpascal_helper(classh) then
          Internalerror(2011030101);
        hashedid.id:=s;
        { in a helper things are a bit more complex:
          1. search the symbol in the helper (if not "inherited")
          2. search the symbol in the extended type
          3. search the symbol in the parent helpers
          4. only classes: search the symbol in the parents of the extended type
        }
        if not aHasInherited then
          begin
            { search in the helper itself }
            srsymtable:=classh.symtable;
            srsym:=tsym(srsymtable.FindWithHash(hashedid));
            if assigned(srsym) and
               is_visible_for_object(srsym,contextclassh) then
              begin
                addsymref(srsym);
                result:=true;
                exit;
              end;
          end;
        { now search in the extended type itself }
        if classh.extendeddef.typ in [recorddef,objectdef] then
          begin
            srsymtable:=tabstractrecorddef(classh.extendeddef).symtable;
            srsym:=tsym(srsymtable.FindWithHash(hashedid));
            if assigned(srsym) and
               is_visible_for_object(srsym,contextclassh) then
              begin
                addsymref(srsym);
                result:=true;
                exit;
              end;
          end;
        { now search in the parent helpers }
        parentclassh:=classh.childof;
        while assigned(parentclassh) do
          begin
            srsymtable:=parentclassh.symtable;
            srsym:=tsym(srsymtable.FindWithHash(hashedid));
            if assigned(srsym) and
               is_visible_for_object(srsym,contextclassh) then
              begin
                addsymref(srsym);
                result:=true;
                exit;
              end;
            parentclassh:=parentclassh.childof;
          end;
        if is_class(classh.extendeddef) then
          { now search in the parents of the extended class (with helpers!) }
          result:=searchsym_in_class(tobjectdef(classh.extendeddef).childof,contextclassh,s,srsym,srsymtable,true);
          { addsymref is already called by searchsym_in_class }
      end;

    function search_specific_assignment_operator(assignment_type:ttoken;from_def,to_def:Tdef):Tprocdef;
      var
        sym : Tprocsym;
        hashedid : THashedIDString;
        curreq,
        besteq : tequaltype;
        currpd,
        bestpd : tprocdef;
        stackitem : psymtablestackitem;
      begin
        hashedid.id:=overloaded_names[assignment_type];
        besteq:=te_incompatible;
        bestpd:=nil;
        stackitem:=symtablestack.stack;
        while assigned(stackitem) do
          begin
            sym:=Tprocsym(stackitem^.symtable.FindWithHash(hashedid));
            if sym<>nil then
              begin
                if sym.typ<>procsym then
                  internalerror(200402031);
                { if the source type is an alias then this is only the second choice,
                  if you mess with this code, check tw4093 }
                currpd:=sym.find_procdef_assignment_operator(from_def,to_def,curreq);
                if curreq>besteq then
                  begin
                    besteq:=curreq;
                    bestpd:=currpd;
                    if (besteq=te_exact) then
                      break;
                  end;
              end;
            stackitem:=stackitem^.next;
          end;
        result:=bestpd;
      end;


    function search_assignment_operator(from_def,to_def:Tdef;explicit:boolean):Tprocdef;
      begin
        { search record/object symtable first for a suitable operator }
        if from_def.typ in [recorddef,objectdef] then
          symtablestack.push(tabstractrecorddef(from_def).symtable);
        if to_def.typ in [recorddef,objectdef] then
          symtablestack.push(tabstractrecorddef(to_def).symtable);

        { if type conversion is explicit then search first for explicit
          operator overload and if not found then use implicit operator }
        if explicit then
          result:=search_specific_assignment_operator(_OP_EXPLICIT,from_def,to_def)
        else
          result:=nil;
        if result=nil then
          result:=search_specific_assignment_operator(_ASSIGNMENT,from_def,to_def);

        { restore symtable stack }
        if to_def.typ in [recorddef,objectdef] then
          symtablestack.pop(tabstractrecorddef(to_def).symtable);
        if from_def.typ in [recorddef,objectdef] then
          symtablestack.pop(tabstractrecorddef(from_def).symtable);
      end;


    function search_enumerator_operator(from_def,to_def:Tdef): Tprocdef;
      var
        sym : Tprocsym;
        hashedid : THashedIDString;
        curreq,
        besteq : tequaltype;
        currpd,
        bestpd : tprocdef;
        stackitem : psymtablestackitem;
      begin
        hashedid.id:='enumerator';
        besteq:=te_incompatible;
        bestpd:=nil;
        stackitem:=symtablestack.stack;
        while assigned(stackitem) do
          begin
            sym:=Tprocsym(stackitem^.symtable.FindWithHash(hashedid));
            if sym<>nil then
              begin
                if sym.typ<>procsym then
                  internalerror(200910241);
                { if the source type is an alias then this is only the second choice,
                  if you mess with this code, check tw4093 }
                currpd:=sym.find_procdef_enumerator_operator(from_def,to_def,curreq);
                if curreq>besteq then
                  begin
                    besteq:=curreq;
                    bestpd:=currpd;
                    if (besteq=te_exact) then
                      break;
                  end;
              end;
            stackitem:=stackitem^.next;
          end;
        result:=bestpd;
    end;


    function search_system_type(const s: TIDString): ttypesym;
      var
        sym : tsym;
      begin
        sym:=tsym(systemunit.Find(s));
        if not assigned(sym) or
           (sym.typ<>typesym) then
          cgmessage1(cg_f_unknown_system_type,s);
        result:=ttypesym(sym);
      end;


    function try_search_system_type(const s: TIDString): ttypesym;
      var
        sym : tsym;
      begin
        sym:=tsym(systemunit.Find(s));
        if not assigned(sym) then
          result:=nil
        else
          begin
            if sym.typ<>typesym then
              cgmessage1(cg_f_unknown_system_type,s);
            result:=ttypesym(sym);
          end;
      end;


    function search_named_unit_globaltype(const unitname, typename: TIDString; throwerror: boolean): ttypesym;
      var
        srsymtable: tsymtable;
        sym: tsym;
      begin
        if searchsym_in_named_module(unitname,typename,sym,srsymtable) and
           (sym.typ=typesym) then
          begin
            result:=ttypesym(sym);
            exit;
          end
        else
          begin
            if throwerror then
              cgmessage2(cg_f_unknown_type_in_unit,typename,unitname);
            result:=nil;
          end;
      end;

    function search_last_objectpascal_helper(pd,contextclassh : tabstractrecorddef;out odef : tobjectdef):boolean;
      var
        s: string;
        list: TFPObjectList;
        i: integer;
        st: tsymtable;
      begin
        result:=false;
        odef:=nil;
        { when there are no helpers active currently then we don't need to do
          anything }
        if current_module.extendeddefs.count=0 then
          exit;
        { no helpers for anonymous types }
        if not assigned(pd.objrealname) or (pd.objrealname^='') then
          exit;
        { if pd is defined inside a procedure we must not use make_mangledname
          (as a helper may not be defined in a procedure this is no problem...)}
        st:=pd.owner;
        while st.symtabletype in [objectsymtable,recordsymtable] do
          st:=st.defowner.owner;
        if st.symtabletype=localsymtable then
          exit;
        { the mangled name is used as the key for tmodule.extendeddefs }
        s:=make_mangledname('',pd.symtable,'');
        list:=TFPObjectList(current_module.extendeddefs.Find(s));
        if assigned(list) and (list.count>0) then
          begin
            i:=list.count-1;
            repeat
              odef:=tobjectdef(list[list.count-1]);
              result:=(odef.owner.symtabletype in [staticsymtable,globalsymtable]) or
                      is_visible_for_object(tobjectdef(list[i]).typesym,contextclassh);
              dec(i);
            until result or (i<0);
            if not result then
              { just to be sure that noone uses odef }
              odef:=nil;
          end;
      end;

    function search_objectpascal_helper(pd,contextclassh : tabstractrecorddef;const s: string; out srsym: tsym; out srsymtable: tsymtable):boolean;

      var
        hashedid  : THashedIDString;
        classh : tobjectdef;
        i : integer;
        pdef : tprocdef;
      begin
        result:=false;

        { if there is no class helper for the class then there is no need to
          search further }
        if not search_last_objectpascal_helper(pd,contextclassh,classh) then
          exit;

        hashedid.id:=s;

        repeat
          srsymtable:=classh.symtable;
          srsym:=tsym(srsymtable.FindWithHash(hashedid));

          if srsym<>nil then
            begin
              if srsym.typ=propertysym then
                begin
                  result:=true;
                  exit;
                end;
              for i:=0 to tprocsym(srsym).procdeflist.count-1 do
                begin
                  pdef:=tprocdef(tprocsym(srsym).procdeflist[i]);
                  if not is_visible_for_object(pdef.owner,pdef.visibility,contextclassh) then
                    continue;
                  { we need to know if a procedure references symbols
                    in the static symtable, because then it can't be
                    inlined from outside this unit }
                  if assigned(current_procinfo) and
                     (srsym.owner.symtabletype=staticsymtable) then
                    include(current_procinfo.flags,pi_uses_static_symtable);
                  { the first found method wins }
                  srsym:=tprocdef(tprocsym(srsym).procdeflist[i]).procsym;
                  srsymtable:=srsym.owner;
                  addsymref(srsym);
                  result:=true;
                  exit;
                end;
            end;

          { try the helper parent if available }
          classh:=classh.childof;
        until classh=nil;

        srsym:=nil;
        srsymtable:=nil;
      end;

    function search_objc_helper(pd : tobjectdef;const s : string; out srsym: tsym; out srsymtable: tsymtable):boolean;
      var
        hashedid   : THashedIDString;
        stackitem  : psymtablestackitem;
        i          : longint;
        defowner   : tobjectdef;
      begin
        hashedid.id:=class_helper_prefix+s;
        stackitem:=symtablestack.stack;
        while assigned(stackitem) do
          begin
            srsymtable:=stackitem^.symtable;
            srsym:=tsym(srsymtable.FindWithHash(hashedid));
            if assigned(srsym) then
              begin
                if not(srsymtable.symtabletype in [globalsymtable,staticsymtable]) or
                   not(srsym.owner.symtabletype in [globalsymtable,staticsymtable]) or
                   (srsym.typ<>procsym) then
                  internalerror(2009111505);
                { check whether this procsym includes a helper for this particular class }
                for i:=0 to tprocsym(srsym).procdeflist.count-1 do
                  begin
                    { does pd inherit from (or is the same as) the class
                      that this method's category extended?

                      Warning: this list contains both category and objcclass methods
                       (for id.randommethod), so only check category methods here
                    }
                    defowner:=tobjectdef(tprocdef(tprocsym(srsym).procdeflist[i]).owner.defowner);
                    if (oo_is_classhelper in defowner.objectoptions) and
                       pd.is_related(defowner.childof) then
                      begin
                        { we need to know if a procedure references symbols
                          in the static symtable, because then it can't be
                          inlined from outside this unit }
                        if assigned(current_procinfo) and
                           (srsym.owner.symtabletype=staticsymtable) then
                          include(current_procinfo.flags,pi_uses_static_symtable);
                        { no need to keep looking. There might be other
                          categories that extend this, a parent or child
                          class with a method with the same name (either
                          overriding this one, or overridden by this one),
                          but that doesn't matter as far as the basic
                          procsym is concerned.
                        }
                        srsym:=tprocdef(tprocsym(srsym).procdeflist[i]).procsym;
                        srsymtable:=srsym.owner;
                        addsymref(srsym);
                        result:=true;
                        exit;
                      end;
                  end;
              end;
            stackitem:=stackitem^.next;
          end;
        srsym:=nil;
        srsymtable:=nil;
        result:=false;
      end;


    function search_objc_method(const s : string; out srsym: tsym; out srsymtable: tsymtable):boolean;
      var
        hashedid   : THashedIDString;
        stackitem  : psymtablestackitem;
        i          : longint;
      begin
        hashedid.id:=class_helper_prefix+s;
        stackitem:=symtablestack.stack;
        while assigned(stackitem) do
          begin
            srsymtable:=stackitem^.symtable;
            srsym:=tsym(srsymtable.FindWithHash(hashedid));
            if assigned(srsym) then
              begin
                if not(srsymtable.symtabletype in [globalsymtable,staticsymtable]) or
                   not(srsym.owner.symtabletype in [globalsymtable,staticsymtable]) or
                   (srsym.typ<>procsym) then
                  internalerror(2009112005);
                { check whether this procsym includes a helper for this particular class }
                for i:=0 to tprocsym(srsym).procdeflist.count-1 do
                  begin
                    { we need to know if a procedure references symbols
                      in the static symtable, because then it can't be
                      inlined from outside this unit }
                    if assigned(current_procinfo) and
                       (srsym.owner.symtabletype=staticsymtable) then
                      include(current_procinfo.flags,pi_uses_static_symtable);
                    { no need to keep looking. There might be other
                      methods with the same name, but that doesn't matter
                      as far as the basic procsym is concerned.
                    }
                    srsym:=tprocdef(tprocsym(srsym).procdeflist[i]).procsym;
                    { We need the symtable in which the classhelper-like sym
                      is located, not the objectdef. The reason is that the
                      callnode will climb the symtablestack until it encounters
                      this symtable to start looking for overloads (and it won't
                      find the objectsymtable in which this method sym is
                      located

                    srsymtable:=srsym.owner;
                    }
                    addsymref(srsym);
                    result:=true;
                    exit;
                  end;
              end;
            stackitem:=stackitem^.next;
          end;
        srsym:=nil;
        srsymtable:=nil;
        result:=false;
      end;


    function search_struct_member(pd : tabstractrecorddef;const s : string):tsym;
    { searches n in symtable of pd and all anchestors }
      var
        hashedid   : THashedIDString;
        srsym      : tsym;
        orgpd      : tabstractrecorddef;
        srsymtable : tsymtable;
      begin
        { in case this is a formal class, first find the real definition }
        if (oo_is_formal in pd.objectoptions) then
          pd:=find_real_class_definition(tobjectdef(pd),true);
        if search_objectpascal_helper(pd, pd, s, result, srsymtable) then
          exit;
        hashedid.id:=s;
        orgpd:=pd;
        while assigned(pd) do
         begin
           srsym:=tsym(pd.symtable.FindWithHash(hashedid));
           if assigned(srsym) then
            begin
              search_struct_member:=srsym;
              exit;
            end;
           if pd.typ=objectdef then
             pd:=tobjectdef(pd).childof
           else
             pd:=nil;
         end;

        { not found, now look for class helpers }
        if is_objcclass(pd) then
          search_objc_helper(tobjectdef(orgpd),s,result,srsymtable)
        else
          result:=nil;
      end;


    function search_macro(const s : string):tsym;
      var
        stackitem  : psymtablestackitem;
        hashedid   : THashedIDString;
        srsym      : tsym;
      begin
        hashedid.id:=s;

        { First search the localmacrosymtable before searching the
          global macrosymtables from the units }
        if assigned(current_module) then
          begin
            srsym:=tsym(current_module.localmacrosymtable.FindWithHash(hashedid));
            if assigned(srsym) then
              begin
                result:= srsym;
                exit;
              end;
          end;

        stackitem:=macrosymtablestack.stack;
        while assigned(stackitem) do
          begin
            srsym:=tsym(stackitem^.symtable.FindWithHash(hashedid));
            if assigned(srsym) then
              begin
                result:= srsym;
                exit;
              end;
            stackitem:=stackitem^.next;
          end;
        result:= nil;
      end;


    function defined_macro(const s : string):boolean;
      var
        mac: tmacro;
      begin
        mac:=tmacro(search_macro(s));
        if assigned(mac) then
          begin
            mac.is_used:=true;
            defined_macro:=mac.defined;
          end
        else
          defined_macro:=false;
      end;


{****************************************************************************
                              Object Helpers
****************************************************************************}

   function search_default_property(pd : tabstractrecorddef) : tpropertysym;
   { returns the default property of a class, searches also anchestors }
     var
       _defaultprop : tpropertysym;
       helperpd : tobjectdef;
     begin
        _defaultprop:=nil;
        { first search in helper's hierarchy }
        if search_last_objectpascal_helper(pd,nil,helperpd) then
          while assigned(helperpd) do
            begin
              helperpd.symtable.SymList.ForEachCall(@tstoredsymtable(helperpd.symtable).testfordefaultproperty,@_defaultprop);
              if assigned(_defaultprop) then
                break;
              helperpd:=helperpd.childof;
            end;
        if assigned(_defaultprop) then
          begin
            search_default_property:=_defaultprop;
            exit;
          end;
        { now search in the type's hierarchy itself }
        while assigned(pd) do
          begin
             pd.symtable.SymList.ForEachCall(@tstoredsymtable(pd.symtable).testfordefaultproperty,@_defaultprop);
             if assigned(_defaultprop) then
               break;
             if (pd.typ=objectdef) then
               pd:=tobjectdef(pd).childof
             else
               break;
          end;
        search_default_property:=_defaultprop;
     end;


{****************************************************************************
                              Macro Helpers
****************************************************************************}

    procedure def_system_macro(const name : string);
      var
        mac : tmacro;
        s: string;
      begin
         if name = '' then
           internalerror(2004121202);
         s:= upper(name);
         mac:=tmacro(search_macro(s));
         if not assigned(mac) then
           begin
             mac:=tmacro.create(s);
             if assigned(current_module) then
               current_module.localmacrosymtable.insert(mac)
             else
               initialmacrosymtable.insert(mac);
           end;
         Message1(parser_c_macro_defined,mac.name);
         mac.defined:=true;
      end;


    procedure set_system_macro(const name, value : string);
      var
        mac : tmacro;
        s: string;
      begin
        if name = '' then
          internalerror(2004121203);
         s:= upper(name);
         mac:=tmacro(search_macro(s));
         if not assigned(mac) then
           begin
             mac:=tmacro.create(s);
             if assigned(current_module) then
               current_module.localmacrosymtable.insert(mac)
             else
               initialmacrosymtable.insert(mac);
           end
         else
           begin
             mac.is_compiler_var:=false;
             if assigned(mac.buftext) then
               freemem(mac.buftext,mac.buflen);
           end;
         Message2(parser_c_macro_set_to,mac.name,value);
         mac.buflen:=length(value);
         getmem(mac.buftext,mac.buflen);
         move(value[1],mac.buftext^,mac.buflen);
         mac.defined:=true;
      end;


    procedure set_system_compvar(const name, value : string);
      var
        mac : tmacro;
        s: string;
      begin
        if name = '' then
          internalerror(2004121204);
         s:= upper(name);
         mac:=tmacro(search_macro(s));
         if not assigned(mac) then
           begin
             mac:=tmacro.create(s);
             mac.is_compiler_var:=true;
             if assigned(current_module) then
               current_module.localmacrosymtable.insert(mac)
             else
               initialmacrosymtable.insert(mac);
           end
         else
           begin
             mac.is_compiler_var:=true;
             if assigned(mac.buftext) then
               freemem(mac.buftext,mac.buflen);
           end;
         Message2(parser_c_macro_set_to,mac.name,value);
         mac.buflen:=length(value);
         getmem(mac.buftext,mac.buflen);
         move(value[1],mac.buftext^,mac.buflen);
         mac.defined:=true;
      end;


    procedure undef_system_macro(const name : string);
      var
        mac : tmacro;
        s: string;
      begin
         if name = '' then
           internalerror(2004121205);
         s:= upper(name);
         mac:=tmacro(search_macro(s));
         if not assigned(mac) then
           {If not found, then it's already undefined.}
         else
           begin
             Message1(parser_c_macro_undefined,mac.name);
             mac.defined:=false;
             mac.is_compiler_var:=false;
             { delete old definition }
             if assigned(mac.buftext) then
               begin
                  freemem(mac.buftext,mac.buflen);
                  mac.buftext:=nil;
               end;
           end;
      end;


{$ifdef UNITALIASES}
{****************************************************************************
                              TUNIT_ALIAS
 ****************************************************************************}

    constructor tunit_alias.create(const n:string);
      var
        i : longint;
      begin
        i:=pos('=',n);
        if i=0 then
         fail;
        inherited createname(Copy(n,1,i-1));
        newname:=stringdup(Copy(n,i+1,255));
      end;


    destructor tunit_alias.destroy;
      begin
        stringdispose(newname);
        inherited destroy;
      end;


    procedure addunitalias(const n:string);
      begin
        unitaliases^.insert(tunit_alias,init(Upper(n))));
      end;


    function getunitalias(const n:string):string;
      var
        p : punit_alias;
      begin
        p:=punit_alias(unitaliases^.Find(Upper(n)));
        if assigned(p) then
         getunitalias:=punit_alias(p).newname^
        else
         getunitalias:=n;
      end;
{$endif UNITALIASES}


{****************************************************************************
                           Init/Done Symtable
****************************************************************************}

   procedure InitSymtable;
     begin
       { Reset symbolstack }
       symtablestack:=nil;
       systemunit:=nil;
       { create error syms and def }
       generrorsym:=terrorsym.create;
       generrordef:=terrordef.create;
       { macros }
       initialmacrosymtable:=tmacrosymtable.create(false);
       macrosymtablestack:=TSymtablestack.create;
       macrosymtablestack.push(initialmacrosymtable);
{$ifdef UNITALIASES}
       { unit aliases }
       unitaliases:=TFPHashObjectList.create;
{$endif}
       { set some global vars to nil, might be important for the ide }
       class_tobject:=nil;
       interface_iunknown:=nil;
       interface_idispatch:=nil;
       rec_tguid:=nil;
       dupnr:=0;
     end;


   procedure DoneSymtable;
      begin
        generrorsym.owner:=nil;
        generrorsym.free;
        generrordef.owner:=nil;
        generrordef.free;
        initialmacrosymtable.free;
        macrosymtablestack.free;
{$ifdef UNITALIASES}
        unitaliases.free;
{$endif}
     end;

end.
