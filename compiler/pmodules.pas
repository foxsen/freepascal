{
    Copyright (c) 1998-2008 by Florian Klaempfl

    Handles the parsing and loading of the modules (ppufiles)

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
unit pmodules;

{$i fpcdefs.inc}

interface

    procedure proc_unit;
    procedure proc_package;
    procedure proc_program(islibrary : boolean);

implementation

    uses
       SysUtils,
       globtype,version,systems,tokens,
       cutils,cfileutl,cclasses,comphook,
       globals,verbose,fmodule,finput,fppu,
       symconst,symbase,symtype,symdef,symsym,symtable,symcreat,
       wpoinfo,
       aasmtai,aasmdata,aasmcpu,aasmbase,
       cgbase,cgobj,ngenutil,
       nbas,nutils,ncgutil,
       link,assemble,import,export,gendef,ppu,comprsrc,dbgbase,
       cresstr,procinfo,
       pexports,
       objcgutl,
       wpobase,
       scanner,pbase,pexpr,psystem,psub,pdecsub,ptype,
       cpuinfo;


    procedure create_objectfile;
      var
        DLLScanner      : TDLLScanner;
        s               : string;
        KeepShared      : TCmdStrList;
      begin
        { try to create import entries from system dlls }
        if (tf_has_dllscanner in target_info.flags) and
           (not current_module.linkOtherSharedLibs.Empty) then
         begin
           { Init DLLScanner }
           if assigned(CDLLScanner[target_info.system]) then
            DLLScanner:=CDLLScanner[target_info.system].Create
           else
            internalerror(200104121);
           KeepShared:=TCmdStrList.Create;
           { Walk all shared libs }
           While not current_module.linkOtherSharedLibs.Empty do
            begin
              S:=current_module.linkOtherSharedLibs.Getusemask(link_always);
              if not DLLScanner.scan(s) then
               KeepShared.Concat(s);
            end;
           DLLscanner.Free;
           { Recreate import section }
           if (target_info.system in [system_i386_win32,system_i386_wdosx]) then
            begin
              if assigned(current_asmdata.asmlists[al_imports]) then
               current_asmdata.asmlists[al_imports].clear
              else
               current_asmdata.asmlists[al_imports]:=TAsmList.Create;
              importlib.generatelib;
            end;
           { Readd the not processed files }
           while not KeepShared.Empty do
            begin
              s:=KeepShared.GetFirst;
              current_module.linkOtherSharedLibs.add(s,link_always);
            end;
           KeepShared.Free;
         end;

        { Start and end module debuginfo, at least required for stabs
          to insert n_sourcefile lines }
        if (cs_debuginfo in current_settings.moduleswitches) or
           (cs_use_lineinfo in current_settings.globalswitches) then
          current_debuginfo.insertmoduleinfo;

        { create the .s file and assemble it }
        GenerateAsm(false);

        { Also create a smartlinked version ? }
        if create_smartlink_library then
         begin
           GenerateAsm(true);
           if (af_needar in target_asm.flags) then
             Linker.MakeStaticLibrary;
         end;

        { resource files }
        CompileResourceFiles;
      end;


    procedure insertobjectfile;
    { Insert the used object file for this unit in the used list for this unit }
      begin
        current_module.linkunitofiles.add(current_module.objfilename,link_static);
        current_module.flags:=current_module.flags or uf_static_linked;

        if create_smartlink_library then
         begin
           current_module.linkunitstaticlibs.add(current_module.staticlibfilename ,link_smart);
           current_module.flags:=current_module.flags or uf_smart_linked;
         end;
      end;


    procedure create_dwarf_frame;
      begin
        { Dwarf conflicts with smartlinking in separate .a files }
        if create_smartlink_library then
          exit;
        { Call frame information }
        { MWE: we write our own info, so dwarf asm support is not really needed }
        { if (af_supports_dwarf in target_asm.flags) and }
        { CFI is currently broken for Darwin }
        if not(target_info.system in systems_darwin) and
           (
            (tf_needs_dwarf_cfi in target_info.flags) or
            (paratargetdbg in [dbg_dwarf2, dbg_dwarf3])
           ) then
          begin
            current_asmdata.asmlists[al_dwarf_frame].Free;
            current_asmdata.asmlists[al_dwarf_frame] := TAsmList.create;
            current_asmdata.asmcfi.generate_code(current_asmdata.asmlists[al_dwarf_frame]);
          end;
      end;

    Function CheckResourcesUsed : boolean;
      var
        hp           : tused_unit;
        found        : Boolean;
      begin
        CheckResourcesUsed:=tf_has_winlike_resources in target_info.flags;
        if not CheckResourcesUsed then exit;

        hp:=tused_unit(usedunits.first);
        found:=((current_module.flags and uf_has_resourcefiles)=uf_has_resourcefiles);
        If not found then
          While Assigned(hp) and not found do
            begin
            Found:=((hp.u.flags and uf_has_resourcefiles)=uf_has_resourcefiles);
            hp:=tused_unit(hp.next);
            end;
        CheckResourcesUsed:=found;
      end;

    procedure AddUnit(const s:string);
      var
        hp : tppumodule;
        unitsym : tunitsym;
      begin
        { load unit }
        hp:=registerunit(current_module,s,'');
        hp.loadppu;
        hp.adddependency(current_module);
        { add to symtable stack }
        symtablestack.push(hp.globalsymtable);
        if (m_mac in current_settings.modeswitches) and
           assigned(hp.globalmacrosymtable) then
          macrosymtablestack.push(hp.globalmacrosymtable);
        { insert unitsym }
        unitsym:=tunitsym.create(s,hp);
        inc(unitsym.refs);
        tabstractunitsymtable(current_module.localsymtable).insertunit(unitsym);
        { add to used units }
        current_module.addusedunit(hp,false,unitsym);
      end;


    procedure maybeloadvariantsunit;
      var
        hp : tmodule;
      begin
        { Do we need the variants unit? Skip this
          for VarUtils unit for bootstrapping }
        if (current_module.flags and uf_uses_variants=0) or
           (current_module.modulename^='VARUTILS') then
          exit;
        { Variants unit already loaded? }
        hp:=tmodule(loaded_units.first);
        while assigned(hp) do
          begin
            if hp.modulename^='VARIANTS' then
              exit;
            hp:=tmodule(hp.next);
          end;
        { Variants unit is not loaded yet, load it now }
        Message(parser_w_implicit_uses_of_variants_unit);
        AddUnit('variants');
      end;


    function MaybeRemoveResUnit : boolean;
      var
        resources_used : boolean;
        hp : tmodule;
        uu : tused_unit;
        unitname : shortstring;
      begin
        { We simply remove the unit from:
           - usedunit list, so that things like init/finalization table won't
              contain references to this unit
           - loaded_units list, so that the unit object file doesn't get linked
             with the executable. }
        { Note: on windows we always need resources! }
        resources_used:=(target_info.system in systems_all_windows)
                         or CheckResourcesUsed;
        if (not resources_used) and (tf_has_winlike_resources in target_info.flags) then
          begin
            { resources aren't used, so we don't need this unit }
            if target_res.id=res_ext then
              unitname:='FPEXTRES'
            else
              unitname:='FPINTRES';
            Message1(unit_u_unload_resunit,unitname);
            { find the module }
            hp:=tmodule(loaded_units.first);
            while assigned(hp) do
              begin
                if hp.is_unit and (hp.modulename^=unitname) then break;
                hp:=tmodule(hp.next);
              end;
            if not assigned(hp) then
              internalerror(200801071);
            { find its tused_unit in the global list }
            uu:=tused_unit(usedunits.first);
            while assigned(uu) do
              begin
                if uu.u=hp then break;
                uu:=tused_unit(uu.next);
              end;
            if not assigned(uu) then
              internalerror(200801072);
           { remove the tused_unit }
            usedunits.Remove(uu);
            uu.Free;
           { remove the module }
            loaded_units.Remove(hp);
            unloaded_units.Concat(hp);
          end;
        MaybeRemoveResUnit:=resources_used;
      end;


    procedure loaddefaultunits;
      begin
        { we are going to rebuild the symtablestack, clear it first }
        symtablestack.clear;
        macrosymtablestack.clear;

        { macro symtable }
        macrosymtablestack.push(initialmacrosymtable);

        { are we compiling the system unit? }
        if (cs_compilesystem in current_settings.moduleswitches) then
         begin
           systemunit:=tglobalsymtable(current_module.localsymtable);
           { create system defines }
           create_intern_symbols;
           create_intern_types;
           { Set the owner of errorsym and errortype to symtable to
             prevent crashes when accessing .owner }
           generrorsym.owner:=systemunit;
           generrordef.owner:=systemunit;
           exit;
         end;

        { insert the system unit, it is allways the first. Load also the
          internal types from the system unit }
        AddUnit('system');
        systemunit:=tglobalsymtable(symtablestack.top);
        load_intern_types;

        { Set the owner of errorsym and errortype to symtable to
          prevent crashes when accessing .owner }
        generrorsym.owner:=systemunit;
        generrordef.owner:=systemunit;

        { Units only required for main module }
        if not(current_module.is_unit) then
         begin
           { Heaptrc unit, load heaptrace before any other units especially objpas }
           if (cs_use_heaptrc in current_settings.globalswitches) then
             AddUnit('heaptrc');
           { Lineinfo unit }
           if (cs_use_lineinfo in current_settings.globalswitches) then begin
             case paratargetdbg of
               dbg_stabs:
                 AddUnit('lineinfo');
               dbg_stabx:
                 AddUnit('lnfogdb');
               else
                 AddUnit('lnfodwrf');
             end;
           end;
           { Valgrind requires c memory manager }
           if (cs_gdb_valgrind in current_settings.globalswitches) then
             AddUnit('cmem');
{$ifdef cpufpemu}
           { Floating point emulation unit?
             softfpu must be in the system unit anyways (FK)
           if (cs_fp_emulation in current_settings.moduleswitches) and not(target_info.system in system_wince) then
             AddUnit('softfpu');
           }
{$endif cpufpemu}
           { Which kind of resource support?
             Note: if resources aren't used this unit will be removed later,
             otherwise we need it here since it must be loaded quite early }
           if (tf_has_winlike_resources in target_info.flags) then
             if target_res.id=res_ext then
               AddUnit('fpextres')
             else
               AddUnit('fpintres');
         end;
        { Objpas unit? }
        if m_objpas in current_settings.modeswitches then
          AddUnit('objpas');

        { Macpas unit? }
        if m_mac in current_settings.modeswitches then
          AddUnit('macpas');

        if m_iso in current_settings.modeswitches then
          AddUnit('iso7185');

        { default char=widechar? }
        if m_default_unicodestring in current_settings.modeswitches then
          AddUnit('uuchar');

        { Objective-C support unit? }
        if (m_objectivec1 in current_settings.modeswitches) then
          begin
            { interface to Objective-C run time }
            AddUnit('objc');
            loadobjctypes;
            { NSObject }
            if not(current_module.is_unit) or
               (current_module.modulename^<>'OBJCBASE') then
              AddUnit('objcbase');
          end;
        { Profile unit? Needed for go32v2 only }
        if (cs_profile in current_settings.moduleswitches) and
           (target_info.system in [system_i386_go32v2,system_i386_watcom]) then
          AddUnit('profile');
        if (cs_load_fpcylix_unit in current_settings.globalswitches) then
          begin
            AddUnit('fpcylix');
            AddUnit('dynlibs');
          end;

        { CPU targets with microcontroller support can add a controller specific unit }
{$if defined(ARM) or defined(AVR)}
        if (target_info.system in systems_embedded) and (current_settings.controllertype<>ct_none) and
          (embedded_controllers[current_settings.controllertype].controllerunitstr<>'') then
          AddUnit(embedded_controllers[current_settings.controllertype].controllerunitstr);
{$endif ARM}
      end;


    procedure loadautounits;
      var
        hs,s : string;
      begin
        hs:=autoloadunits;
        repeat
          s:=GetToken(hs,',');
          if s='' then
            break;
          AddUnit(s);
        until false;
      end;


    procedure loadunits;
      var
         s,sorg  : ansistring;
         fn      : string;
         pu      : tused_unit;
         hp2     : tmodule;
         unitsym : tunitsym;
         filepos : tfileposinfo;
      begin
         consume(_USES);
         repeat
           s:=pattern;
           sorg:=orgpattern;
           filepos:=current_tokenpos;
           consume(_ID);
           while token=_POINT do
             begin
               consume(_POINT);
               s:=s+'.'+pattern;
               sorg:=sorg+'.'+orgpattern;
               consume(_ID);
             end;
           { support "<unit> in '<file>'" construct, but not for tp7 }
           fn:='';
           if not(m_tp7 in current_settings.modeswitches) and
              try_to_consume(_OP_IN) then
             fn:=FixFileName(get_stringconst);
           { Give a warning if lineinfo is loaded }
           if s='LINEINFO' then begin
            Message(parser_w_no_lineinfo_use_switch);
            if (paratargetdbg in [dbg_dwarf2, dbg_dwarf3]) then
              s := 'LNFODWRF';
            sorg := s;
           end;
           { Give a warning if objpas is loaded }
           if s='OBJPAS' then
            Message(parser_w_no_objpas_use_mode);
           { Using the unit itself is not possible }
           if (s<>current_module.modulename^) then
            begin
              { check if the unit is already used }
              hp2:=nil;
              pu:=tused_unit(current_module.used_units.first);
              while assigned(pu) do
               begin
                 if (pu.u.modulename^=s) then
                  begin
                    hp2:=pu.u;
                    break;
                  end;
                 pu:=tused_unit(pu.next);
               end;
              if not assigned(hp2) then
                hp2:=registerunit(current_module,sorg,fn)
              else
                Message1(sym_e_duplicate_id,s);
              { Create unitsym, we need to use the name as specified, we
                can not use the modulename because that can be different
                when -Un is used }
              current_tokenpos:=filepos;
              unitsym:=tunitsym.create(sorg,nil);
              tabstractunitsymtable(current_module.localsymtable).insertunit(unitsym);
              { the current module uses the unit hp2 }
              current_module.addusedunit(hp2,true,unitsym);
            end
           else
            Message1(sym_e_duplicate_id,s);
           if token=_COMMA then
            begin
              pattern:='';
              consume(_COMMA);
            end
           else
            break;
         until false;

         { Load the units }
         pu:=tused_unit(current_module.used_units.first);
         while assigned(pu) do
          begin
            { Only load the units that are in the current
              (interface/implementation) uses clause }
            if pu.in_uses and
               (pu.in_interface=current_module.in_interface) then
             begin
               tppumodule(pu.u).loadppu;
               { is our module compiled? then we can stop }
               if current_module.state=ms_compiled then
                exit;
               { add this unit to the dependencies }
               pu.u.adddependency(current_module);
               { save crc values }
               pu.checksum:=pu.u.crc;
               pu.interface_checksum:=pu.u.interface_crc;
               pu.indirect_checksum:=pu.u.indirect_crc;
               { connect unitsym to the module }
               pu.unitsym.module:=pu.u;
               { add to symtable stack }
               symtablestack.push(pu.u.globalsymtable);
               if (m_mac in current_settings.modeswitches) and
                  assigned(pu.u.globalmacrosymtable) then
                 macrosymtablestack.push(pu.u.globalmacrosymtable);
               { check hints }
               pu.u.check_hints;
             end;
            pu:=tused_unit(pu.next);
          end;

         consume(_SEMICOLON);
      end;


     procedure reset_all_defs;
       begin
         if assigned(current_module.wpoinfo) then
           current_module.wpoinfo.resetdefs;
       end;


    procedure free_localsymtables(st:TSymtable);
      var
        i   : longint;
        def : tstoreddef;
        pd  : tprocdef;
      begin
        for i:=0 to st.DefList.Count-1 do
          begin
            def:=tstoreddef(st.DefList[i]);
            if def.typ=procdef then
              begin
                pd:=tprocdef(def);
                if assigned(pd.localst) and
                   (pd.localst.symtabletype<>staticsymtable) and
                   not(po_inline in pd.procoptions) then
                  begin
                    free_localsymtables(pd.localst);
                    pd.localst.free;
                    pd.localst:=nil;
                  end;
              end;
          end;
      end;


    procedure parse_implementation_uses;
      begin
         if token=_USES then
           loadunits;
      end;


    procedure setupglobalswitches;
      begin
        if (cs_create_pic in current_settings.moduleswitches) then
          begin
            def_system_macro('FPC_PIC');
            def_system_macro('PIC');
          end;
      end;


    function create_main_proc(const name:string;potype:tproctypeoption;st:TSymtable):tcgprocinfo;
      var
        ps  : tprocsym;
        pd  : tprocdef;
      begin
        { there should be no current_procinfo available }
        if assigned(current_procinfo) then
         internalerror(200304275);
        {Generate a procsym for main}
        ps:=tprocsym.create('$'+name);
        { main are allways used }
        inc(ps.refs);
        st.insert(ps);
        pd:=tprocdef(cnodeutils.create_main_procdef(target_info.cprefix+name,potype,ps));
        { We don't need is a local symtable. Change it into the static
          symtable }
        pd.localst.free;
        pd.localst:=st;
        handle_calling_convention(pd);
        { set procinfo and current_procinfo.procdef }
        result:=tcgprocinfo(cprocinfo.create(nil));
        result.procdef:=pd;
        { main proc does always a call e.g. to init system unit }
        include(result.flags,pi_do_call);
      end;


    procedure release_main_proc(pi:tcgprocinfo);
      begin
        { remove localst as it was replaced by staticsymtable }
        pi.procdef.localst:=nil;
        { remove procinfo }
        current_module.procinfo:=nil;
        pi.free;
        pi:=nil;
      end;



    { Insert _GLOBAL_OFFSET_TABLE_ symbol if system uses it }

    procedure maybe_load_got;
{$ifdef i386}
       var
         gotvarsym : tstaticvarsym;
{$endif i386}
      begin
{$ifdef i386}
         if (cs_create_pic in current_settings.moduleswitches) and
            (tf_pic_uses_got in target_info.flags) then
           begin
             { insert symbol for got access in assembler code}
             gotvarsym:=tstaticvarsym.create('_GLOBAL_OFFSET_TABLE_',
                          vs_value,voidpointertype,[vo_is_external]);
             gotvarsym.set_mangledname('_GLOBAL_OFFSET_TABLE_');
             current_module.localsymtable.insert(gotvarsym);
             { avoid unnecessary warnings }
             gotvarsym.varstate:=vs_read;
             gotvarsym.refs:=1;
           end;
{$endif i386}
      end;

    function gen_implicit_initfinal(flag:word;st:TSymtable):tcgprocinfo;
      begin
        { create procdef }
        case flag of
          uf_init :
            begin
              result:=create_main_proc(make_mangledname('',current_module.localsymtable,'init_implicit'),potype_unitinit,st);
              result.procdef.aliasnames.insert(make_mangledname('INIT$',current_module.localsymtable,''));
            end;
          uf_finalize :
            begin
              result:=create_main_proc(make_mangledname('',current_module.localsymtable,'finalize_implicit'),potype_unitfinalize,st);
              result.procdef.aliasnames.insert(make_mangledname('FINALIZE$',current_module.localsymtable,''));
              if (not current_module.is_unit) then
                result.procdef.aliasnames.insert('PASCALFINALIZE');
            end;
          else
            internalerror(200304253);
        end;
        result.code:=cnothingnode.create;
      end;


    procedure copy_macro(p:TObject; arg:pointer);
      begin
        current_module.globalmacrosymtable.insert(tmacro(p).getcopy);
      end;

    function try_consume_hintdirective(var moduleopt:tmoduleoptions; var deprecatedmsg:pshortstring):boolean;
      var
        deprecated_seen,
        last_is_deprecated:boolean;
      begin
        try_consume_hintdirective:=false;
        deprecated_seen:=false;
        repeat
          last_is_deprecated:=false;
          case idtoken of
            _LIBRARY :
              begin
                include(moduleopt,mo_hint_library);
                try_consume_hintdirective:=true;
              end;
            _DEPRECATED :
              begin
                { allow deprecated only once }
                if deprecated_seen then
                  break;
                include(moduleopt,mo_hint_deprecated);
                try_consume_hintdirective:=true;
                last_is_deprecated:=true;
                deprecated_seen:=true;
              end;
            _EXPERIMENTAL :
              begin
                include(moduleopt,mo_hint_experimental);
                try_consume_hintdirective:=true;
              end;
            _PLATFORM :
              begin
                include(moduleopt,mo_hint_platform);
                try_consume_hintdirective:=true;
              end;
            _UNIMPLEMENTED :
              begin
                include(moduleopt,mo_hint_unimplemented);
                try_consume_hintdirective:=true;
              end;
            else
              break;
          end;
          consume(Token);
          { handle deprecated message }
          if ((token=_CSTRING) or (token=_CCHAR)) and last_is_deprecated then
            begin
              if deprecatedmsg<>nil then
                internalerror(201001221);
              if token=_CSTRING then
                deprecatedmsg:=stringdup(cstringpattern)
              else
                deprecatedmsg:=stringdup(pattern);
              consume(token);
              include(moduleopt,mo_has_deprecated_msg);
            end;
        until false;
      end;


{$ifdef jvm}
      procedure addmoduleclass;
        var
          def: tobjectdef;
          typesym: ttypesym;
        begin
          { java_jlobject may not have been parsed yet (system unit); in any
            case, we only use this to refer to the class type, so inheritance
            does not matter }
          def:=tobjectdef.create(odt_javaclass,'__FPC_JVM_Module_Class_Alias$',nil);
          include(def.objectoptions,oo_is_external);
          include(def.objectoptions,oo_is_sealed);
          def.objextname:=stringdup(current_module.realmodulename^);
          typesym:=ttypesym.create('__FPC_JVM_Module_Class_Alias$',def);
          symtablestack.top.insert(typesym);
        end;
{$endif jvm}

    procedure proc_unit;

      function is_assembler_generated:boolean;
      var
        hal : tasmlisttype;
      begin
        result:=false;
        if Errorcount=0 then
          begin
            for hal:=low(TasmlistType) to high(TasmlistType) do
              if not current_asmdata.asmlists[hal].empty then
                begin
                  result:=true;
                  exit;
                end;
          end;
      end;

      var
         main_file: tinputfile;
{$ifdef EXTDEBUG}
         store_crc,
{$endif EXTDEBUG}
         store_interface_crc,
         store_indirect_crc: cardinal;
         s1,s2  : ^string; {Saves stack space}
         force_init_final : boolean;
         init_procinfo,
         finalize_procinfo : tcgprocinfo;
         unitname : ansistring;
         unitname8 : string[8];
         ag: boolean;
{$ifdef debug_devirt}
         i: longint;
{$endif debug_devirt}
      begin
         init_procinfo:=nil;
         finalize_procinfo:=nil;

         if m_mac in current_settings.modeswitches then
           current_module.mode_switch_allowed:= false;

         consume(_UNIT);
         if compile_level=1 then
          Status.IsExe:=false;

         unitname:=orgpattern;
         consume(_ID);
         while token=_POINT do
           begin
             consume(_POINT);
             unitname:=unitname+'.'+orgpattern;
             consume(_ID);
           end;

         { create filenames and unit name }
         main_file := current_scanner.inputfile;
         while assigned(main_file.next) do
           main_file := main_file.next;

         new(s1);
         s1^:=current_module.modulename^;
         current_module.SetFileName(main_file.path+main_file.name,true);
         current_module.SetModuleName(unitname);

         { check for system unit }
         new(s2);
         s2^:=upper(ChangeFileExt(ExtractFileName(main_file.name),''));
         unitname8:=copy(current_module.modulename^,1,8);
         if (cs_check_unit_name in current_settings.globalswitches) and
            (
             not(
                 (current_module.modulename^=s2^) or
                 (
                  (length(current_module.modulename^)>8) and
                  (unitname8=s2^)
                 )
                )
             or
             (
              (length(s1^)>8) and
              (s1^<>current_module.modulename^)
             )
            ) then
          Message1(unit_e_illegal_unit_name,current_module.realmodulename^);
         if (current_module.modulename^='SYSTEM') then
          include(current_settings.moduleswitches,cs_compilesystem);
         dispose(s2);
         dispose(s1);

         if (target_info.system in systems_unit_program_exports) then
           exportlib.preparelib(current_module.realmodulename^);

         { parse hint directives }
         try_consume_hintdirective(current_module.moduleoptions, current_module.deprecatedmsg);

         consume(_SEMICOLON);
         consume(_INTERFACE);
         { global switches are read, so further changes aren't allowed }
         current_module.in_global:=false;

         { handle the global switches }
         setupglobalswitches;

         message1(unit_u_loading_interface_units,current_module.modulename^);

         { update status }
         status.currentmodule:=current_module.realmodulename^;

         { maybe turn off m_objpas if we are compiling objpas }
         if (current_module.modulename^='OBJPAS') then
           exclude(current_settings.modeswitches,m_objpas);

         { maybe turn off m_mac if we are compiling macpas }
         if (current_module.modulename^='MACPAS') then
           exclude(current_settings.modeswitches,m_mac);

         parse_only:=true;

         { generate now the global symboltable,
           define first as local to overcome dependency conflicts }
         current_module.localsymtable:=tglobalsymtable.create(current_module.modulename^,current_module.moduleid);

         { insert unitsym of this unit to prevent other units having
           the same name }
         tabstractunitsymtable(current_module.localsymtable).insertunit(tunitsym.create(current_module.realmodulename^,current_module));

         { load default units, like the system unit }
         loaddefaultunits;

         { insert qualifier for the system unit (allows system.writeln) }
         if not(cs_compilesystem in current_settings.moduleswitches) and
            (token=_USES) then
           begin
             loadunits;
             { has it been compiled at a higher level ?}
             if current_module.state=ms_compiled then
               exit;
           end;

         { move the global symtable from the temporary local to global }
         current_module.globalsymtable:=current_module.localsymtable;
         current_module.localsymtable:=nil;

         { number all units, so we know if a unit is used by this unit or
           needs to be added implicitly }
         current_module.updatemaps;

         { create whole program optimisation information (may already be
           updated in the interface, e.g., in case of classrefdef typed
           constants }
         current_module.wpoinfo:=tunitwpoinfo.create;

         { ... parse the declarations }
         Message1(parser_u_parsing_interface,current_module.realmodulename^);
         symtablestack.push(current_module.globalsymtable);
{$ifdef jvm}
         { fake classdef to represent the class corresponding to the unit }
         addmoduleclass;
{$endif}
         read_interface_declarations;
         symtablestack.pop(current_module.globalsymtable);

         { Export macros defined in the interface for macpas. The macros
           are put in the globalmacrosymtable that will only be used by other
           units. The current unit continues to use the localmacrosymtable }
         if (m_mac in current_settings.modeswitches) then
          begin
            current_module.globalmacrosymtable:=tmacrosymtable.create(true);
            current_module.localmacrosymtable.SymList.ForEachCall(@copy_macro,nil);
          end;

         { leave when we got an error }
         if (Errorcount>0) and not status.skip_error then
          begin
            Message1(unit_f_errors_in_unit,tostr(Errorcount));
            status.skip_error:=true;
            exit;
          end;

         { Our interface is compiled, generate CRC and switch to implementation }
         if not(cs_compilesystem in current_settings.moduleswitches) and
            (Errorcount=0) then
           tppumodule(current_module).getppucrc;
         current_module.in_interface:=false;
         current_module.interface_compiled:=true;

         { First reload all units depending on our interface, we need to do this
           in the implementation part to prevent erroneous circular references }
         tppumodule(current_module).setdefgeneration;
         tppumodule(current_module).reload_flagged_units;

         { Parse the implementation section }
         if (m_mac in current_settings.modeswitches) and try_to_consume(_END) then
           current_module.interface_only:=true
         else
           current_module.interface_only:=false;

         parse_only:=false;

         { create static symbol table }
         current_module.localsymtable:=tstaticsymtable.create(current_module.modulename^,current_module.moduleid);

         { Insert _GLOBAL_OFFSET_TABLE_ symbol if system uses it }
         maybe_load_got;

         if not current_module.interface_only then
           begin
             consume(_IMPLEMENTATION);
             Message1(unit_u_loading_implementation_units,current_module.modulename^);
             { Read the implementation units }
             parse_implementation_uses;
           end;

         if current_module.state=ms_compiled then
           exit;

         { All units are read, now give them a number }
         current_module.updatemaps;

         symtablestack.push(current_module.globalsymtable);
         symtablestack.push(current_module.localsymtable);

         if not current_module.interface_only then
           begin
             Message1(parser_u_parsing_implementation,current_module.modulename^);
             if current_module.in_interface then
               internalerror(200212285);

             { Compile the unit }
             init_procinfo:=create_main_proc(make_mangledname('',current_module.localsymtable,'init'),potype_unitinit,current_module.localsymtable);
             init_procinfo.procdef.aliasnames.insert(make_mangledname('INIT$',current_module.localsymtable,''));
             init_procinfo.parse_body;
             { save file pos for debuginfo }
             current_module.mainfilepos:=init_procinfo.entrypos;
           end;

         { Generate specializations of objectdefs methods }
         generate_specialization_procs;

         { add implementations for synthetic method declarations added by
           the compiler }
         add_synthetic_method_implementations(current_module.globalsymtable);
         add_synthetic_method_implementations(current_module.localsymtable);

         { if the unit contains ansi/widestrings, initialization and
           finalization code must be forced }
         force_init_final:=tglobalsymtable(current_module.globalsymtable).needs_init_final or
                           tstaticsymtable(current_module.localsymtable).needs_init_final;

         { should we force unit initialization? }
         { this is a hack, but how can it be done better ? }
         { Now the sole purpose of this is to change 'init' to 'init_implicit',
           is it needed at all? (Sergei) }
         { it's needed in case cnodeutils.force_init = true }
         if (force_init_final or cnodeutils.force_init) and
            assigned(init_procinfo) and
            has_no_code(init_procinfo.code) then
           begin
             { first release the not used init procinfo }
             if assigned(init_procinfo) then
               release_main_proc(init_procinfo);
             init_procinfo:=gen_implicit_initfinal(uf_init,current_module.localsymtable);
           end;
         { finalize? }
         if not current_module.interface_only and (token=_FINALIZATION) then
           begin
              { Compile the finalize }
              finalize_procinfo:=create_main_proc(make_mangledname('',current_module.localsymtable,'finalize'),potype_unitfinalize,current_module.localsymtable);
              finalize_procinfo.procdef.aliasnames.insert(make_mangledname('FINALIZE$',current_module.localsymtable,''));
              finalize_procinfo.parse_body;
           end
         else if force_init_final or cnodeutils.force_final then
           finalize_procinfo:=gen_implicit_initfinal(uf_finalize,current_module.localsymtable);

         { Now both init and finalize bodies are read and it is known
           which variables are used in both init and finalize we can now
           generate the code. This is required to prevent putting a variable in
           a register that is also used in the finalize body (PFV) }
         if assigned(init_procinfo) then
           begin
             if (force_init_final or cnodeutils.force_init) or
                not(has_no_code(init_procinfo.code)) then
               begin
                 init_procinfo.code:=cnodeutils.wrap_proc_body(init_procinfo.procdef,init_procinfo.code);
                 init_procinfo.generate_code;
                 current_module.flags:=current_module.flags or uf_init;
               end;
             init_procinfo.resetprocdef;
             release_main_proc(init_procinfo);
           end;
         if assigned(finalize_procinfo) then
           begin
             if force_init_final or
                cnodeutils.force_init or
                not(has_no_code(finalize_procinfo.code)) then
               begin
                 finalize_procinfo.code:=cnodeutils.wrap_proc_body(finalize_procinfo.procdef,finalize_procinfo.code);
                 finalize_procinfo.generate_code;
                 current_module.flags:=current_module.flags or uf_finalize;
               end;
             finalize_procinfo.resetprocdef;
             release_main_proc(finalize_procinfo);
           end;

         symtablestack.pop(current_module.localsymtable);
         symtablestack.pop(current_module.globalsymtable);

         { the last char should always be a point }
         consume(_POINT);

         { reset wpo flags for all defs }
         reset_all_defs;

         if (Errorcount=0) then
           begin
             { tests, if all (interface) forwards are resolved }
             tstoredsymtable(current_module.globalsymtable).check_forwards;
             { check if all private fields are used }
             tstoredsymtable(current_module.globalsymtable).allprivatesused;

             { test static symtable }
             tstoredsymtable(current_module.localsymtable).allsymbolsused;
             tstoredsymtable(current_module.localsymtable).allprivatesused;
             tstoredsymtable(current_module.localsymtable).check_forwards;
             tstoredsymtable(current_module.localsymtable).checklabels;

             { used units }
             current_module.allunitsused;
           end;

         { leave when we got an error }
         if (Errorcount>0) and not status.skip_error then
          begin
            Message1(unit_f_errors_in_unit,tostr(Errorcount));
            status.skip_error:=true;
            exit;
          end;

         { if an Objective-C module, generate rtti and module info }
         MaybeGenerateObjectiveCImageInfo(current_module.globalsymtable,current_module.localsymtable);

         { do we need to add the variants unit? }
         maybeloadvariantsunit;

         { generate wrappers for interfaces }
         gen_intf_wrappers(current_asmdata.asmlists[al_procedures],current_module.globalsymtable,false);
         gen_intf_wrappers(current_asmdata.asmlists[al_procedures],current_module.localsymtable,false);

         { generate rtti/init tables }
         write_persistent_type_info(current_module.globalsymtable,true);
         write_persistent_type_info(current_module.localsymtable,false);

         { Tables }
         cnodeutils.InsertThreadvars;

         { Resource strings }
         GenerateResourceStrings;

         { Widestring typed constants }
         cnodeutils.InsertWideInits;

         { Resourcestring references }
         cnodeutils.InsertResStrInits;

         { generate debuginfo }
         if (cs_debuginfo in current_settings.moduleswitches) then
           current_debuginfo.inserttypeinfo;

         { generate imports }
         if current_module.ImportLibraryList.Count>0 then
           importlib.generatelib;

         { insert own objectfile, or say that it's in a library
           (no check for an .o when loading) }
         ag:=is_assembler_generated;
         if ag then
           insertobjectfile
         else
           begin
             current_module.flags:=current_module.flags or uf_no_link;
             current_module.flags:=current_module.flags and not (uf_has_stabs_debuginfo or uf_has_dwarf_debuginfo);
           end;

         if ag then
          begin
            { create callframe info }
            create_dwarf_frame;
            { assemble }
            create_objectfile;
          end;

         { Write out the ppufile after the object file has been created }
         store_interface_crc:=current_module.interface_crc;
         store_indirect_crc:=current_module.indirect_crc;
{$ifdef EXTDEBUG}
         store_crc:=current_module.crc;
{$endif EXTDEBUG}
         if (Errorcount=0) then
           tppumodule(current_module).writeppu;

         if not(cs_compilesystem in current_settings.moduleswitches) then
           begin
             if store_interface_crc<>current_module.interface_crc then
               Message1(unit_u_interface_crc_changed,current_module.ppufilename);
             if store_indirect_crc<>current_module.indirect_crc then
               Message1(unit_u_indirect_crc_changed,current_module.ppufilename);
           end;
{$ifdef EXTDEBUG}
         if not(cs_compilesystem in current_settings.moduleswitches) then
           if (store_crc<>current_module.crc) and simplify_ppu then
             Message1(unit_u_implementation_crc_changed,current_module.ppufilename);
{$endif EXTDEBUG}

         { release local symtables that are not needed anymore }
         free_localsymtables(current_module.globalsymtable);
         free_localsymtables(current_module.localsymtable);

         { leave when we got an error }
         if (Errorcount>0) and not status.skip_error then
          begin
            Message1(unit_f_errors_in_unit,tostr(Errorcount));
            status.skip_error:=true;
            exit;
          end;

{$ifdef debug_devirt}
         { print out all instantiated class/object types }
         writeln('constructed object/class/classreftypes in ',current_module.realmodulename^);
         for i := 0 to current_module.wpoinfo.createdobjtypes.count-1 do
           begin
             write('  ',tdef(current_module.wpoinfo.createdobjtypes[i]).GetTypeName);
             case tdef(current_module.wpoinfo.createdobjtypes[i]).typ of
               objectdef:
                 case tobjectdef(current_module.wpoinfo.createdobjtypes[i]).objecttype of
                   odt_object:
                     writeln(' (object)');
                   odt_class:
                     writeln(' (class)');
                   else
                     internalerror(2008101103);
                 end;
               else
                 internalerror(2008101104);
             end;
           end;

         for i := 0 to current_module.wpoinfo.createdclassrefobjtypes.count-1 do
           begin
             write('  Class Of ',tdef(current_module.wpoinfo.createdclassrefobjtypes[i]).GetTypeName);
             case tdef(current_module.wpoinfo.createdclassrefobjtypes[i]).typ of
               objectdef:
                 case tobjectdef(current_module.wpoinfo.createdclassrefobjtypes[i]).objecttype of
                   odt_class:
                     writeln(' (classrefdef)');
                   else
                     internalerror(2008101105);
                 end
               else
                 internalerror(2008101102);
             end;
           end;
{$endif debug_devirt}

        Message1(unit_u_finished_compiling,current_module.modulename^);
      end;


    procedure procexport(const s : string);
      var
        hp : texported_item;
      begin
        hp:=texported_item.create;
        hp.name:=stringdup(s);
        hp.options:=hp.options or eo_name;
        exportlib.exportprocedure(hp);
      end;


    procedure varexport(const s : string);
      var
        hp : texported_item;
      begin
        hp:=texported_item.create;
        hp.name:=stringdup(s);
        hp.options:=hp.options or eo_name;
        exportlib.exportvar(hp);
      end;


    procedure insert_export(sym : TObject;arg:pointer);
      var
        i : longint;
        item : TCmdStrListItem;
      begin
        case TSym(sym).typ of
          { ignore: }
          unitsym,
          syssym,
          constsym,
          enumsym,
          typesym:
            ;
          procsym:
            begin
              for i:=0 to tprocsym(sym).ProcdefList.Count-1 do
                begin
                  if not(tprocdef(tprocsym(sym).ProcdefList[i]).proccalloption in [pocall_internproc]) and
                    ((tprocdef(tprocsym(sym).ProcdefList[i]).procoptions*[po_external])=[]) and
                    ((tsymtable(arg).symtabletype=globalsymtable) or
                     ((tsymtable(arg).symtabletype=staticsymtable) and (po_public in tprocdef(tprocsym(sym).ProcdefList[i]).procoptions))
                    ) then
                    begin
                      procexport(tprocdef(tprocsym(sym).ProcdefList[i]).mangledname);
                      { walk through all aliases }
                      item:=TCmdStrListItem(tprocdef(tprocsym(sym).ProcdefList[i]).aliasnames.first);
                      while assigned(item) do
                        begin
                          { avoid duplicate entries, sometimes aliasnames contains the mangledname }
                          if item.str<>tprocdef(tprocsym(sym).ProcdefList[i]).mangledname then
                            procexport(item.str);
                          item:=TCmdStrListItem(item.next);
                        end;
                    end;
                end;
            end;
          staticvarsym:
            begin
              varexport(tsym(sym).mangledname);
            end;
          else
            begin
              writeln('unknown: ',ord(TSym(sym).typ));
            end;
        end;
      end;


    Function RewritePPU(const PPUFn,PPLFn:String):Boolean;
      Var
        MakeStatic : Boolean;
      Var
        buffer : array[0..$1fff] of byte;
        inppu,
        outppu : tppufile;
        b,
        untilb : byte;
        l,m    : longint;
        f      : file;
        ext,
        s      : string;
        ppuversion : dword;
      begin
        Result:=false;
        MakeStatic:=False;
        inppu:=tppufile.create(PPUFn);
        if not inppu.openfile then
         begin
           inppu.free;
           Comment(V_Error,'Could not open : '+PPUFn);
           Exit;
         end;
      { Check the ppufile }
        if not inppu.CheckPPUId then
         begin
           inppu.free;
           Comment(V_Error,'Not a PPU File : '+PPUFn);
           Exit;
         end;
        ppuversion:=inppu.GetPPUVersion;
        if ppuversion<CurrentPPUVersion then
         begin
           inppu.free;
           Comment(V_Error,'Wrong PPU Version '+tostr(ppuversion)+' in '+PPUFn);
           Exit;
         end;
      { No .o file generated for this ppu, just skip }
        if (inppu.header.flags and uf_no_link)<>0 then
         begin
           inppu.free;
           Result:=true;
           Exit;
         end;
      { Already a lib? }
        if (inppu.header.flags and uf_in_library)<>0 then
         begin
           inppu.free;
           Comment(V_Error,'PPU is already in a library : '+PPUFn);
           Exit;
         end;
      { We need a static linked unit }
        if (inppu.header.flags and uf_static_linked)=0 then
         begin
           inppu.free;
           Comment(V_Error,'PPU is not static linked : '+PPUFn);
           Exit;
         end;
      { Check if shared is allowed }
        if tsystem(inppu.header.target) in [system_i386_go32v2] then
         begin
           Comment(V_Error,'Shared library not supported for ppu target, switching to static library');
           MakeStatic:=true;
         end;
      { Create the new ppu }
        if PPUFn=PPLFn then
         outppu:=tppufile.create('ppumove.$$$')
        else
         outppu:=tppufile.create(PPLFn);
        outppu.createfile;
      { Create new header, with the new flags }
        outppu.header:=inppu.header;
        outppu.header.flags:=outppu.header.flags or uf_in_library;
        if MakeStatic then
         outppu.header.flags:=outppu.header.flags or uf_static_linked
        else
         outppu.header.flags:=outppu.header.flags or uf_shared_linked;
      { read until the object files are found }
        untilb:=iblinkunitofiles;
        repeat
          b:=inppu.readentry;
          if b in [ibendinterface,ibend] then
           begin
             inppu.free;
             outppu.free;
             Comment(V_Error,'No files to be linked found : '+PPUFn);
             Exit;
           end;
          if b<>untilb then
           begin
             repeat
               inppu.getdatabuf(buffer,sizeof(buffer),l);
               outppu.putdata(buffer,l);
             until l<sizeof(buffer);
             outppu.writeentry(b);
           end;
        until (b=untilb);
      { we have now reached the section for the files which need to be added,
        now add them to the list }
        case b of
          iblinkunitofiles :
            begin
              { add all o files, and save the entry when not creating a static
                library to keep staticlinking possible }
              while not inppu.endofentry do
               begin
                 s:=inppu.getstring;
                 m:=inppu.getlongint;
                 if not MakeStatic then
                  begin
                    outppu.putstring(s);
                    outppu.putlongint(m);
                  end;
                 current_module.linkotherofiles.add(s,link_always);;
               end;
              if not MakeStatic then
               outppu.writeentry(b);
            end;
      {    iblinkunitstaticlibs :
            begin
              AddToLinkFiles(ExtractLib(inppu.getstring));
              if not inppu.endofentry then
               begin
                 repeat
                   inppu.getdatabuf(buffer^,bufsize,l);
                   outppu.putdata(buffer^,l);
                 until l<bufsize;
                 outppu.writeentry(b);
               end;
             end; }
        end;
      { just add a new entry with the new lib }
        if MakeStatic then
         begin
           outppu.putstring('imp'+current_module.realmodulename^);
           outppu.putlongint(link_static);
           outppu.writeentry(iblinkunitstaticlibs)
         end
        else
         begin
           outppu.putstring('imp'+current_module.realmodulename^);
           outppu.putlongint(link_shared);
           outppu.writeentry(iblinkunitsharedlibs);
         end;
      { read all entries until the end and write them also to the new ppu }
        repeat
          b:=inppu.readentry;
        { don't write ibend, that's written automatically }
          if b<>ibend then
           begin
             if b=iblinkothersharedlibs then
               begin
                 while not inppu.endofentry do
                   begin
                     s:=inppu.getstring;
                     m:=inppu.getlongint;

                     outppu.putstring(s);
                     outppu.putlongint(m);

                     { strip lib prefix }
                     if copy(s,1,3)='lib' then
                       delete(s,1,3);
                     ext:=ExtractFileExt(s);
                     if ext<>'' then
                       delete(s,length(s)-length(ext)+1,length(ext));

                     current_module.linkOtherSharedLibs.add(s,link_always);
                   end;
               end
             else
               repeat
                 inppu.getdatabuf(buffer,sizeof(buffer),l);
                 outppu.putdata(buffer,l);
               until l<sizeof(buffer);
             outppu.writeentry(b);
           end;
        until b=ibend;
      { write the last stuff and close }
        outppu.flush;
        outppu.writeheader;
        outppu.free;
        inppu.free;
      { rename }
        if PPUFn=PPLFn then
         begin
           {$push}{$I-}
            assign(f,PPUFn);
            erase(f);
            assign(f,'ppumove.$$$');
            rename(f,PPUFn);
           {$pop}
           if ioresult<>0 then;
         end;
        Result:=True;
      end;


    procedure createimportlibfromexports;
      var
        hp : texported_item;
      begin
        hp:=texported_item(current_module._exports.first);
        while assigned(hp) do
          begin
            current_module.AddExternalImport(current_module.realmodulename^,hp.name^,hp.name^,hp.index,hp.is_var,false);
            hp:=texported_item(hp.next);
          end;
      end;


    procedure proc_package;
      var
        main_file : tinputfile;
        hp,hp2    : tmodule;
        {finalize_procinfo,
        init_procinfo,
        main_procinfo : tcgprocinfo;}
        force_init_final : boolean;
        uu : tused_unit;
        module_name: ansistring;
      begin
         Status.IsPackage:=true;
         Status.IsExe:=true;
         parse_only:=false;
         {main_procinfo:=nil;
         init_procinfo:=nil;
         finalize_procinfo:=nil;}

         if not RelocSectionSetExplicitly then
           RelocSection:=true;

         { Relocation works only without stabs under Windows when }
         { external linker (LD) is used.  LD generates relocs for }
         { stab sections which is not loaded in memory. It causes }
         { AV error when DLL is loaded and relocation is needed.  }
         { Internal linker does not have this problem.            }
         if RelocSection and
            (target_info.system in systems_all_windows+[system_i386_wdosx]) and
            (cs_link_extern in current_settings.globalswitches) then
           begin
              include(current_settings.globalswitches,cs_link_strip);
              { Warning stabs info does not work with reloc section !! }
              if (cs_debuginfo in current_settings.moduleswitches) and
                 (target_dbg.id=dbg_stabs) then
                begin
                  Message1(parser_w_parser_reloc_no_debug,current_module.mainsource);
                  Message(parser_w_parser_win32_debug_needs_WN);
                  exclude(current_settings.moduleswitches,cs_debuginfo);
                end;
           end;
         { get correct output names }
         main_file := current_scanner.inputfile;
         while assigned(main_file.next) do
           main_file := main_file.next;

         current_module.SetFileName(main_file.path+main_file.name,true);

         { consume _PACKAGE word }
         consume(_ID);

         module_name:=orgpattern;
         consume(_ID);
         while token=_POINT do
           begin
             consume(_POINT);
             module_name:=module_name+'.'+orgpattern;
             consume(_ID);
           end;

         current_module.setmodulename(module_name);
         current_module.ispackage:=true;
         exportlib.preparelib(module_name);

         if tf_library_needs_pic in target_info.flags then
           include(current_settings.moduleswitches,cs_create_pic);

         consume(_SEMICOLON);

         { global switches are read, so further changes aren't allowed }
         current_module.in_global:=false;

         { setup things using the switches }
         setupglobalswitches;

         { set implementation flag }
         current_module.in_interface:=false;
         current_module.interface_compiled:=true;

         { insert after the unit symbol tables the static symbol table }
         { of the program                                             }
         current_module.localsymtable:=tstaticsymtable.create(current_module.modulename^,current_module.moduleid);

         {Load the units used by the program we compile.}
         if token=_REQUIRES then
           begin
           end;

         {Load the units used by the program we compile.}
         if (token=_ID) and (idtoken=_CONTAINS) then
           begin
             { consume _CONTAINS word }
             consume(_ID);
             while true do
               begin
                 if token=_ID then
                   begin
                     module_name:=pattern;
                     consume(_ID);
                     while token=_POINT do
                       begin
                         consume(_POINT);
                         module_name:=module_name+'.'+orgpattern;
                         consume(_ID);
                       end;
                     AddUnit(module_name);
                   end
                 else
                   consume(_ID);
                 if token=_COMMA then
                   consume(_COMMA)
                 else break;
               end;
             consume(_SEMICOLON);
           end;

         { All units are read, now give them a number }
         current_module.updatemaps;

         {Insert the name of the main program into the symbol table.}
         if current_module.realmodulename^<>'' then
           tabstractunitsymtable(current_module.localsymtable).insertunit(tunitsym.create(current_module.realmodulename^,current_module));

         Message1(parser_u_parsing_implementation,current_module.mainsource);

         symtablestack.push(current_module.localsymtable);

         { create whole program optimisation information }
         current_module.wpoinfo:=tunitwpoinfo.create;

         { should we force unit initialization? }
         force_init_final:=tstaticsymtable(current_module.localsymtable).needs_init_final;
         if force_init_final or cnodeutils.force_init then
           {init_procinfo:=gen_implicit_initfinal(uf_init,current_module.localsymtable)};

         { Add symbol to the exports section for win32 so smartlinking a
           DLL will include the edata section }
         if assigned(exportlib) and
            (target_info.system in [system_i386_win32,system_i386_wdosx]) and
            ((current_module.flags and uf_has_exports)<>0) then
           current_asmdata.asmlists[al_procedures].concat(tai_const.createname(make_mangledname('EDATA',current_module.localsymtable,''),0));

         { all labels must be defined before generating code }
         if Errorcount=0 then
           tstoredsymtable(current_module.localsymtable).checklabels;

         symtablestack.pop(current_module.localsymtable);

         { consume the last point }
         consume(_END);
         consume(_POINT);

         if (Errorcount=0) then
           begin
             { test static symtable }
             tstoredsymtable(current_module.localsymtable).allsymbolsused;
             tstoredsymtable(current_module.localsymtable).allprivatesused;
             tstoredsymtable(current_module.localsymtable).check_forwards;

             current_module.allunitsused;
           end;

         new_section(current_asmdata.asmlists[al_globals],sec_data,'_FPCDummy',4);
         current_asmdata.asmlists[al_globals].concat(tai_symbol.createname_global('_FPCDummy',AT_DATA,0));
         current_asmdata.asmlists[al_globals].concat(tai_const.create_32bit(0));

         new_section(current_asmdata.asmlists[al_procedures],sec_code,'',0);
         current_asmdata.asmlists[al_procedures].concat(tai_symbol.createname_global('_DLLMainCRTStartup',AT_FUNCTION,0));
         gen_fpc_dummy(current_asmdata.asmlists[al_procedures]);
         current_asmdata.asmlists[al_procedures].concat(tai_const.createname('_FPCDummy',0));

         { leave when we got an error }
         if (Errorcount>0) and not status.skip_error then
           begin
             Message1(unit_f_errors_in_unit,tostr(Errorcount));
             status.skip_error:=true;
             exit;
           end;

         { remove all unused units, this happends when units are removed
           from the uses clause in the source and the ppu was already being loaded }
         hp:=tmodule(loaded_units.first);
         while assigned(hp) do
          begin
            hp2:=hp;
            hp:=tmodule(hp.next);
            if hp2.is_unit and
               not assigned(hp2.globalsymtable) then
              loaded_units.remove(hp2);
          end;

         { force exports }
         uu:=tused_unit(usedunits.first);
         while assigned(uu) do
           begin
             uu.u.globalsymtable.symlist.ForEachCall(@insert_export,uu.u.globalsymtable);
             { check localsymtable for exports too to get public symbols }
             uu.u.localsymtable.symlist.ForEachCall(@insert_export,uu.u.localsymtable);

             { create special exports }
             if (uu.u.flags and uf_init)<>0 then
               procexport(make_mangledname('INIT$',uu.u.globalsymtable,''));
             if (uu.u.flags and uf_finalize)<>0 then
               procexport(make_mangledname('FINALIZE$',uu.u.globalsymtable,''));
             if (uu.u.flags and uf_threadvars)=uf_threadvars then
               varexport(make_mangledname('THREADVARLIST',uu.u.globalsymtable,''));

             uu:=tused_unit(uu.next);
           end;

{$ifdef arm}
         { Insert .pdata section for arm-wince.
           It is needed for exception handling. }
         if target_info.system in [system_arm_wince] then
           InsertPData;
{$endif arm}

         { generate debuginfo }
         if (cs_debuginfo in current_settings.moduleswitches) then
           current_debuginfo.inserttypeinfo;

         exportlib.generatelib;

         { write all our exports to the import library,
           needs to be done after exportlib.generatelib; }
         createimportlibfromexports;

         { generate imports }
         if current_module.ImportLibraryList.Count>0 then
           importlib.generatelib;

         { Reference all DEBUGINFO sections from the main .fpc section }
         if (cs_debuginfo in current_settings.moduleswitches) then
           current_debuginfo.referencesections(current_asmdata.asmlists[al_procedures]);

         { insert own objectfile }
         insertobjectfile;

         { assemble and link }
         create_objectfile;

         { We might need the symbols info if not using
           the default do_extractsymbolinfo
           which is a dummy function PM }
         needsymbolinfo:=do_extractsymbolinfo<>@def_extractsymbolinfo;
         { release all local symtables that are not needed anymore }
         if (not needsymbolinfo) then
           free_localsymtables(current_module.localsymtable);

         { leave when we got an error }
         if (Errorcount>0) and not status.skip_error then
          begin
            Message1(unit_f_errors_in_unit,tostr(Errorcount));
            status.skip_error:=true;
            exit;
          end;

         if (not current_module.is_unit) then
           begin
             { finally rewrite all units included into the package }
             uu:=tused_unit(usedunits.first);
             while assigned(uu) do
               begin
                 RewritePPU(uu.u.ppufilename,uu.u.ppufilename);
                 uu:=tused_unit(uu.next);
               end;

             { create the executable when we are at level 1 }
             if (compile_level=1) then
               begin
                 { create global resource file by collecting all resource files }
                 CollectResourceFiles;
                 { write .def file }
                 if (cs_link_deffile in current_settings.globalswitches) then
                   deffile.writefile;
                 { insert all .o files from all loaded units and
                   unload the units, we don't need them anymore.
                   Keep the current_module because that is still needed }
                 hp:=tmodule(loaded_units.first);
                 while assigned(hp) do
                  begin
                    { the package itself contains no code so far }
                    linker.AddModuleFiles(hp);
                    hp2:=tmodule(hp.next);
                    if (hp<>current_module) and
                       (not needsymbolinfo) then
                      begin
                        loaded_units.remove(hp);
                        hp.free;
                      end;
                    hp:=hp2;
                  end;
                 linker.MakeSharedLibrary
               end;

             { Give Fatal with error count for linker errors }
             if (Errorcount>0) and not status.skip_error then
              begin
                Message1(unit_f_errors_in_unit,tostr(Errorcount));
                status.skip_error:=true;
              end;
          end;
      end;


    procedure proc_program(islibrary : boolean);
      var
         main_file : tinputfile;
         hp,hp2    : tmodule;
         finalize_procinfo,
         init_procinfo,
         main_procinfo : tcgprocinfo;
         force_init_final : boolean;
         resources_used : boolean;
         program_name : ansistring;
      begin
         DLLsource:=islibrary;
         Status.IsLibrary:=IsLibrary;
         Status.IsPackage:=false;
         Status.IsExe:=true;
         parse_only:=false;
         main_procinfo:=nil;
         init_procinfo:=nil;
         finalize_procinfo:=nil;
         resources_used:=false;

         { DLL defaults to create reloc info }
         if islibrary then
           begin
             if not RelocSectionSetExplicitly then
               RelocSection:=true;
           end;

         { Relocation works only without stabs under Windows when }
         { external linker (LD) is used.  LD generates relocs for }
         { stab sections which is not loaded in memory. It causes }
         { AV error when DLL is loaded and relocation is needed.  }
         { Internal linker does not have this problem.            }
         if RelocSection and
            (target_info.system in systems_all_windows+[system_i386_wdosx]) and
            (cs_link_extern in current_settings.globalswitches) then
           begin
              include(current_settings.globalswitches,cs_link_strip);
              { Warning stabs info does not work with reloc section !! }
              if (cs_debuginfo in current_settings.moduleswitches) and
                 (target_dbg.id=dbg_stabs) then
                begin
                  Message1(parser_w_parser_reloc_no_debug,current_module.mainsource);
                  Message(parser_w_parser_win32_debug_needs_WN);
                  exclude(current_settings.moduleswitches,cs_debuginfo);
                end;
           end;
         { get correct output names }
         main_file := current_scanner.inputfile;
         while assigned(main_file.next) do
           main_file := main_file.next;

         current_module.SetFileName(main_file.path+main_file.name,true);

         if islibrary then
           begin
              consume(_LIBRARY);
              program_name:=orgpattern;
              consume(_ID);
              while token=_POINT do
                begin
                  consume(_POINT);
                  program_name:=program_name+'.'+orgpattern;
                  consume(_ID);
                end;
              current_module.setmodulename(program_name);
              current_module.islibrary:=true;
              exportlib.preparelib(program_name);

              if tf_library_needs_pic in target_info.flags then
                include(current_settings.moduleswitches,cs_create_pic);

              consume(_SEMICOLON);
           end
         else
           { is there an program head ? }
           if token=_PROGRAM then
            begin
              consume(_PROGRAM);
              program_name:=orgpattern;
              consume(_ID);
              while token=_POINT do
                begin
                  consume(_POINT);
                  program_name:=program_name+'.'+orgpattern;
                  consume(_ID);
                end;
              current_module.setmodulename(program_name);
              if (target_info.system in systems_unit_program_exports) then
                exportlib.preparelib(program_name);
              if token=_LKLAMMER then
                begin
                   consume(_LKLAMMER);
                   repeat
                     consume(_ID);
                   until not try_to_consume(_COMMA);
                   consume(_RKLAMMER);
                end;
              consume(_SEMICOLON);
            end
         else if (target_info.system in systems_unit_program_exports) then
           exportlib.preparelib(current_module.realmodulename^);

         { global switches are read, so further changes aren't allowed }
         current_module.in_global:=false;

         { setup things using the switches }
         setupglobalswitches;

         { set implementation flag }
         current_module.in_interface:=false;
         current_module.interface_compiled:=true;

         { insert after the unit symbol tables the static symbol table }
         { of the program                                             }
         current_module.localsymtable:=tstaticsymtable.create(current_module.modulename^,current_module.moduleid);

         { load standard units (system,objpas,profile unit) }
         loaddefaultunits;

         { Load units provided on the command line }
         loadautounits;

         {Load the units used by the program we compile.}
         if token=_USES then
           loadunits;

         { All units are read, now give them a number }
         current_module.updatemaps;

         {Insert the name of the main program into the symbol table.}
         if current_module.realmodulename^<>'' then
           tabstractunitsymtable(current_module.localsymtable).insertunit(tunitsym.create(current_module.realmodulename^,current_module));

         Message1(parser_u_parsing_implementation,current_module.mainsource);

         symtablestack.push(current_module.localsymtable);

{$ifdef jvm}
         { fake classdef to represent the class corresponding to the unit }
         addmoduleclass;
{$endif}

         { Insert _GLOBAL_OFFSET_TABLE_ symbol if system uses it }
         maybe_load_got;

         { create whole program optimisation information }
         current_module.wpoinfo:=tunitwpoinfo.create;

         { The program intialization needs an alias, so it can be called
           from the bootstrap code.}
         if islibrary then
          begin
            main_procinfo:=create_main_proc(make_mangledname('',current_module.localsymtable,mainaliasname),potype_proginit,current_module.localsymtable);
            { Win32 startup code needs a single name }
            if not(target_info.system in (systems_darwin+systems_aix)) then
              main_procinfo.procdef.aliasnames.insert('PASCALMAIN')
            else
              main_procinfo.procdef.aliasnames.insert(target_info.Cprefix+'PASCALMAIN')
          end
         else if (target_info.system in ([system_i386_netware,system_i386_netwlibc,system_powerpc_macos]+systems_darwin+systems_aix)) then
           begin
             main_procinfo:=create_main_proc('PASCALMAIN',potype_proginit,current_module.localsymtable);
           end
         else
           begin
             main_procinfo:=create_main_proc(mainaliasname,potype_proginit,current_module.localsymtable);
             main_procinfo.procdef.aliasnames.insert('PASCALMAIN');
           end;
         main_procinfo.parse_body;
         { save file pos for debuginfo }
         current_module.mainfilepos:=main_procinfo.entrypos;

         { Generate specializations of objectdefs methods }
         generate_specialization_procs;

         { add implementations for synthetic method declarations added by
           the compiler }
         add_synthetic_method_implementations(current_module.localsymtable);

         { should we force unit initialization? }
         force_init_final:=tstaticsymtable(current_module.localsymtable).needs_init_final;
         if force_init_final or cnodeutils.force_init then
           init_procinfo:=gen_implicit_initfinal(uf_init,current_module.localsymtable);

         { Add symbol to the exports section for win32 so smartlinking a
           DLL will include the edata section }
         if assigned(exportlib) and
            (target_info.system in [system_i386_win32,system_i386_wdosx]) and
            ((current_module.flags and uf_has_exports)<>0) then
           current_asmdata.asmlists[al_procedures].concat(tai_const.createname(make_mangledname('EDATA',current_module.localsymtable,''),0));

         { finalize? }
         if token=_FINALIZATION then
           begin
              { Parse the finalize }
              finalize_procinfo:=create_main_proc(make_mangledname('',current_module.localsymtable,'finalize'),potype_unitfinalize,current_module.localsymtable);
              finalize_procinfo.procdef.aliasnames.insert(make_mangledname('FINALIZE$',current_module.localsymtable,''));
              finalize_procinfo.procdef.aliasnames.insert('PASCALFINALIZE');
              finalize_procinfo.parse_body;
           end
         else
           if force_init_final or cnodeutils.force_final then
             finalize_procinfo:=gen_implicit_initfinal(uf_finalize,current_module.localsymtable);

          { the finalization routine of libraries is generic (and all libraries need to }
          { be finalized, so they can finalize any units they use                       }
          if (islibrary) then
            exportlib.setfininame(current_asmdata.asmlists[al_procedures],'FPC_LIB_EXIT');

         { all labels must be defined before generating code }
         if Errorcount=0 then
           tstoredsymtable(current_module.localsymtable).checklabels;

         { See remark in unit init/final }
         main_procinfo.generate_code;
         main_procinfo.resetprocdef;
         release_main_proc(main_procinfo);
         if assigned(init_procinfo) then
           begin
             { initialization can be implicit only }
             current_module.flags:=current_module.flags or uf_init;
             init_procinfo.code:=cnodeutils.wrap_proc_body(init_procinfo.procdef,init_procinfo.code);
             init_procinfo.generate_code;
             init_procinfo.resetprocdef;
             release_main_proc(init_procinfo);
           end;
         if assigned(finalize_procinfo) then
           begin
             if force_init_final or
                cnodeutils.force_init or
                not(has_no_code(finalize_procinfo.code)) then
               begin
                 finalize_procinfo.code:=cnodeutils.wrap_proc_body(finalize_procinfo.procdef,finalize_procinfo.code);
                 finalize_procinfo.generate_code;
                 current_module.flags:=current_module.flags or uf_finalize;
               end;
             finalize_procinfo.resetprocdef;
             release_main_proc(finalize_procinfo);
           end;

         symtablestack.pop(current_module.localsymtable);

         { consume the last point }
         consume(_POINT);

         { reset wpo flags for all defs }
         reset_all_defs;

         if (Errorcount=0) then
           begin
             { test static symtable }
             tstoredsymtable(current_module.localsymtable).allsymbolsused;
             tstoredsymtable(current_module.localsymtable).allprivatesused;
             tstoredsymtable(current_module.localsymtable).check_forwards;

             current_module.allunitsused;
           end;

         { leave when we got an error }
         if (Errorcount>0) and not status.skip_error then
           begin
             Message1(unit_f_errors_in_unit,tostr(Errorcount));
             status.skip_error:=true;
             exit;
           end;

         { remove all unused units, this happens when units are removed
           from the uses clause in the source and the ppu was already being loaded }
         hp:=tmodule(loaded_units.first);
         while assigned(hp) do
          begin
            hp2:=hp;
            hp:=tmodule(hp.next);
            if hp2.is_unit and
               not assigned(hp2.globalsymtable) then
                begin
                  loaded_units.remove(hp2);
                  unloaded_units.concat(hp2);
                end;
          end;

         { do we need to add the variants unit? }
         maybeloadvariantsunit;

         { Now that everything has been compiled we know if we need resource
           support. If not, remove the unit. }
         resources_used:=MaybeRemoveResUnit;

         linker.initsysinitunitname;
         if target_info.system in systems_internal_sysinit then
         begin
           { add start/halt unit }
           AddUnit(linker.sysinitunit);
         end;

{$ifdef arm}
         { Insert .pdata section for arm-wince.
           It is needed for exception handling. }
         if target_info.system in [system_arm_wince] then
           InsertPData;
{$endif arm}

         cnodeutils.InsertThreadvars;

         { generate rtti/init tables }
         write_persistent_type_info(current_module.localsymtable,false);

         { if an Objective-C module, generate rtti and module info }
         MaybeGenerateObjectiveCImageInfo(nil,current_module.localsymtable);

         { generate wrappers for interfaces }
         gen_intf_wrappers(current_asmdata.asmlists[al_procedures],current_module.localsymtable,false);

         { generate imports }
         if current_module.ImportLibraryList.Count>0 then
           importlib.generatelib;

         { generate debuginfo }
         if (cs_debuginfo in current_settings.moduleswitches) then
           current_debuginfo.inserttypeinfo;

         if islibrary or (target_info.system in systems_unit_program_exports) then
           exportlib.generatelib;

         { Reference all DEBUGINFO sections from the main .fpc section }
         if (cs_debuginfo in current_settings.moduleswitches) then
           current_debuginfo.referencesections(current_asmdata.asmlists[al_procedures]);

         { Resource strings }
         GenerateResourceStrings;

         { Windows widestring needing initialization }
         cnodeutils.InsertWideInits;

         { Resourcestring references (const foo:string=someresourcestring) }
         cnodeutils.InsertResStrInits;

         { insert Tables and StackLength }
         cnodeutils.InsertInitFinalTable;
         cnodeutils.InsertThreadvarTablesTable;
         cnodeutils.InsertResourceTablesTable;
         cnodeutils.InsertWideInitsTablesTable;
         cnodeutils.InsertResStrTablesTable;
         cnodeutils.InsertMemorySizes;

{$ifdef FPC_HAS_SYSTEMS_INTERRUPT_TABLE}
         if target_info.system in systems_interrupt_table then
           InsertInterruptTable;
{$endif FPC_HAS_SYSTEMS_INTERRUPT_TABLE}

         { Insert symbol to resource info }
         cnodeutils.InsertResourceInfo(resources_used);

         { create callframe info }
         create_dwarf_frame;

         { insert own objectfile }
         insertobjectfile;

         { assemble and link }
         create_objectfile;

         { We might need the symbols info if not using
           the default do_extractsymbolinfo
           which is a dummy function PM }
         needsymbolinfo:=
           (do_extractsymbolinfo<>@def_extractsymbolinfo) or
           ((current_settings.genwpoptimizerswitches*WPOptimizationsNeedingAllUnitInfo)<>[]);

         { release all local symtables that are not needed anymore }
         if (not needsymbolinfo) then
           free_localsymtables(current_module.localsymtable);

         { leave when we got an error }
         if (Errorcount>0) and not status.skip_error then
          begin
            Message1(unit_f_errors_in_unit,tostr(Errorcount));
            status.skip_error:=true;
            exit;
          end;

         if (not current_module.is_unit) then
           begin
             { create the executable when we are at level 1 }
             if (compile_level=1) then
               begin
                 { create global resource file by collecting all resource files }
                 CollectResourceFiles;
                 { write .def file }
                 if (cs_link_deffile in current_settings.globalswitches) then
                  deffile.writefile;
                 { insert all .o files from all loaded units and
                   unload the units, we don't need them anymore.
                   Keep the current_module because that is still needed }
                 hp:=tmodule(loaded_units.first);
                 while assigned(hp) do
                  begin
                    linker.AddModuleFiles(hp);
                    hp2:=tmodule(hp.next);
                    if (hp<>current_module) and
                       (not needsymbolinfo) then
                      begin
                        loaded_units.remove(hp);
                        hp.free;
                      end;
                    hp:=hp2;
                  end;
                 { free also unneeded units we didn't free before }
                 if not needsymbolinfo then
                   unloaded_units.Clear;
                 { finally we can create a executable }
                 if DLLSource then
                   linker.MakeSharedLibrary
                 else
                   linker.MakeExecutable;

                 { collect all necessary information for whole-program optimization }
                 wpoinfomanager.extractwpoinfofromprogram;
               end;


             { Give Fatal with error count for linker errors }
             if (Errorcount>0) and not status.skip_error then
              begin
                Message1(unit_f_errors_in_unit,tostr(Errorcount));
                status.skip_error:=true;
              end;
          end;
      end;

end.
