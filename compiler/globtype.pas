{
    Copyright (c) 1998-2002 by Florian Klaempfl, Pierre Muller

    Global types

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
unit globtype;

{$i fpcdefs.inc}

interface

    const
       maxidlen = 127;

    type
       { TCmdStr is used to pass command line parameters to an external program to be
         executed from the FPC application. In some circomstances, this can be more
         than 255 characters. That's why using Ansi Strings}
       TCmdStr = AnsiString;
       TPathStr = AnsiString;

{$ifdef symansistr}
       TSymStr = AnsiString;
{$else symansistr}
       TSymStr = ShortString;
{$endif symansistr}
       PSymStr = ^TSymStr;

       { Integer type corresponding to pointer size }
{$ifdef cpu64bitaddr}
       PUint = qword;
       PInt = int64;
{$endif cpu64bitaddr}
{$ifdef cpu32bitaddr}
       PUint = cardinal;
       PInt = longint;
{$endif cpu32bitaddr}
{$ifdef cpu16bitaddr}
       PUint = word;
       PInt = Smallint;
{$endif cpu16bitaddr}

       { Natural integer register type and size for the target machine }
{$ifdef cpu64bitalu}
       AWord = qword;
       AInt = Int64;

     Const
       AIntBits = 64;
{$endif cpu64bitalu}
{$ifdef cpu32bitalu}
       AWord = longword;
       AInt = longint;

     Const
       AIntBits = 32;
{$endif cpu32bitalu}
{$ifdef cpu16bitalu}
       AWord = Word;
       AInt = Smallint;

     Const
       AIntBits = 16;
{$endif cpu16bitalu}
{$ifdef cpu8bitalu}
       AWord = Byte;
       AInt = Shortint;

     Const
       AIntBits = 8;
{$endif cpu8bitalu}

     Type
       PAWord = ^AWord;
       PAInt = ^AInt;

       { target cpu specific type used to store data sizes }
       ASizeInt = PInt;
       ASizeUInt = PUInt;

       { type used for handling constants etc. in the code generator }
       TCGInt = Int64;

       { This must be an ordinal type with the same size as a pointer
         Note: Must be unsigned! Otherwise, ugly code like
         pointer(-1) will result in a pointer with the value
         $fffffffffffffff on a 32bit machine if the compiler uses
         int64 constants internally (JM) }
       TConstPtrUInt = AWord;

       { Use a variant record to be sure that the array if aligned correctly }
       tdoublerec=record
         case byte of
           0 : (bytes:array[0..7] of byte);
           1 : (value:double);
       end;
       textendedrec=record
         case byte of
           0 : (bytes:array[0..9] of byte);
           1 : (value:extended);
       end;

       pconstset = ^tconstset;
       tconstset = set of 0..255;

       { Switches which can be changed locally }
       tlocalswitch = (cs_localnone,
         { codegen }
         cs_check_overflow,cs_check_range,cs_check_object,
         cs_check_io,cs_check_stack,
         cs_checkpointer,cs_check_ordinal_size,
         cs_generate_stackframes,cs_do_assertion,cs_generate_rtti,
         cs_full_boolean_eval,cs_typed_const_writable,cs_allow_enum_calc,
         cs_do_inline,cs_fpu_fwait,cs_ieee_errors,
         cs_check_low_addr_load,
         { mmx }
         cs_mmx,cs_mmx_saturation,
         { parser }
         cs_typed_addresses,cs_strict_var_strings,cs_refcountedstrings,
         cs_bitpacking,cs_varpropsetter,cs_scopedenums,cs_pointermath,
         { macpas specific}
         cs_external_var, cs_externally_visible,
         { jvm specific }
         cs_check_var_copyout
       );
       tlocalswitches = set of tlocalswitch;

       { Switches which can be changed only at the beginning of a new module }
       tmoduleswitch = (cs_modulenone,
         { parser }
         cs_fp_emulation,cs_extsyntax,cs_openstring,
         { support }
         cs_support_goto,cs_support_macro,
         cs_support_c_operators,
         { generation }
         cs_profile,cs_debuginfo,cs_compilesystem,
         cs_lineinfo,cs_implicit_exceptions,cs_explicit_codepage,
         { linking }
         cs_create_smart,cs_create_dynamic,cs_create_pic,
         { browser switches are back }
         cs_browser,cs_local_browser,
         { target specific }
         cs_executable_stack
       );
       tmoduleswitches = set of tmoduleswitch;

       { Switches which can be changed only for a whole program/compilation,
         mostly set with commandline }
       tglobalswitch = (cs_globalnone,
         { parameter switches }
         cs_check_unit_name,cs_constructor_name,cs_support_exceptions,
         cs_support_c_objectivepas,
         { units }
         cs_load_objpas_unit,
         cs_load_gpc_unit,
         cs_load_fpcylix_unit,
         cs_support_vectors,
         { debuginfo }
         cs_use_heaptrc,cs_use_lineinfo,
         cs_gdb_valgrind,cs_no_regalloc,cs_stabs_preservecase,
         { assembling }
         cs_asm_leave,cs_asm_extern,cs_asm_pipe,cs_asm_source,
         cs_asm_regalloc,cs_asm_tempalloc,cs_asm_nodes,
         { linking }
         cs_link_nolink,cs_link_static,cs_link_smart,cs_link_shared,cs_link_deffile,
         cs_link_strip,cs_link_staticflag,cs_link_on_target,cs_link_extern,cs_link_opt_vtable,
         cs_link_opt_used_sections,cs_link_separate_dbg_file,
         cs_link_map,cs_link_pthread,cs_link_no_default_lib_order,
	 cs_link_native
       );
       tglobalswitches = set of tglobalswitch;

       { global switches specific to debug information }
       tdebugswitch = (ds_none,
          { enable set support in dwarf debug info, breaks gdb versions }
          { without support for that tag (they refuse to parse the rest }
          { of the debug information)                                   }
          ds_dwarf_sets,
          { use absolute paths for include files in stabs. Pro: gdb     }
          { always knows full path to file. Con: doesn't work anymore   }
          { if the include file is moved (otherwise, things still work  }
          { if your source hierarchy is the same, but has a different   }
          { base path)                                                  }
          ds_stabs_abs_include_files,
          { prefix method names by "classname__" in DWARF (like is done }
          { for Stabs); not enabled by default, because otherwise once  }
          { support for calling methods has been added to gdb, you'd    }
          { always have to type classinstance.classname__methodname()   }
          ds_dwarf_method_class_prefix
       );
       tdebugswitches = set of tdebugswitch;

       { global target-specific switches }
       ttargetswitch = (ts_none,
         { generate code that results in smaller TOCs than normal (AIX) }
         ts_small_toc,
         { for the JVM target: generate integer array initializations via string
           constants in order to reduce the generated code size (Java routines
           are limited to 64kb of bytecode) }
         ts_compact_int_array_init
       );
       ttargetswitches = set of ttargetswitch;


       { adding a new entry here requires also adding the appropriate define in
         systemh.inc (FK)
       }
       tfeature = (
         f_heap,f_init_final,f_rtti,f_classes,f_exceptions,f_exitcode,
         f_ansistrings,f_widestrings,f_textio,f_consoleio,f_fileio,
         f_random,f_variants,f_objects,f_dynarrays,f_threading,f_commandargs,
         f_processes,f_stackcheck,f_dynlibs,f_softfpu,f_objectivec1,f_resources
       );
       tfeatures = set of tfeature;

     type
       { optimizer }
       toptimizerswitch = (cs_opt_none,
         cs_opt_level1,cs_opt_level2,cs_opt_level3,
         cs_opt_regvar,cs_opt_uncertain,cs_opt_size,cs_opt_stackframe,
         cs_opt_peephole,cs_opt_asmcse,cs_opt_loopunroll,cs_opt_tailrecursion,cs_opt_nodecse,
         cs_opt_nodedfa,cs_opt_loopstrength,cs_opt_scheduler,cs_opt_autoinline
       );
       toptimizerswitches = set of toptimizerswitch;

       { whole program optimizer }
       twpoptimizerswitch = (
         cs_wpo_devirtualize_calls,cs_wpo_optimize_vmts,
         cs_wpo_symbol_liveness
       );
       twpoptimizerswitches = set of twpoptimizerswitch;

    type
       { Used by ARM / AVR to differentiate between specific microcontrollers }
       tcontrollerdatatype = record
          controllertypestr, controllerunitstr: string[20];
          interruptvectors:integer;
          flashbase, flashsize, srambase, sramsize, eeprombase, eepromsize: dword;
       end;

    const
       OptimizerSwitchStr : array[toptimizerswitch] of string[10] = ('',
         'LEVEL1','LEVEL2','LEVEL3',
         'REGVAR','UNCERTAIN','SIZE','STACKFRAME',
         'PEEPHOLE','ASMCSE','LOOPUNROLL','TAILREC','CSE',
         'DFA','STRENGTH','SCHEDULE','AUTOINLINE'
       );
       WPOptimizerSwitchStr : array [twpoptimizerswitch] of string[14] = (
         'DEVIRTCALLS','OPTVMTS','SYMBOLLIVENESS'
       );

       DebugSwitchStr : array[tdebugswitch] of string[22] = ('',
         'DWARFSETS','STABSABSINCLUDES','DWARFMETHODCLASSPREFIX');

       TargetSwitchStr : array[ttargetswitch] of string[19] = ('',
         'SMALLTOC',
         'COMPACTINTARRAYINIT');

       { switches being applied to all CPUs at the given level }
       genericlevel1optimizerswitches = [cs_opt_level1];
       genericlevel2optimizerswitches = [cs_opt_level2];
       genericlevel3optimizerswitches = [cs_opt_level3];

       { whole program optimizations whose information generation requires
         information from all loaded units
       }
       WPOptimizationsNeedingAllUnitInfo = [cs_wpo_devirtualize_calls,cs_wpo_optimize_vmts];

       featurestr : array[tfeature] of string[12] = (
         'HEAP','INITFINAL','RTTI','CLASSES','EXCEPTIONS','EXITCODE',
         'ANSISTRINGS','WIDESTRINGS','TEXTIO','CONSOLEIO','FILEIO',
         'RANDOM','VARIANTS','OBJECTS','DYNARRAYS','THREADING','COMMANDARGS',
         'PROCESSES','STACKCHECK','DYNLIBS','SOFTFPU','OBJECTIVEC1','RESOURCES'
       );

    type
       { Switches which can be changed by a mode (fpc,tp7,delphi) }
       tmodeswitch = (m_none,m_all, { needed for keyword }
         { generic }
         m_fpc,m_objfpc,m_delphi,m_tp7,m_mac,m_iso,
         {$ifdef fpc_mode}m_gpc,{$endif}
         { more specific }
         m_class,               { delphi class model }
         m_objpas,              { load objpas unit }
         m_result,              { result in functions }
         m_string_pchar,        { pchar 2 string conversion }
         m_cvar_support,        { cvar variable directive }
         m_nested_comment,      { nested comments }
         m_tp_procvar,          { tp style procvars (no @ needed) }
         m_mac_procvar,         { macpas style procvars }
         m_repeat_forward,      { repeating forward declarations is needed }
         m_pointer_2_procedure, { allows the assignement of pointers to
                                  procedure variables                     }
         m_autoderef,           { does auto dereferencing of struct. vars }
         m_initfinal,           { initialization/finalization for units }
         m_default_ansistring,  { ansistring turned on by default }
         m_out,                 { support the calling convention OUT }
         m_default_para,        { support default parameters }
         m_hintdirective,       { support hint directives }
         m_duplicate_names,     { allow locals/paras to have duplicate names of globals }
         m_property,            { allow properties }
         m_default_inline,      { allow inline proc directive }
         m_except,              { allow exception-related keywords }
         m_objectivec1,         { support interfacing with Objective-C (1.0) }
         m_objectivec2,         { support interfacing with Objective-C (2.0) }
         m_nested_procvars,     { support nested procedural variables }
         m_non_local_goto,      { support non local gotos (like iso pascal) }
         m_advanced_records,    { advanced record syntax with visibility sections, methods and properties }
         m_isolike_unary_minus, { unary minus like in iso pascal: same precedence level as binary minus/plus }
         m_systemcodepage,      { use system codepage as compiler codepage by default, emit ansistrings with system codepage }
         m_final_fields,        {�allows declaring fields as "final", which means they must be initialised
                                  in the (class) constructor and are constant from then on (same as final
                                  fields in Java) }
         m_default_unicodestring {�makes the default string type in $h+ mode unicodestring rather than
                                   ansistring; similarly, char becomes unicodechar rather than ansichar }
       );
       tmodeswitches = set of tmodeswitch;

       { Win32, OS/2 & MacOS application types }
       tapptype = (
         app_none,
         app_native,
         app_gui,       { graphic user-interface application}
         app_cui,       { console application}
         app_fs,        { full-screen type application (OS/2 and EMX only) }
         app_tool,      { tool application, (MPW tool for MacOS, MacOS only)}
         app_arm7,
         app_arm9,
         app_bundle     { dynamically loadable bundle, Darwin only }
       );

       { interface types }
       tinterfacetypes = (
         it_interfacecom,
         it_interfacecorba,
         it_interfacejava
       );

       { currently parsed block type }
       tblock_type = (
         bt_none,        { not assigned                              }
         bt_general,     { default                                   }
         bt_type,        { type section                              }
         bt_const,       { const section                             }
         bt_const_type,  { const part of type. e.g.: ": Integer = 1" }
         bt_var,         { variable declaration                      }
         bt_var_type,    { type of variable                          }
         bt_except,      { except section                            }
         bt_body         { procedure body                            }
       );

       { Temp types }
       ttemptype = (tt_none,
                    { free temp location, can be reused for something else }
                    tt_free,
                    { temp location that will be freed when ttgobj.UnGetTemp/
                      ttgobj.UnGetIfTemp is called on it }
                    tt_normal,
                    { temp location that will not be freed; if it has to be
                      freed, first ttgobj.changetemptype() it to tt_normal,
                      or call ttgobj.UnGetLocal() instead (for local variables,
                      since they are also persistent temps) }
                    tt_persistent,
                    { temp location that can never be reused anymore, even
                      after it has been freed }
                    tt_noreuse,
                    { freed version of the above }
                    tt_freenoreuse,
                    { temp location that has been allocated by the register
                      allocator and that can be reallocated only by the
                      register allocator }
                    tt_regallocator,
                    { freed version of the above }
                    tt_freeregallocator);
       ttemptypeset = set of ttemptype;

       { calling convention for tprocdef and tprocvardef }
       tproccalloption=(pocall_none,
         { procedure uses C styled calling }
         pocall_cdecl,
         { C++ calling conventions }
         pocall_cppdecl,
         { Far16 for OS/2 }
         pocall_far16,
         { Old style FPC default calling }
         pocall_oldfpccall,
         { Procedure has compiler magic}
         pocall_internproc,
         { procedure is a system call, applies e.g. to MorphOS and PalmOS }
         pocall_syscall,
         { pascal standard left to right }
         pocall_pascal,
         { procedure uses register (fastcall) calling }
         pocall_register,
         { safe call calling conventions }
         pocall_safecall,
         { procedure uses stdcall call }
         pocall_stdcall,
         { Special calling convention for cpus without a floating point
           unit. Floating point numbers are passed in integer registers
           instead of floating point registers. Depending on the other
           available calling conventions available for the cpu
           this replaces either pocall_fastcall or pocall_stdcall.
         }
         pocall_softfloat,
         { Metrowerks Pascal. Special case on Mac OS (X): passes all }
         { constant records by reference.                            }
         pocall_mwpascal,
         { Special interrupt handler for embedded systems }
         pocall_interrupt
       );
       tproccalloptions = set of tproccalloption;

     const
       proccalloptionStr : array[tproccalloption] of string[14]=('',
           'CDecl',
           'CPPDecl',
           'Far16',
           'OldFPCCall',
           'InternProc',
           'SysCall',
           'Pascal',
           'Register',
           'SafeCall',
           'StdCall',
           'SoftFloat',
           'MWPascal',
           'Interrupt'
         );

       { Default calling convention }
{$ifdef x86}
       pocall_default = pocall_register;
{$else}
       pocall_default = pocall_stdcall;
{$endif}

       modeswitchstr : array[tmodeswitch] of string[18] = ('','',
         '','','','','','',
         {$ifdef fpc_mode}'',{$endif}
         { more specific }
         'CLASS',
         'OBJPAS',
         'RESULT',
         'PCHARTOSTRING',
         'CVAR',
         'NESTEDCOMMENTS',
         'CLASSICPROCVARS',
         'MACPROCVARS',
         'REPEATFORWARD',
         'POINTERTOPROCVAR',
         'AUTODEREF',
         'INITFINAL',
         'ANSISTRINGS',
         'OUT',
         'DEFAULTPARAMETERS',
         'HINTDIRECTIVE',
         'DUPLICATELOCALS',
         'PROPERTIES',
         'ALLOWINLINE',
         'EXCEPTIONS',
         'OBJECTIVEC1',
         'OBJECTIVEC2',
         'NESTEDPROCVARS',
         'NONLOCALGOTO',
         'ADVANCEDRECORDS',
         'ISOUNARYMINUS',
         'SYSTEMCODEPAGE',
         'FINALFIELDS',
         'UNICODESTRINGS');


     type
       tprocinfoflag=(
         { procedure has at least one assembler block }
         pi_has_assembler_block,
         { procedure does a call }
         pi_do_call,
         { procedure has a try statement = no register optimization }
         pi_uses_exceptions,
         { procedure is declared as @var(assembler), don't optimize}
         pi_is_assembler,
         { procedure contains data which needs to be finalized }
         pi_needs_implicit_finally,
         { procedure has the implicit try..finally generated }
         pi_has_implicit_finally,
         { procedure uses fpu}
         pi_uses_fpu,
         { procedure uses GOT for PIC code }
         pi_needs_got,
         { references var/proc/type/const in static symtable,
           i.e. not allowed for inlining from other units }
         pi_uses_static_symtable,
         { set if the procedure has to push parameters onto the stack }
         pi_has_stackparameter,
         { set if the procedure has at least one label }
         pi_has_label,
         { calls itself recursive }
         pi_is_recursive,
         { stack frame optimization not possible (only on x86 probably) }
         pi_needs_stackframe,
         { set if the procedure has at least one register saved on the stack }
         pi_has_saved_regs,
         { dfa was generated for this proc }
         pi_dfaavailable,
         { subroutine contains interprocedural used labels }
         pi_has_interproclabel,
         { subroutine has unwind info (win64) }
         pi_has_unwind_info,
         { subroutine contains interprocedural gotos }
         pi_has_global_goto,
         { subroutine contains inherited call }
         pi_has_inherited
       );
       tprocinfoflags=set of tprocinfoflag;

    type
      { float types -- warning, this enum/order is used internally by the RTL
        as well in rtl/inc/real2str.inc }
      tfloattype = (
        s32real,s64real,s80real,sc80real { the C "long double" type on x86 },
        s64comp,s64currency,s128real
      );

    type
      { register allocator live range extension direction }
      TRADirection = (rad_forward, rad_backwards, rad_backwards_reinit);

    type
      TIDString = string[maxidlen];

      tnormalset = set of byte; { 256 elements set }
      pnormalset = ^tnormalset;

      pboolean   = ^boolean;
      pdouble    = ^double;
      pbyte      = ^byte;
      pword      = ^word;
      plongint   = ^longint;
      plongintarray = plongint;

      pfileposinfo = ^tfileposinfo;
      tfileposinfo = record
        { if types of column or fileindex are changed, modify tcompilerppufile.putposinfo }
        line      : longint;
        column    : word;
        fileindex : word;
        moduleindex : word;
      end;

  {$ifndef xFPC}
    type
      pguid = ^tguid;
      tguid = packed record
        D1: LongWord;
        D2: Word;
        D3: Word;
        D4: array[0..7] of Byte;
      end;
  {$endif}

       tstringencoding = Word;
       tcodepagestring = string[20];

    const
       { link options }
       link_none    = $0;
       link_always  = $1;
       link_static  = $2;
       link_smart   = $4;
       link_shared  = $8;

    type
      { a message state }
      tmsgstate = (
        ms_on := 1,
        ms_off := 2,
        ms_error := 3,

        ms_on_global := $11,    // turn on output
        ms_off_global := $22,   // turn off output
        ms_error_global := $33  // cast to error
      );
    const
      { Mask for current value of message state }
      ms_local_mask = $0f;
      { Mask for global value of message state
        that needs to be restored when changing units }
      ms_global_mask = $f0;
      { Shift used to convert global to local message state }
      ms_shift = 4;

    type
      pmessagestaterecord = ^tmessagestaterecord;
      tmessagestaterecord = record
        next : pmessagestaterecord;
        value : longint;
        state : tmsgstate;
      end;


  { hide Sysutils.ExecuteProcess in units using this one after SysUtils}
  const
    ExecuteProcess = 'Do not use' deprecated 'Use cfileutil.RequotedExecuteProcess instead, ExecuteProcess cannot deal with single quotes as used by Unix command lines';

implementation

end.
