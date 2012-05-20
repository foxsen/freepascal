{
    Copyright (c) 1998-2002 by Florian Klaempfl, Pierre Muller

    Symbol table constants

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
unit symconst;

{$i fpcdefs.inc}

interface

uses
  globtype;

const
  def_alignment     = 4;

  C_alignment       = -1;
  bit_alignment     = -2;
  mac68k_alignment  = -3;

  { if you change one of the following contants, }
  { you have also to change the typinfo unit}
  { and the rtl/i386,template/rttip.inc files    }
  tkUnknown  = 0;
  tkInteger  = 1;
  tkChar     = 2;
  tkEnumeration   = 3;
  tkFloat    = 4;
  tkSet      = 5;
  tkMethod   = 6;
  tkSString  = 7;
  tkString   = tkSString;
  tkLString  = 8;
  tkAString  = 9;
  tkWString  = 10;
  tkVariant  = 11;
  tkArray    = 12;
  tkRecord   = 13;
  tkInterface= 14;
  tkClass    = 15;
  tkObject   = 16;
  tkWChar    = 17;
  tkBool     = 18;
  tkInt64    = 19;
  tkQWord    = 20;
  tkDynArray = 21;
  tkInterfaceCorba = 22;
  tkProcVar  = 23;
  tkUString  = 24;
  tkUChar    = 25;
  tkHelper   = 26;
  tkFile     = 27;

  otSByte     = 0;
  otUByte     = 1;
  otSWord     = 2;
  otUWord     = 3;
  otSLong     = 4;
  otULong     = 5;
  otSLongLong = 6;
  otULongLong = 7;

  ftSingle   = 0;
  ftDouble   = 1;
  ftExtended = 2;
  ftComp     = 3;
  ftCurr     = 4;
  ftFloat128 = 5;

  mkProcedure        = 0;
  mkFunction         = 1;
  mkConstructor      = 2;
  mkDestructor       = 3;
  mkClassProcedure   = 4;
  mkClassFunction    = 5;
  mkClassConstructor = 6;
  mkClassDestructor  = 7;
  mkOperatorOverload = 8;
// delphi has the next too:
//mkSafeProcedure    = 9;
//mkSafeFunction     = 10;

  pfvar      = 1;
  pfConst    = 2;
  pfArray    = 4;
  pfAddress  = 8;
  pfReference= 16;
  pfOut      = 32;
  pfConstRef = 64;

  unknown_level         = 0;
  main_program_level    = 1;
  normal_function_level = 2;

  { implicit parameter positions, normal parameters start at 10
    and will increase with 10 for each parameter. The high parameters
    will be inserted with n+1 }
  paranr_parentfp = 1;
  paranr_parentfp_delphi_cc_leftright = 1;
  paranr_self = 2;
  paranr_result = 3;
  paranr_vmt = 4;

  { the implicit parameters for Objective-C methods need to come
    after the hidden result parameter }
  paranr_objc_self = 4;
  paranr_objc_cmd = 5;
  { Required to support variations of syscalls on MorphOS }
  paranr_syscall_basesysv    = 9;
  paranr_syscall_sysvbase    = high(word)-5;
  paranr_syscall_r12base     = high(word)-4;
  paranr_syscall_legacy      = high(word)-3;
  paranr_result_leftright    = high(word)-2;
  paranr_parentfp_delphi_cc  = high(word)-1;

  { prefix for names of class helper procsyms added to regular symtables }
  class_helper_prefix = 'CH$';


type
  { keep this in sync with TIntfFlag in rtl/objpas/typinfo.pp }
  TCompilerIntfFlag = (ifHasGuid,ifDispInterface,ifDispatch,ifHasStrGUID);

  { Deref entry options }
  tdereftype = (deref_nil,
    deref_unit,
    deref_symid,
    deref_defid
  );

  { symbol visibility }
  tvisibility=(
    vis_hidden,
    vis_strictprivate,
    vis_private,
    vis_strictprotected,
    vis_protected,
    vis_public,
    vis_published,
    vis_none
  );

  { symbol options }
  tsymoption=(sp_none,
    sp_static,              { static symbol in class/object/record }
    sp_hint_deprecated,
    sp_hint_platform,
    sp_hint_library,
    sp_hint_unimplemented,
    sp_has_overloaded,
    sp_internal,            { internal symbol, not reported as unused }
    sp_implicitrename,
    sp_hint_experimental,
    sp_generic_para,
    sp_has_deprecated_msg,
    sp_generic_dummy,       { this is used for symbols that are generated when a
                              generic is encountered to ease inline
                              specializations, etc; those symbols can be
                              "overridden" with a completely different symbol }
    sp_explicitrename       { this is used to keep track of type renames created
                              by the user }
  );
  tsymoptions=set of tsymoption;

  { flags for a definition }
  tdefoption=(df_none,
    { type is unique, i.e. declared with type = type <tdef>; }
    df_unique,
    { type is a generic }
    df_generic,
    { type is a specialization of a generic type }
    df_specialization,
    { def has been copied from another def so symtable is not owned }
    df_copied_def
  );
  tdefoptions=set of tdefoption;

  tdefstate=(ds_none,
    ds_vmt_written,
    ds_rtti_table_used,
    ds_init_table_used,
    ds_rtti_table_written,
    ds_init_table_written,
    ds_dwarf_dbg_info_used,
    ds_dwarf_dbg_info_written
  );
  tdefstates=set of tdefstate;

  { tsymlist entry types }
  tsltype = (sl_none,
    sl_load,
    sl_call,
    sl_subscript,
    sl_vec,
    sl_typeconv,
    sl_absolutetype
  );

  { base types for orddef }
  tordtype = (
    uvoid,
    u8bit,u16bit,u32bit,u64bit,
    s8bit,s16bit,s32bit,s64bit,
    pasbool8,pasbool16,pasbool32,pasbool64,
    bool8bit,bool16bit,bool32bit,bool64bit,
    uchar,uwidechar,scurrency
  );

  { string types }
  tstringtype = (
    st_shortstring,
    st_longstring,
    st_ansistring,
    st_widestring,
    st_unicodestring
  );

  tvarianttype = (
    vt_normalvariant,vt_olevariant
  );

  tcallercallee = (callnoside,callerside,calleeside,callbothsides);

  { basic type for tprocdef and tprocvardef }
  tproctypeoption=(potype_none,
    potype_proginit,     { Program initialization }
    potype_unitinit,     { unit initialization }
    potype_unitfinalize, { unit finalization }
    potype_constructor,  { Procedure is a constructor }
    potype_destructor,   { Procedure is a destructor }
    potype_operator,     { Procedure defines an operator }
    potype_procedure,
    potype_function,
    potype_class_constructor, { class constructor }
    potype_class_destructor,  { class destructor  }
    potype_propgetter,        { Dispinterface property accessors }
    potype_propsetter,
    potype_exceptfilter       { SEH exception filter or termination handler }
  );
  tproctypeoptions=set of tproctypeoption;

  { other options for tprocdef and tprocvardef }
  tprocoption=(po_none,
    po_classmethod,       { class method }
    po_virtualmethod,     { Procedure is a virtual method }
    po_abstractmethod,    { Procedure is an abstract method }
    po_finalmethod,       { Procedure is a final method }
    po_staticmethod,      { static method }
    po_overridingmethod,  { method with override directive }
    po_methodpointer,     { method pointer, only in procvardef, also used for 'with object do' }
    po_interrupt,         { Procedure is an interrupt handler }
    po_iocheck,           { IO checking should be done after a call to the procedure }
    po_assembler,         { Procedure is written in assembler }
    po_msgstr,            { method for string message handling }
    po_msgint,            { method for int message handling }
    po_exports,           { Procedure has export directive (needed for OS/2) }
    po_external,          { Procedure is external (in other object or lib)}
    po_overload,          { procedure is declared with overload directive }
    po_varargs,           { printf like arguments }
    po_internconst,       { procedure has constant evaluator intern }
    { flag that only the address of a method is returned and not a full methodpointer }
    po_addressonly,
    { procedure is exported }
    po_public,
    { calling convention is specified explicitly }
    po_hascallingconvention,
    { reintroduce flag }
    po_reintroduce,
    { location of parameters is given explicitly as it is necessary for some syscall
      conventions like that one of MorphOS }
    po_explicitparaloc,
    { no stackframe will be generated, used by lowlevel assembler like get_frame }
    po_nostackframe,
    po_has_mangledname,
    po_has_public_name,
    po_forward,
    po_global,
    po_has_inlininginfo,
    { The different kind of syscalls on MorphOS }
    po_syscall_legacy,
    po_syscall_sysv,
    po_syscall_basesysv,
    po_syscall_sysvbase,
    po_syscall_r12base,
    { Procedure can be inlined }
    po_inline,
    { Procedure is used for internal compiler calls }
    po_compilerproc,
    { importing }
    po_has_importdll,
    po_has_importname,
    po_kylixlocal,
    po_dispid,
    { weakly linked (i.e., may or may not exist at run time) }
    po_weakexternal,
    { Objective-C method }
    po_objc,
    { enumerator support }
    po_enumerator_movenext,
    { optional Objective-C protocol method }
    po_optional,
    { nested procedure that uses Delphi-style calling convention for passing
      the frame pointer (pushed on the stack, always the last parameter,
      removed by the caller). Required for nested procvar compatibility,
      because such procvars can hold both regular and nested procedures
      (when calling a regular procedure using the above convention, it will
       simply not see the frame pointer parameter, and since the caller cleans
       up the stack will also remain balanced) }
    po_delphi_nested_cc,
    { allows the routine's RawByteString var/out parameters to accept parameters
      that do not match exactly (without typeconversion) }
    po_rtlproc,
    { Non-virtual method of a Java class that has been transformed into a
      "virtual; final;" method for JVM-implementation reasons }
    po_java_nonvirtual,
    { automatically inherited routine from parent class, ignore for resolving
      overloads (on the JVM target, constructors are not automatically
      inherited, so we explicitly have to add the constructors of the parent
      class to the child class; this influences the overload resolution logic
      though, so ignore them there) }
    po_ignore_for_overload_resolution
  );
  tprocoptions=set of tprocoption;

  { options for objects and classes }
  tobjecttyp = (odt_none,
    odt_class,
    odt_object,
    odt_interfacecom,
    odt_interfacecom_property,
    odt_interfacecom_function,
    odt_interfacecorba,
    odt_cppclass,
    odt_dispinterface,
    odt_objcclass,
    odt_objcprotocol,
    odt_objccategory, { note that these are changed into odt_class afterwards }
    odt_helper,
    odt_javaclass,
    odt_interfacejava
  );

  { defines the type of the extended "structure"; only used for parsing }
  thelpertype=(ht_none,
    ht_class,
    ht_record
  );

  { Variations in interfaces implementation }
  { Beware, this data is duplicated in the compiler and rtl. }
  { Do not change the order of the fields. }
  tinterfaceentrytype = (etStandard,
    etVirtualMethodResult,
    etStaticMethodResult,
    etFieldValue,
    etVirtualMethodClass,
    etStaticMethodClass,
    etFieldValueClass
  );

  { options for objects and classes }
  tobjectoption=(oo_none,
    oo_is_forward,         { the class is only a forward declared yet }
    oo_is_abstract,        { the class is abstract - only descendants can be used }
    oo_is_sealed,          { the class is sealed - can't have descendants }
    oo_has_virtual,        { the object/class has virtual methods }
    oo_has_private,
    oo_has_protected,
    oo_has_strictprivate,
    oo_has_strictprotected,
    oo_has_constructor,    { the object/class has a constructor }
    oo_has_destructor,     { the object/class has a destructor }
    oo_has_vmt,            { the object/class has a vmt }
    oo_has_msgstr,
    oo_has_msgint,
    oo_can_have_published,{ the class has rtti, i.e. you can publish properties }
    oo_has_default_property,
    oo_has_valid_guid,
    oo_has_enumerator_movenext,
    oo_has_enumerator_current,
    oo_is_external,       { the class is externally implemented (objcclass, cppclass) }
    oo_is_formal,         { the class is only formally defined in this module (x = objcclass; external [name 'x'];) }
    oo_is_classhelper,    { objcclasses that represent categories, and Delpi-style class helpers, are marked like this }
    oo_has_class_constructor, { the object/class has a class constructor }
    oo_has_class_destructor,  { the object/class has a class destructor  }
    oo_is_enum_class,     { the class represents an enum (JVM) }
    oo_has_new_destructor { the object/class declares a destructor (apart from potentially inherting one from the parent) }
  );
  tobjectoptions=set of tobjectoption;

  tarraydefoption=(ado_none,
    ado_IsConvertedPointer,
    ado_IsDynamicArray,
    ado_IsVariant,
    ado_IsConstructor,
    ado_IsArrayOfConst,
    ado_IsConstString,
    ado_IsBitPacked
  );
  tarraydefoptions=set of tarraydefoption;

  { options for properties }
  tpropertyoption=(ppo_none,
    ppo_indexed,                  { delcared wwith "index" keyword }
    ppo_defaultproperty,
    ppo_stored,
    ppo_hasparameters,            { has parameters: prop[param1, param2: type] }
    ppo_implements,
    ppo_enumerator_current,       { implements current property for enumerator }
    ppo_overrides,                { overrides ancestor property }
    ppo_dispid_write              { no longer used }
  );
  tpropertyoptions=set of tpropertyoption;

  { options for variables }
  tvaroption=(vo_none,
    vo_is_external,
    vo_is_dll_var,
    vo_is_thread_var,
    vo_has_local_copy,
    vo_is_const,  { variable is declared as const (parameter) and can't be written to }
    vo_is_public,
    vo_is_high_para,
    vo_is_funcret,
    vo_is_self,
    vo_is_vmt,
    vo_is_result,  { special result variable }
    vo_is_parentfp,
    vo_is_loop_counter, { used to detect assignments to loop counter }
    vo_is_hidden_para,
    vo_has_explicit_paraloc,
    vo_is_syscall_lib,
    vo_has_mangledname,
    vo_is_typed_const,
    vo_is_range_check,
    vo_is_overflow_check,
    vo_is_typinfo_para,
    vo_is_weak_external,
    { Objective-C message selector parameter }
    vo_is_msgsel,
    { first field of variant part of a record }
    vo_is_first_field,
    vo_volatile,
    vo_has_section,
    { variable contains a winlike WideString which should be finalized
      even in $J- state }
    vo_force_finalize,
    { this is an internal variable that is used for Default() intrinsic in code
      sections }
    vo_is_default_var
  );
  tvaroptions=set of tvaroption;

  { register variable }
  tvarregable=(vr_none,
    vr_intreg,
    vr_fpureg,
    vr_mmreg,
    { does not mean "needs address register", but "if it's a parameter which is }
    { passed by reference, then its address can be put in a register            }
    vr_addr
  );

  { types of the symtables }
  TSymtabletype = (
    abstractsymtable,      { not a real symtable             }
    globalsymtable,        { unit interface symtable         }
    staticsymtable,        { unit implementation symtable    }
    ObjectSymtable,        { object symtable                 }
    recordsymtable,        { record symtable                 }
    localsymtable,         { subroutine symtable             }
    parasymtable,          { arguments symtable              }
    withsymtable,          { with operator symtable          }
    stt_excepTSymtable,    { try/except symtable             }
    exportedmacrosymtable, { }
    localmacrosymtable,    { }
    enumsymtable,          { symtable for enum members       }
    arraysymtable          { used to store parameterised type
                             in array                        }
  );

  { options for symtables }
  tsymtableoption = (
    sto_has_helper        { contains at least one helper symbol }
  );
  tsymtableoptions = set of tsymtableoption;

  { definition contains the informations about a type }
  tdeftyp = (abstractdef,
    arraydef,recorddef,pointerdef,orddef,
    stringdef,enumdef,procdef,objectdef,errordef,
    filedef,formaldef,setdef,procvardef,floatdef,
    classrefdef,forwarddef,variantdef,undefineddef
  );

  { possible types for symtable entries }
  tsymtyp = (abstractsym,
    staticvarsym,localvarsym,paravarsym,fieldvarsym,
    typesym,procsym,unitsym,constsym,enumsym,
    errorsym,syssym,labelsym,absolutevarsym,propertysym,
    macrosym,namespacesym
  );

  { State of the variable:
     vs_declared: variable has been declared, not initialised
       (e.g. normal variable, out parameter)
     vs_initialised: variable has been declared and is valid
       (e.g. typed constant, var/const parameter)
     vs_read: variable has been read and the read was checked for validity
       (so a warning has been given if necessary)
     vs_read_not_warned: variable has been read, but we didn't warn about
       whether or not the variable was valid
       (e.g. read of global variable -> warn at end of compilation unit if
        the state is vs_read_not_warned, since that means it's only read and
        never written)
     vs_referred_not_inited: variable has been used in length/low/high/@/...
        expression, was not yet initialised and needn't be at that time
        (e.g. length() of a statically allocated array, or sizeof(variable))
     vs_written: variable has been assigned/written to, but not yet read
        (e.g. assigning something to a variable/parameter)
     vs_readwritten: variable has been written to and read from }
  tvarstate=(vs_none,
    vs_declared,vs_initialised,vs_read,vs_read_not_warned,
    vs_referred_not_inited,vs_written,vs_readwritten
  );

  tvarspez = (vs_value,vs_const,vs_var,vs_out,vs_constref,vs_final);

  absolutetyp = (tovar,toasm,toaddr);

  tconsttyp = (constnone,
    constord,conststring,constreal,
    constset,constpointer,constnil,
    constresourcestring,constwstring,constguid
  );

  { RTTI information to store }
  trttitype = (
    fullrtti,initrtti,
    { Objective-C }
    objcmetartti,objcmetarortti,
    objcclassrtti,objcclassrortti
  );

  { The order is from low priority to high priority,
    Note: the operators > and < are used on this list }
  tequaltype = (
    te_incompatible,
    te_convert_operator,
    te_convert_l6,
    te_convert_l5,     { ad infinitum... }
    te_convert_l4,     { and yet even less preferred conversion }
    te_convert_l3,     { even less preferred conversion (possibly with loss of data) }
    te_convert_l2,     { compatible less preferred conversion }
    te_convert_l1,     { compatible conversion     }
    te_equal,          { the definitions are equal }
    te_exact
  );

  tvariantequaltype = (
    tve_incompatible,
    tve_chari64,
    tve_sstring,
    tve_astring,
    tve_wstring,
    tve_ustring,
    tve_boolformal,
    tve_extended,
    tve_dblcurrency,
    tve_single,
    tve_cardinal,
    tve_longint,
    tve_smallint,
    tve_word,
    tve_shortint,
    tve_byte
  );
  tvariantequaltypes = set of tvariantequaltype;

  tdefdbgstatus = (
    dbg_state_unused,
    dbg_state_used,
    dbg_state_writing,
    dbg_state_written,
    dbg_state_queued
  );

var
  clearstack_pocalls : tproccalloptions;
  cdecl_pocalls      : tproccalloptions;

const
{$ifndef jvm}
   inherited_objectoptions : tobjectoptions = [oo_has_virtual,oo_has_private,oo_has_protected,
                oo_has_strictprotected,oo_has_strictprivate,oo_has_constructor,oo_has_destructor,
                oo_can_have_published];
{$else not jvm}
{ constructors are not inherited in Java }
inherited_objectoptions : tobjectoptions = [oo_has_virtual,oo_has_private,oo_has_protected,
             oo_has_strictprotected,oo_has_strictprivate,oo_has_destructor,
             oo_can_have_published];
{$endif not jvm}

{$ifdef i386}
   { we only take this into account on i386, on other platforms we always
     push in the same order
   }
   pushleftright_pocalls : tproccalloptions = [pocall_register,pocall_pascal];
{$endif}

     SymTypeName : array[tsymtyp] of string[12] = (
       'abstractsym','globalvar','localvar','paravar','fieldvar',
       'type','proc','unit','const','enum',
       'errorsym','system sym','label','absolutevar','property',
       'macrosym','namespace'
     );

     typName : array[tdeftyp] of string[12] = (
       'abstractdef','arraydef','recorddef','pointerdef','orddef',
       'stringdef','enumdef','procdef','objectdef','errordef',
       'filedef','formaldef','setdef','procvardef','floatdef',
       'classrefdef','forwarddef','variantdef','undefineddef'
     );

     EqualTypeName : array[tequaltype] of string[16] = (
       'incompatible','convert_operator','convert_l6', 'convert_l5','convert_l4','convert_l3',
       'convert_l2','convert_l1','equal','exact'
     );

     visibilityName : array[tvisibility] of string[16] = (
       'hidden','strict private','private','strict protected','protected',
       'public','published',''
     );


{$ifndef jvm}
     default_class_type=odt_class;
{$else not jvm}
     default_class_type=odt_javaclass;
{$endif not jvm}

{ !! Be sure to keep these in sync with ones in rtl/inc/varianth.inc }
      varempty = 0;
      varnull = 1;
      varsmallint = 2;
      varinteger = 3;
      varsingle = 4;
      vardouble = 5;
      varcurrency = 6;
      vardate = 7;
      varolestr = 8;
      vardispatch = 9;
      varerror = 10;
      varboolean = 11;
      varvariant = 12;
      varunknown = 13;
      vardecimal = 14;
      varshortint = 16;
      varbyte = 17;
      varword = 18;
      varlongword = 19;
      varint64 = 20;
      varqword = 21;

      varUndefined = -1;

      varstrarg = $48;
      varustrarg = $49;

      varstring = $100;
      varany = $101;
      varustring = $102;
      vardefmask = $fff;
      vararray = $2000;
      varbyref = $4000;

implementation

end.
