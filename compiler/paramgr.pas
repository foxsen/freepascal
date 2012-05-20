{
    Copyright (c) 2002 by Florian Klaempfl

    Generic calling convention handling

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
{# Parameter passing manager. Used to manage how
   parameters are passed to routines.
}
unit paramgr;

{$i fpcdefs.inc}

  interface

    uses
       cclasses,globtype,
       cpubase,cgbase,cgutils,
       parabase,
       aasmtai,aasmdata,
       symconst,symtype,symsym,symdef;

    type
       {# This class defines some methods to take care of routine
          parameters. It should be overridden for each new processor
       }

       { tparamanager }

       tparamanager = class
          { true if the location in paraloc can be reused as localloc }
          function param_use_paraloc(const cgpara:tcgpara):boolean;virtual;
          {# Returns true if the return value is actually a parameter
             pointer.
          }
          function ret_in_param(def : tdef;calloption : tproccalloption) : boolean;virtual;

          function push_high_param(varspez:tvarspez;def : tdef;calloption : tproccalloption) : boolean;virtual;

          { Returns true if a parameter is too large to copy and only
            the address is pushed
          }
          function push_addr_param(varspez:tvarspez;def : tdef;calloption : tproccalloption) : boolean;virtual;abstract;
          { returns true if a parameter must be handled via copy-out (construct
            a reference, copy the parameter's value there in case of copy-in/out, pass the reference)
          }
          function push_copyout_param(varspez:tvarspez;def : tdef;calloption : tproccalloption) : boolean;virtual;
          { return the size of a push }
          function push_size(varspez:tvarspez;def : tdef;calloption : tproccalloption) : longint;virtual;
          {# Returns a structure giving the information on
            the storage of the parameter (which must be
            an integer parameter). This is only used when calling
            internal routines directly, where all parameters must
            be 4-byte values.

            In case the location is a register, this register is allocated.
            Call freeintparaloc() after the call to free the locations again.
            Default implementation: don't do anything at all (in case you don't
            use register parameter passing)

            @param(list Current assembler list)
            @param(nr Parameter number of routine, starting from 1)
          }
          function get_para_align(calloption : tproccalloption):byte;virtual;
          function get_volatile_registers_int(calloption : tproccalloption):tcpuregisterset;virtual;
          function get_volatile_registers_fpu(calloption : tproccalloption):tcpuregisterset;virtual;
          function get_volatile_registers_flags(calloption : tproccalloption):tcpuregisterset;virtual;
          function get_volatile_registers_mm(calloption : tproccalloption):tcpuregisterset;virtual;

          procedure getintparaloc(calloption : tproccalloption; nr : longint;var cgpara:TCGPara);virtual;abstract;

          {# allocate an individual pcgparalocation that's part of a tcgpara

            @param(list Current assembler list)
            @param(loc Parameter location element)
          }
          procedure allocparaloc(list: TAsmList; const paraloc: pcgparalocation);

          {# allocate a parameter location created with create_paraloc_info

            @param(list Current assembler list)
            @param(loc Parameter location)
          }
          procedure alloccgpara(list: TAsmList; const cgpara: TCGPara); virtual;

          {# free a parameter location allocated with alloccgpara

            @param(list Current assembler list)
            @param(loc Parameter location)
          }
          procedure freecgpara(list: TAsmList; const cgpara: TCGPara); virtual;

          { This is used to populate the location information on all parameters
            for the routine as seen in either the caller or the callee. It returns
            the size allocated on the stack
          }
          function  create_paraloc_info(p : tabstractprocdef; side: tcallercallee):longint;virtual;abstract;

          { Returns the location of the function result if p had def as
            function result instead of its actual result. Used if the compiler
            forces the function result to something different than the real
            result.  }
          function  get_funcretloc(p : tabstractprocdef; side: tcallercallee; def: tdef): tcgpara;virtual;abstract;

          { This is used to populate the location information on all parameters
            for the routine when it is being inlined. It returns
            the size allocated on the stack
          }
          function  create_inline_paraloc_info(p : tabstractprocdef):longint;virtual;

          { This is used to populate the location information on all parameters
            for the routine that are passed as varargs. It returns
            the size allocated on the stack (including the normal parameters)
          }
          function  create_varargs_paraloc_info(p : tabstractprocdef; varargspara:tvarargsparalist):longint;virtual;abstract;

          function is_stack_paraloc(paraloc: pcgparalocation): boolean;virtual;
          procedure createtempparaloc(list: TAsmList;calloption : tproccalloption;parasym : tparavarsym;can_use_final_stack_loc : boolean;var cgpara:TCGPara);virtual;
          procedure duplicatecgparaloc(const orgparaloc: pcgparalocation; intonewparaloc: pcgparalocation);
          procedure duplicateparaloc(list: TAsmList;calloption : tproccalloption;parasym : tparavarsym;var cgpara:TCGPara);

          function parseparaloc(parasym : tparavarsym;const s : string) : boolean;virtual;
          function parsefuncretloc(p : tabstractprocdef; const s : string) : boolean;virtual;

          { allocate room for parameters on the stack in the entry code? }
          function use_fixed_stack: boolean;
          { whether stack pointer can be changed in the middle of procedure }
          function use_stackalloc: boolean;
       end;


    var
       paramanager : tparamanager;


implementation

    uses
       systems,
       cgobj,tgobj,
       defutil,verbose;

    { true if the location in paraloc can be reused as localloc }
    function tparamanager.param_use_paraloc(const cgpara:tcgpara):boolean;
      begin
        result:=false;
      end;


    { true if uses a parameter as return value }
    function tparamanager.ret_in_param(def : tdef;calloption : tproccalloption) : boolean;
      begin
         ret_in_param:=((def.typ=arraydef) and not(is_dynamic_array(def))) or
           (def.typ=recorddef) or
           (def.typ=stringdef) or
           ((def.typ=procvardef) and not tprocvardef(def).is_addressonly) or
           { interfaces are also passed by reference to be compatible with delphi and COM }
           ((def.typ=objectdef) and (is_object(def) or is_interface(def) or is_dispinterface(def))) or
           (def.typ=variantdef) or
           ((def.typ=setdef) and not is_smallset(def));
      end;


    function tparamanager.push_high_param(varspez:tvarspez;def : tdef;calloption : tproccalloption) : boolean;
      begin
         push_high_param:=not(calloption in cdecl_pocalls) and
                          (
                           is_open_array(def) or
                           is_open_string(def) or
                           is_array_of_const(def)
                          );
      end;


    function tparamanager.push_copyout_param(varspez: tvarspez; def: tdef; calloption: tproccalloption): boolean;
      begin
        push_copyout_param:=false;
      end;


    { return the size of a push }
    function tparamanager.push_size(varspez:tvarspez;def : tdef;calloption : tproccalloption) : longint;
      begin
        push_size:=-1;
        case varspez of
          vs_constref,
          vs_out,
          vs_var :
            push_size:=sizeof(pint);
          vs_value,
          vs_const :
            begin
                if push_addr_param(varspez,def,calloption) then
                  push_size:=sizeof(pint)
                else
                  begin
                    { special array are normally pushed by addr, only for
                      cdecl array of const it comes here and the pushsize
                      is unknown }
                    if is_array_of_const(def) then
                      push_size:=0
                    else
                      push_size:=def.size;
                  end;
            end;
        end;
      end;


    function tparamanager.get_para_align(calloption : tproccalloption):byte;
      begin
        result:=std_param_align;
      end;


    function tparamanager.get_volatile_registers_int(calloption : tproccalloption):tcpuregisterset;
      begin
        result:=[];
      end;


    function tparamanager.get_volatile_registers_fpu(calloption : tproccalloption):tcpuregisterset;
      begin
        result:=[];
      end;


    function tparamanager.get_volatile_registers_flags(calloption : tproccalloption):tcpuregisterset;
      begin
        result:=[];
      end;


    function tparamanager.get_volatile_registers_mm(calloption : tproccalloption):tcpuregisterset;
      begin
        result:=[];
      end;

{$if first_mm_imreg = 0}
  {$WARN 4044 OFF} { Comparison might be always false ... }
{$endif}

    procedure tparamanager.allocparaloc(list: TAsmList; const paraloc: pcgparalocation);
      begin
        case paraloc^.loc of
          LOC_REGISTER,
          LOC_CREGISTER:
            begin
              if getsupreg(paraloc^.register)<first_int_imreg then
                cg.getcpuregister(list,paraloc^.register);
            end;
{$ifndef x86}
{ don't allocate ST(x), they're not handled by the register allocator }
          LOC_FPUREGISTER,
          LOC_CFPUREGISTER:
            begin
              if getsupreg(paraloc^.register)<first_fpu_imreg then
                cg.getcpuregister(list,paraloc^.register);
            end;
{$endif not x86}
          LOC_MMREGISTER,
          LOC_CMMREGISTER :
            begin
              if getsupreg(paraloc^.register)<first_mm_imreg then
                cg.getcpuregister(list,paraloc^.register);
            end;
        end;
      end;


    procedure tparamanager.alloccgpara(list: TAsmList; const cgpara: TCGPara);
      var
        paraloc : pcgparalocation;
      begin
        paraloc:=cgpara.location;
        while assigned(paraloc) do
          begin
            allocparaloc(list,paraloc);
            paraloc:=paraloc^.next;
          end;
      end;


    procedure tparamanager.freecgpara(list: TAsmList; const cgpara: TCGPara);
      var
        paraloc : Pcgparalocation;
        href : treference;
      begin
        paraloc:=cgpara.location;
        while assigned(paraloc) do
          begin
            case paraloc^.loc of
              LOC_VOID:
                ;
              LOC_REGISTER,
              LOC_CREGISTER:
                begin
                  if getsupreg(paraloc^.register)<first_int_imreg then
                    cg.ungetcpuregister(list,paraloc^.register);
                end;
              LOC_FPUREGISTER,
              LOC_CFPUREGISTER:
                begin
                  if getsupreg(paraloc^.register)<first_fpu_imreg then
                    cg.ungetcpuregister(list,paraloc^.register);
                end;
              LOC_MMREGISTER,
              LOC_CMMREGISTER :
                begin
                  if getsupreg(paraloc^.register)<first_mm_imreg then
                    cg.ungetcpuregister(list,paraloc^.register);
                end;
              LOC_REFERENCE,
              LOC_CREFERENCE :
                begin
                  if use_fixed_stack then
                    begin
                      { don't use reference_reset_base, because that will depend on cgobj }
                      fillchar(href,sizeof(href),0);
                      href.base:=paraloc^.reference.index;
                      href.offset:=paraloc^.reference.offset;
                      tg.ungetiftemp(list,href);
                    end;
                end;
              else
                internalerror(2004110212);
            end;
            paraloc:=paraloc^.next;
          end;
      end;


    function tparamanager.is_stack_paraloc(paraloc: pcgparalocation): boolean;
      begin
        result:=
          assigned(paraloc) and
          (paraloc^.loc=LOC_REFERENCE) and
          (paraloc^.reference.index=NR_STACK_POINTER_REG);
      end;


    procedure tparamanager.createtempparaloc(list: TAsmList;calloption : tproccalloption;parasym : tparavarsym;can_use_final_stack_loc : boolean;var cgpara:TCGPara);
      var
        href : treference;
        len  : aint;
        paraloc,
        newparaloc : pcgparalocation;
      begin
        paraloc:=parasym.paraloc[callerside].location;
        cgpara.reset;
        cgpara.size:=parasym.paraloc[callerside].size;
        cgpara.intsize:=parasym.paraloc[callerside].intsize;
        cgpara.alignment:=parasym.paraloc[callerside].alignment;
        cgpara.def:=parasym.paraloc[callerside].def;
{$ifdef powerpc}
        cgpara.composite:=parasym.paraloc[callerside].composite;
{$endif powerpc}
        while assigned(paraloc) do
          begin
            if paraloc^.size=OS_NO then
              len:=push_size(parasym.varspez,parasym.vardef,calloption)
            else
              len:=tcgsize2size[paraloc^.size];
            newparaloc:=cgpara.add_location;
            newparaloc^.size:=paraloc^.size;
            newparaloc^.shiftval:=paraloc^.shiftval;
            { $warning maybe release this optimization for all targets?  }
            { released for all CPUs:
              i386 isn't affected anyways because it uses the stack to push parameters
              on arm it reduces executable size of the compiler by 2.1 per cent (FK) }
            { Does it fit a register? }
            if ((not can_use_final_stack_loc and
                 use_fixed_stack) or
                not is_stack_paraloc(paraloc)) and
               (len<=sizeof(pint)) and
               (paraloc^.size in [OS_8,OS_16,OS_32,OS_64,OS_128,OS_S8,OS_S16,OS_S32,OS_S64,OS_S128]) then
              newparaloc^.loc:=LOC_REGISTER
            else
              newparaloc^.loc:=paraloc^.loc;
            case newparaloc^.loc of
              LOC_REGISTER :
                newparaloc^.register:=cg.getintregister(list,paraloc^.size);
              LOC_FPUREGISTER :
                newparaloc^.register:=cg.getfpuregister(list,paraloc^.size);
              LOC_MMREGISTER :
                newparaloc^.register:=cg.getmmregister(list,paraloc^.size);
              LOC_REFERENCE :
                begin
                  if (can_use_final_stack_loc or
                      not use_fixed_stack) and
                     is_stack_paraloc(paraloc) then
                    duplicatecgparaloc(paraloc,newparaloc)
                  else
                    begin
                      if assigned(cgpara.def) then
                        tg.gethltemp(list,cgpara.def,len,tt_persistent,href)
                      else
                        tg.gettemp(list,len,cgpara.alignment,tt_persistent,href);
                      newparaloc^.reference.index:=href.base;
                      newparaloc^.reference.offset:=href.offset;
                    end;
                end;
            end;
            paraloc:=paraloc^.next;
          end;
      end;


    procedure tparamanager.duplicatecgparaloc(const orgparaloc: pcgparalocation; intonewparaloc: pcgparalocation);
      begin
        move(orgparaloc^,intonewparaloc^,sizeof(intonewparaloc^));
        intonewparaloc^.next:=nil;
      end;


    procedure tparamanager.duplicateparaloc(list: TAsmList;calloption : tproccalloption;parasym : tparavarsym;var cgpara:TCGPara);
      var
        paraloc,
        newparaloc : pcgparalocation;
      begin
        cgpara.reset;
        cgpara.size:=parasym.paraloc[callerside].size;
        cgpara.intsize:=parasym.paraloc[callerside].intsize;
        cgpara.alignment:=parasym.paraloc[callerside].alignment;
{$ifdef powerpc}
        cgpara.composite:=parasym.paraloc[callerside].composite;
{$endif powerpc}
        paraloc:=parasym.paraloc[callerside].location;
        while assigned(paraloc) do
          begin
            newparaloc:=cgpara.add_location;
            duplicatecgparaloc(paraloc,newparaloc);
            paraloc:=paraloc^.next;
          end;
      end;


    function tparamanager.create_inline_paraloc_info(p : tabstractprocdef):longint;
      begin
        { We need to return the size allocated }
        p.init_paraloc_info(callbothsides);
        result:=p.calleeargareasize;
      end;


    function tparamanager.parseparaloc(parasym: tparavarsym; const s: string): boolean;
      begin
        Result:=False;
        internalerror(200807235);
      end;


    function tparamanager.parsefuncretloc(p: tabstractprocdef; const s: string): boolean;
      begin
        Result:=False;
        internalerror(200807236);
      end;


    function tparamanager.use_fixed_stack: boolean;
      begin
{$ifdef i386}
        result := (target_info.system in [system_i386_darwin,system_i386_iphonesim]);
{$else i386}
{$ifdef cputargethasfixedstack}
        result := true;
{$else cputargethasfixedstack}
        result := false;
{$endif cputargethasfixedstack}
{$endif i386}
      end;

    { This is a separate function because at least win64 allows stack allocations
      despite of fixed stack semantics (actually supporting it requires generating
      a compliant stack frame, not yet possible) }
    function tparamanager.use_stackalloc: boolean;
      begin
        result:=not use_fixed_stack;
      end;

initialization
  ;
finalization
  paramanager.free;
end.
