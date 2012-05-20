{
    Copyright (c) 2002 by Florian Klaempfl

    PowerPC specific calling conventions

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
unit cpupara;

{$i fpcdefs.inc}

  interface

    uses
       globtype,
       aasmtai,aasmdata,
       cpubase,
       symconst,symtype,symdef,symsym,
       paramgr,parabase,cgbase,cgutils;

    type
       tppcparamanager = class(tparamanager)
          function get_volatile_registers_int(calloption : tproccalloption):tcpuregisterset;override;
          function get_volatile_registers_fpu(calloption : tproccalloption):tcpuregisterset;override;
          function push_addr_param(varspez:tvarspez;def : tdef;calloption : tproccalloption) : boolean;override;

          procedure getintparaloc(calloption : tproccalloption; nr : longint;var cgpara:TCGPara);override;
          function create_paraloc_info(p : tabstractprocdef; side: tcallercallee):longint;override;
          function create_varargs_paraloc_info(p : tabstractprocdef; varargspara:tvarargsparalist):longint;override;
          function get_funcretloc(p : tabstractprocdef; side: tcallercallee; def: tdef): tcgpara;override;
          procedure create_funcretloc_info(p : tabstractprocdef; side: tcallercallee);
         private
          procedure init_values(var curintreg, curfloatreg, curmmreg: tsuperregister; var cur_stack_offset: aword);
          function create_paraloc_info_intern(p : tabstractprocdef; side: tcallercallee; paras:tparalist;
              var curintreg, curfloatreg, curmmreg: tsuperregister; var cur_stack_offset: aword; varargsparas: boolean):longint;
          function parseparaloc(p : tparavarsym;const s : string) : boolean;override;
       end;

  implementation

    uses
       verbose,systems,
       defutil,symtable,
       procinfo,cpupi;


    function tppcparamanager.get_volatile_registers_int(calloption : tproccalloption):tcpuregisterset;
      begin
        if (target_info.system = system_powerpc_darwin) then
          result := [RS_R0,RS_R2..RS_R12]
        else
          result := [RS_R0,RS_R3..RS_R12];
      end;


    function tppcparamanager.get_volatile_registers_fpu(calloption : tproccalloption):tcpuregisterset;
      begin
        case target_info.abi of
          abi_powerpc_aix,
          abi_powerpc_sysv:
            result := [RS_F0..RS_F13];
          else
            internalerror(2003091401);
        end;
      end;


    procedure tppcparamanager.getintparaloc(calloption : tproccalloption; nr : longint;var cgpara:TCGPara);
      var
        paraloc : pcgparalocation;
      begin
        cgpara.reset;
        cgpara.size:=OS_ADDR;
        cgpara.intsize:=sizeof(pint);
        cgpara.alignment:=get_para_align(calloption);
        paraloc:=cgpara.add_location;
        with paraloc^ do
         begin
           size:=OS_INT;
           if (nr<=8) then
             begin
               if nr=0 then
                 internalerror(200309271);
               loc:=LOC_REGISTER;
               register:=newreg(R_INTREGISTER,RS_R2+nr,R_SUBWHOLE);
             end
           else
             begin
               loc:=LOC_REFERENCE;
               paraloc^.reference.index:=NR_STACK_POINTER_REG;
               if (target_info.abi <> abi_powerpc_aix) then
                 reference.offset:=sizeof(pint)*(nr-8)
               else
                 reference.offset:=sizeof(pint)*(nr);
             end;
          end;
      end;



    function getparaloc(p : tdef) : tcgloc;

      begin
         { Later, the LOC_REFERENCE is in most cases changed into LOC_REGISTER
           if push_addr_param for the def is true
         }
         case p.typ of
            orddef:
              result:=LOC_REGISTER;
            floatdef:
              result:=LOC_FPUREGISTER;
            enumdef:
              result:=LOC_REGISTER;
            pointerdef:
              result:=LOC_REGISTER;
            formaldef:
              result:=LOC_REGISTER;
            classrefdef:
              result:=LOC_REGISTER;
            procvardef:
              if (target_info.abi = abi_powerpc_aix) or
                 (p.size = sizeof(pint)) then
                result:=LOC_REGISTER
              else
                result:=LOC_REFERENCE;
            recorddef:
              if not(target_info.system in systems_aix) and
                 ((target_info.abi<>abi_powerpc_aix) or
                  ((p.size >= 3) and
                   ((p.size mod 4) <> 0))) then
                result:=LOC_REFERENCE
              else
                result:=LOC_REGISTER;
            objectdef:
              if is_object(p) then
                result:=LOC_REFERENCE
              else
                result:=LOC_REGISTER;
            stringdef:
              if is_shortstring(p) or is_longstring(p) then
                result:=LOC_REFERENCE
              else
                result:=LOC_REGISTER;
            filedef:
              result:=LOC_REGISTER;
            arraydef:
              result:=LOC_REFERENCE;
            setdef:
              if is_smallset(p) then
                result:=LOC_REGISTER
              else
                result:=LOC_REFERENCE;
            variantdef:
              result:=LOC_REFERENCE;
            { avoid problems with errornous definitions }
            errordef:
              result:=LOC_REGISTER;
            else
              internalerror(2002071001);
         end;
      end;


    function tppcparamanager.push_addr_param(varspez:tvarspez;def : tdef;calloption : tproccalloption) : boolean;
      begin
        result:=false;
        { var,out,constref always require address }
        if varspez in [vs_var,vs_out,vs_constref] then
          begin
            result:=true;
            exit;
          end;
        case def.typ of
          variantdef,
          formaldef :
            result:=true;
          { regular procvars must be passed by value, because you cannot pass
            the address of a local stack location when calling e.g.
            pthread_create with the address of a function (first of all it
            expects the address of the function to execute and not the address
            of a memory location containing that address, and secondly if you
            first store the address on the stack and then pass the address of
            this stack location, then this stack location may no longer be
            valid when the newly started thread accesses it.

            However, for "procedure of object" we must use the same calling
            convention as for "8 byte record" due to the need for
            interchangeability with the TMethod record type.
          }
          procvardef :
            result:=
              (target_info.abi <> abi_powerpc_aix) and
              (def.size <> sizeof(pint));
          recorddef :
            result :=
              (target_info.abi<>abi_powerpc_aix) or
              ((varspez = vs_const) and
               ((calloption = pocall_mwpascal) or
                (not (calloption in [pocall_cdecl,pocall_cppdecl]) and
                 (def.size > 8)
                )
               )
              );
          arraydef:
            result:=(tarraydef(def).highrange>=tarraydef(def).lowrange) or
                             is_open_array(def) or
                             is_array_of_const(def) or
                             is_array_constructor(def);
          objectdef :
            result:=is_object(def);
          setdef :
            result:=not is_smallset(def);
          stringdef :
            result:=tstringdef(def).stringtype in [st_shortstring,st_longstring];
        end;
      end;


    procedure tppcparamanager.init_values(var curintreg, curfloatreg, curmmreg: tsuperregister; var cur_stack_offset: aword);
      begin
        case target_info.abi of
          abi_powerpc_aix:
            cur_stack_offset:=24;
          abi_powerpc_sysv:
            cur_stack_offset:=8;
          else
            internalerror(2003051901);
        end;
        curintreg:=RS_R3;
        curfloatreg:=RS_F1;
        curmmreg:=RS_M1;
      end;


    procedure tppcparamanager.create_funcretloc_info(p : tabstractprocdef; side: tcallercallee);
      begin
        p.funcretloc[side]:=get_funcretloc(p,side,p.returndef);
      end;


    function tppcparamanager.get_funcretloc(p : tabstractprocdef; side: tcallercallee; def: tdef): tcgpara;
      var
        paraloc : pcgparalocation;
        retcgsize  : tcgsize;
      begin
        result.init;
        result.alignment:=get_para_align(p.proccalloption);
        { void has no location }
        if is_void(def) then
          begin
            paraloc:=result.add_location;
            result.size:=OS_NO;
            result.intsize:=0;
            paraloc^.size:=OS_NO;
            paraloc^.loc:=LOC_VOID;
            exit;
          end;
        { Constructors return self instead of a boolean }
        if (p.proctypeoption=potype_constructor) then
          begin
            retcgsize:=OS_ADDR;
            result.intsize:=sizeof(pint);
          end
        else
          begin
            retcgsize:=def_cgsize(def);
            result.intsize:=def.size;
          end;
        result.size:=retcgsize;
        { Return is passed as var parameter }
        if ret_in_param(def,p.proccalloption) then
          begin
            paraloc:=result.add_location;
            paraloc^.loc:=LOC_REFERENCE;
            paraloc^.size:=retcgsize;
            exit;
          end;

        paraloc:=result.add_location;
        { Return in FPU register? }
        if def.typ=floatdef then
          begin
            paraloc^.loc:=LOC_FPUREGISTER;
            paraloc^.register:=NR_FPU_RESULT_REG;
            paraloc^.size:=retcgsize;
          end
        else
         { Return in register }
          begin
            if retcgsize in [OS_64,OS_S64] then
             begin
               { low 32bits }
               paraloc^.loc:=LOC_REGISTER;
               if side=callerside then
                 paraloc^.register:=NR_FUNCTION_RESULT64_HIGH_REG
               else
                 paraloc^.register:=NR_FUNCTION_RETURN64_HIGH_REG;
               paraloc^.size:=OS_32;
               { high 32bits }
               paraloc:=result.add_location;
               paraloc^.loc:=LOC_REGISTER;
               if side=callerside then
                 paraloc^.register:=NR_FUNCTION_RESULT64_LOW_REG
               else
                 paraloc^.register:=NR_FUNCTION_RETURN64_LOW_REG;
               paraloc^.size:=OS_32;
             end
            else
             begin
               paraloc^.loc:=LOC_REGISTER;
               if side=callerside then
                 paraloc^.register:=newreg(R_INTREGISTER,RS_FUNCTION_RESULT_REG,cgsize2subreg(R_INTREGISTER,retcgsize))
               else
                 paraloc^.register:=newreg(R_INTREGISTER,RS_FUNCTION_RETURN_REG,cgsize2subreg(R_INTREGISTER,retcgsize));
               paraloc^.size:=retcgsize;
             end;
          end;
      end;


    function tppcparamanager.create_paraloc_info(p : tabstractprocdef; side: tcallercallee):longint;

      var
        cur_stack_offset: aword;
        curintreg, curfloatreg, curmmreg: tsuperregister;
      begin
        init_values(curintreg,curfloatreg,curmmreg,cur_stack_offset);

        result := create_paraloc_info_intern(p,side,p.paras,curintreg,curfloatreg,curmmreg,cur_stack_offset,false);

        create_funcretloc_info(p,side);
      end;



    function tppcparamanager.create_paraloc_info_intern(p : tabstractprocdef; side: tcallercallee; paras:tparalist;
               var curintreg, curfloatreg, curmmreg: tsuperregister; var cur_stack_offset: aword; varargsparas: boolean):longint;
      var
         stack_offset: longint;
         paralen: aint;
         nextintreg,nextfloatreg,nextmmreg, maxfpureg : tsuperregister;
         paradef : tdef;
         paraloc : pcgparalocation;
         i  : integer;
         hp : tparavarsym;
         loc : tcgloc;
         paracgsize: tcgsize;
         sym: tfieldvarsym;

      begin
{$ifdef extdebug}
         if po_explicitparaloc in p.procoptions then
           internalerror(200411141);
{$endif extdebug}

         result:=0;
         nextintreg := curintreg;
         nextfloatreg := curfloatreg;
         nextmmreg := curmmreg;
         stack_offset := cur_stack_offset;
         case target_info.abi of
           abi_powerpc_aix:
             maxfpureg := RS_F13;
           abi_powerpc_sysv:
             maxfpureg := RS_F8;
           else internalerror(2004070912);
         end;

          for i:=0 to paras.count-1 do
            begin
              hp:=tparavarsym(paras[i]);
              paradef := hp.vardef;
              { Syscall for Morphos can have already a paraloc set }
              if (vo_has_explicit_paraloc in hp.varoptions) then
                begin
                  if not(vo_is_syscall_lib in hp.varoptions) then
                    internalerror(200412153);
                  continue;
                end;
              hp.paraloc[side].reset;
              { currently only support C-style array of const }
              if (p.proccalloption in [pocall_cdecl,pocall_cppdecl,pocall_mwpascal]) and
                 is_array_of_const(paradef) then
                begin
                  paraloc:=hp.paraloc[side].add_location;
                  { hack: the paraloc must be valid, but is not actually used }
                  paraloc^.loc := LOC_REGISTER;
                  paraloc^.register := NR_R0;
                  paraloc^.size := OS_ADDR;
                  break;
                end;

              if (hp.varspez in [vs_var,vs_out]) or
                 push_addr_param(hp.varspez,paradef,p.proccalloption) or
                 is_open_array(paradef) or
                 is_array_of_const(paradef) then
                begin
                  paradef:=voidpointertype;
                  loc:=LOC_REGISTER;
                  paracgsize := OS_ADDR;
                  paralen := tcgsize2size[OS_ADDR];
                end
              else
                begin
                  if not is_special_array(paradef) then
                    paralen := paradef.size
                  else
                    paralen := tcgsize2size[def_cgsize(paradef)];
                  if (target_info.abi = abi_powerpc_aix) and
                     (paradef.typ = recorddef) and
                     (hp.varspez in [vs_value,vs_const]) then
                    begin
                      { if a record has only one field and that field is }
                      { non-composite (not array or record), it must be  }
                      { passed according to the rules of that type.       }
                      if tabstractrecordsymtable(tabstractrecorddef(paradef).symtable).has_single_field(sym) and
                         ((sym.vardef.typ=floatdef) or
                          ((target_info.system=system_powerpc_darwin) and
                           (sym.vardef.typ in [orddef,enumdef]))) then
                        begin
                          paradef:=sym.vardef;
                          paracgsize:=def_cgsize(paradef);
                        end
                      else
                        begin
                          paracgsize := int_cgsize(paralen);
                        end;
                    end
                  else
                    begin
                      paracgsize:=def_cgsize(paradef);
                      { for things like formaldef }
                      if (paracgsize=OS_NO) then
                        begin
                          paracgsize:=OS_ADDR;
                          paralen := tcgsize2size[OS_ADDR];
                        end;
                    end
                end;

              loc := getparaloc(paradef);
              if varargsparas and
                 (target_info.abi = abi_powerpc_aix) and
                 (paradef.typ = floatdef) then
                begin
                  loc := LOC_REGISTER;
                  if paracgsize = OS_F64 then
                    paracgsize := OS_64
                  else
                    paracgsize := OS_32;
                end;

              hp.paraloc[side].alignment:=std_param_align;
              hp.paraloc[side].size:=paracgsize;
              hp.paraloc[side].intsize:=paralen;
              if (target_info.abi = abi_powerpc_aix) and
                 (paradef.typ in [recorddef,arraydef]) then
                hp.paraloc[side].composite:=true;
{$ifndef cpu64bitaddr}
              if (target_info.abi=abi_powerpc_sysv) and
                 is_64bit(paradef) and
                 odd(nextintreg-RS_R3) then
                inc(nextintreg);
{$endif not cpu64bitaddr}
              if (paralen = 0) then
                if (paradef.typ = recorddef) then
                  begin
                    paraloc:=hp.paraloc[side].add_location;
                    paraloc^.loc := LOC_VOID;
                  end
                else
                  internalerror(2005011310);
              { can become < 0 for e.g. 3-byte records }
              while (paralen > 0) do
                begin
                  paraloc:=hp.paraloc[side].add_location;
                  { In case of po_delphi_nested_cc, the parent frame pointer
                    is always passed on the stack. }
                  if (loc = LOC_REGISTER) and
                     (nextintreg <= RS_R10) and
                     (not(vo_is_parentfp in hp.varoptions) or
                      not(po_delphi_nested_cc in p.procoptions)) then
                    begin
                      paraloc^.loc := loc;
                      { make sure we don't lose whether or not the type is signed }
                      if (paradef.typ <> orddef) then
                        paracgsize := int_cgsize(paralen);
                      if (paracgsize in [OS_NO,OS_64,OS_S64,OS_128,OS_S128]) then
                        paraloc^.size := OS_INT
                      else
                        paraloc^.size := paracgsize;
                      { aix requires that record data stored in parameter
                        registers is left-aligned }
                      if (target_info.system in systems_aix) and
                         (paradef.typ = recorddef) and
                         (tcgsize2size[paraloc^.size] <> sizeof(aint)) then
                        begin
                          paraloc^.shiftval := (sizeof(aint)-tcgsize2size[paraloc^.size])*(-8);
                          paraloc^.size := OS_INT;
                        end;
                      paraloc^.register:=newreg(R_INTREGISTER,nextintreg,R_SUBNONE);
                      inc(nextintreg);
                      dec(paralen,tcgsize2size[paraloc^.size]);
                      if target_info.abi=abi_powerpc_aix then
                        inc(stack_offset,align(tcgsize2size[paraloc^.size],4));
                    end
                  else if (loc = LOC_FPUREGISTER) and
                          (nextfloatreg <= maxfpureg) then
                    begin
                      paraloc^.loc:=loc;
                      paraloc^.size := paracgsize;
                      paraloc^.register:=newreg(R_FPUREGISTER,nextfloatreg,R_SUBWHOLE);
                      inc(nextfloatreg);
                      dec(paralen,tcgsize2size[paraloc^.size]);
                      { if nextfpureg > maxfpureg, all intregs are already used, since there }
                      { are less of those available for parameter passing in the AIX abi     }
                      if target_info.abi=abi_powerpc_aix then
{$ifndef cpu64bitaddr}
                        if (paracgsize = OS_F32) then
                          begin
                            inc(stack_offset,4);
                            if (nextintreg < RS_R11) then
                              inc(nextintreg);
                          end
                        else
                          begin
                            inc(stack_offset,8);
                            if (nextintreg < RS_R10) then
                              inc(nextintreg,2)
                            else
                              nextintreg := RS_R11;
                          end;
{$else not cpu64bitaddr}
                          begin
                            inc(stack_offset,tcgsize2size[paracgsize]);
                            if (nextintreg < RS_R11) then
                              inc(nextintreg);
                          end;
{$endif not cpu64bitaddr}
                    end
                  else { LOC_REFERENCE }
                    begin
                       paraloc^.loc:=LOC_REFERENCE;
                       case loc of
                         LOC_FPUREGISTER:
                           paraloc^.size:=int_float_cgsize(paralen);
                         LOC_REGISTER,
                         LOC_REFERENCE:
                           paraloc^.size:=int_cgsize(paralen);
                         else
                           internalerror(2006011101);
                       end;
                       if (side = callerside) then
                         paraloc^.reference.index:=NR_STACK_POINTER_REG
                       else
                         begin
                           paraloc^.reference.index:=NR_R12;
                           tppcprocinfo(current_procinfo).needs_frame_pointer := true;
                         end;

                       if not((target_info.system in systems_aix) and
                              (paradef.typ=recorddef)) and
                          (target_info.abi = abi_powerpc_aix) and
                          (hp.paraloc[side].intsize < 3) then
                         paraloc^.reference.offset:=stack_offset+(4-paralen)
                       else
                         paraloc^.reference.offset:=stack_offset;

                       inc(stack_offset,align(paralen,4));
                       while (paralen > 0) and
                             (nextintreg < RS_R11) do
                          begin
                            inc(nextintreg);
                            dec(paralen,sizeof(pint));
                          end;
                       paralen := 0;
                    end;
                end;
            end;
         curintreg:=nextintreg;
         curfloatreg:=nextfloatreg;
         curmmreg:=nextmmreg;
         cur_stack_offset:=stack_offset;
         result:=stack_offset;
      end;


    function tppcparamanager.create_varargs_paraloc_info(p : tabstractprocdef; varargspara:tvarargsparalist):longint;
      var
        cur_stack_offset: aword;
        parasize, l: longint;
        curintreg, firstfloatreg, curfloatreg, curmmreg: tsuperregister;
        i : integer;
        hp: tparavarsym;
        paraloc: pcgparalocation;
      begin
        init_values(curintreg,curfloatreg,curmmreg,cur_stack_offset);
        firstfloatreg:=curfloatreg;

        result:=create_paraloc_info_intern(p,callerside,p.paras,curintreg,curfloatreg,curmmreg,cur_stack_offset, false);
        if (p.proccalloption in [pocall_cdecl,pocall_cppdecl,pocall_mwpascal]) then
          { just continue loading the parameters in the registers }
          begin
            result:=create_paraloc_info_intern(p,callerside,varargspara,curintreg,curfloatreg,curmmreg,cur_stack_offset,true);
            { varargs routines have to reserve at least 32 bytes for the AIX abi }
            if (target_info.abi = abi_powerpc_aix) and
               (result < 32) then
              result := 32;
           end
        else
          begin
            parasize:=cur_stack_offset;
            for i:=0 to varargspara.count-1 do
              begin
                hp:=tparavarsym(varargspara[i]);
                hp.paraloc[callerside].alignment:=4;
                paraloc:=hp.paraloc[callerside].add_location;
                paraloc^.loc:=LOC_REFERENCE;
                paraloc^.size:=def_cgsize(hp.vardef);
                paraloc^.reference.index:=NR_STACK_POINTER_REG;
                l:=push_size(hp.varspez,hp.vardef,p.proccalloption);
                paraloc^.reference.offset:=parasize;
                parasize:=parasize+l;
              end;
            result:=parasize;
          end;
        if curfloatreg<>firstfloatreg then
          include(varargspara.varargsinfo,va_uses_float_reg);
      end;


    function tppcparamanager.parseparaloc(p : tparavarsym;const s : string) : boolean;
      var
        paraloc : pcgparalocation;
        paracgsize : tcgsize;
      begin
        result:=false;
        case target_info.system of
          system_powerpc_morphos:
            begin
              paracgsize:=def_cgsize(p.vardef);
              p.paraloc[callerside].alignment:=4;
              p.paraloc[callerside].size:=paracgsize;
              p.paraloc[callerside].intsize:=tcgsize2size[paracgsize];
              paraloc:=p.paraloc[callerside].add_location;
              paraloc^.loc:=LOC_REFERENCE;
              paraloc^.size:=paracgsize;
              paraloc^.reference.index:=newreg(R_INTREGISTER,RS_R2,R_SUBWHOLE);
              { pattern is always uppercase'd }
              if s='D0' then
                paraloc^.reference.offset:=0
              else if s='D1' then
                paraloc^.reference.offset:=4
              else if s='D2' then
                paraloc^.reference.offset:=8
              else if s='D3' then
                paraloc^.reference.offset:=12
              else if s='D4' then
                paraloc^.reference.offset:=16
              else if s='D5' then
                paraloc^.reference.offset:=20
              else if s='D6' then
                paraloc^.reference.offset:=24
              else if s='D7' then
                paraloc^.reference.offset:=28
              else if s='A0' then
                paraloc^.reference.offset:=32
              else if s='A1' then
                paraloc^.reference.offset:=36
              else if s='A2' then
                paraloc^.reference.offset:=40
              else if s='A3' then
                paraloc^.reference.offset:=44
              else if s='A4' then
                paraloc^.reference.offset:=48
              else if s='A5' then
                paraloc^.reference.offset:=52
              { 'A6' (offset 56) is used by mossyscall as libbase, so API
                never passes parameters in it,
                Indeed, but this allows to declare libbase either explicitly
                or let the compiler insert it }
              else if s='A6' then
                paraloc^.reference.offset:=56
              { 'A7' is the stack pointer on 68k, can't be overwritten
                by API calls, so it has no offset }
              { 'R12' is special, used internally to support r12base sysv
                calling convention }
              else if s='R12' then
                begin
                  paraloc^.loc:=LOC_REGISTER;
                  paraloc^.size:=OS_ADDR;
                  paraloc^.register:=NR_R12;
                end
              else
                exit;

              { copy to callee side }
              p.paraloc[calleeside].add_location^:=paraloc^;
            end;
          else
            internalerror(200404182);
        end;
        result:=true;
      end;

begin
   paramanager:=tppcparamanager.create;
end.
