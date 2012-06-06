{
    Copyright (c) 1998-2002 by Florian Klaempfl and David Zhang

    Calling conventions for the MIPSEL

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
 *****************************************************************************}
unit cpupara;

{$i fpcdefs.inc}

interface

    uses
      globtype,
      cclasses,
      aasmtai,
      cpubase,cpuinfo,
      symconst,symbase,symsym,symtype,symdef,paramgr,parabase,cgbase;

    type
      TMIPSParaManager=class(TParaManager)
        function  push_addr_param(varspez:tvarspez;def : tdef;calloption : tproccalloption) : boolean;override;
        function  get_volatile_registers_int(calloption : tproccalloption):TCpuRegisterSet;override;
        function  get_volatile_registers_fpu(calloption : tproccalloption):TCpuRegisterSet;override;
        {Returns a structure giving the information on the storage of the parameter
        (which must be an integer parameter)
        @param(nr Parameter number of routine, starting from 1)}
        procedure getintparaloc(calloption : tproccalloption; nr : longint;var cgpara : TCGPara);override;
        function  create_paraloc_info(p : TAbstractProcDef; side: tcallercallee):longint;override;
        function  create_varargs_paraloc_info(p : TAbstractProcDef; varargspara:tvarargsparalist):longint;override;
        function  get_funcretloc(p : tabstractprocdef; side: tcallercallee; def: tdef): tcgpara;override;
      private
        procedure create_funcretloc_info(p : tabstractprocdef; side: tcallercallee);
        procedure create_paraloc_info_intern(p : tabstractprocdef; side: tcallercallee; paras: tparalist;
                                             var intparareg,parasize:longint);
      end;

implementation

    uses
      cutils,verbose,systems,
      defutil,
      cgutils,cgobj,
      procinfo,cpupi;

    type
      tparasupregs = array[0..3] of tsuperregister;
      pparasupregs = ^tparasupregs;
    const
      paraoutsupregs : tparasupregs = (RS_R4, RS_R5, RS_R6, RS_R7);
      parainsupregs  : tparasupregs = (RS_R4, RS_R5, RS_R6, RS_R7);


    function TMIPSParaManager.get_volatile_registers_int(calloption : tproccalloption):TCpuRegisterSet;
      begin
        result:=[RS_R1..RS_R15,RS_R24..RS_R25,RS_R31];
      end;


    function TMIPSParaManager.get_volatile_registers_fpu(calloption : tproccalloption):TCpuRegisterSet;
      begin
        result:=[RS_F0..RS_F19];
      end;


    procedure TMIPSParaManager.GetIntParaLoc(calloption : tproccalloption; nr : longint;var cgpara : tcgpara);
      var
        paraloc : pcgparalocation;
      begin
        if nr<1 then
          InternalError(2002100806);
        cgpara.reset;
        cgpara.size:=OS_INT;
        cgpara.intsize:=tcgsize2size[OS_INT];
        cgpara.alignment:=std_param_align;
        paraloc:=cgpara.add_location;
        with paraloc^ do
          begin
            { The first four parameters are passed into registers } 
            dec(nr);
            if nr<4 then 
              begin
                loc:=LOC_REGISTER;
                register:=newreg(R_INTREGISTER,(RS_R4+nr),R_SUBWHOLE);
              end
            else
              begin
                { The other parameters are passed on the stack }
                loc:=LOC_REFERENCE;
                reference.index:=NR_STACK_POINTER_REG;
                reference.offset:=16 + (nr-4)*4;
              end;
            size:=OS_INT;
          end;
      end;

    { true if a parameter is too large to copy and only the address is pushed }
    function TMIPSParaManager.push_addr_param(varspez:tvarspez;def : tdef;calloption : tproccalloption) : boolean;
      begin
        result:=false;
        { var,out,constref always require address }
        if varspez in [vs_var,vs_out,vs_constref] then
          begin
            result:=true;
            exit;
          end;
        case def.typ of
          recorddef,
          arraydef,
          variantdef,
          formaldef :
            push_addr_param:=true;
          objectdef :
            result:=is_object(def);
          stringdef :
            result:=(tstringdef(def).stringtype in [st_shortstring,st_longstring]);
          procvardef :
            result:=not tprocvardef(def).is_addressonly;
          setdef :
            result:=not(is_smallset(def));
        end;
      end;


    procedure TMIPSParaManager.create_funcretloc_info(p : tabstractprocdef; side: tcallercallee);
      begin
        p.funcretloc[side]:=get_funcretloc(p,side,p.returndef);
      end;


    function TMIPSParaManager.get_funcretloc(p : tabstractprocdef; side: tcallercallee; def: tdef): tcgpara;
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
        if p.returndef.typ=floatdef then
          begin
            paraloc^.loc:=LOC_FPUREGISTER;
            paraloc^.register:=NR_FPU_RESULT_REG;
            if retcgsize=OS_F64 then
              setsubreg(paraloc^.register,R_SUBFD);
            paraloc^.size:=retcgsize;
          end
        else
         { Return in register }
          begin
{$ifndef cpu64bitalu}
            if retcgsize in [OS_64,OS_S64] then
             begin
               { high }
               paraloc^.loc:=LOC_REGISTER;
               if side=callerside then
                 paraloc^.register:=NR_FUNCTION_RESULT64_HIGH_REG
               else
                 paraloc^.register:=NR_FUNCTION_RETURN64_HIGH_REG;
               paraloc^.size:=OS_32;
               { low }
               paraloc:=result.add_location;
               paraloc^.loc:=LOC_REGISTER;
               if side=callerside then
                 paraloc^.register:=NR_FUNCTION_RESULT64_LOW_REG
               else
                 paraloc^.register:=NR_FUNCTION_RETURN64_LOW_REG;
               paraloc^.size:=OS_32;
             end
            else
{$endif cpu64bitalu}
             begin
               paraloc^.loc:=LOC_REGISTER;
               paraloc^.size:=retcgsize;
               if side=callerside then
                 paraloc^.register:=newreg(R_INTREGISTER,RS_FUNCTION_RESULT_REG,cgsize2subreg(R_INTREGISTER,retcgsize))
               else
                 paraloc^.register:=newreg(R_INTREGISTER,RS_FUNCTION_RETURN_REG,cgsize2subreg(R_INTREGISTER,retcgsize));
             end;
          end
      end;

    procedure TMIPSParaManager.create_paraloc_info_intern(p : tabstractprocdef; side: tcallercallee;paras:tparalist;
                                                           var intparareg,parasize:longint);
      var
        paraloc      : pcgparalocation;
        i            : integer;
        hp           : tparavarsym;
        paracgsize   : tcgsize;
        hparasupregs : pparasupregs;
        paralen      : longint;
	fpparareg    : integer;
	can_use_float : boolean;
	reg           : tsuperregister;
	alignment     : longint;
	tmp	      : longint;
      begin
        fpparareg := 0;
	can_use_float := true;
        if side=callerside then
          hparasupregs:=@paraoutsupregs
        else
          hparasupregs:=@parainsupregs;

        for i:=0 to paras.count-1 do
          begin

            hp:=tparavarsym(paras[i]);
            { currently only support C-style array of const,
              there should be no location assigned to the vararg array itself }
            if (p.proccalloption in [pocall_cdecl,pocall_cppdecl]) and
               is_array_of_const(hp.vardef) then
              begin
                paraloc:=hp.paraloc[side].add_location;
                { hack: the paraloc must be valid, but is not actually used }
                paraloc^.loc:=LOC_REGISTER;
                paraloc^.register:=NR_R0;
                paraloc^.size:=OS_ADDR;
		{ to check: intparareg? }
		can_use_float := false;
                break;
              end;

            if push_addr_param(hp.varspez,hp.vardef,p.proccalloption) then
              paracgsize:=OS_ADDR
            else
              begin
                paracgsize:=def_cgSize(hp.vardef);
                if paracgsize=OS_NO then
                  paracgsize:=OS_ADDR;
              end;
            hp.paraloc[side].reset;
            hp.paraloc[side].size:=paracgsize;
            paralen:=tcgsize2size[paracgsize];
            if (paralen > 4) then 
	      alignment := paralen
            else
	      alignment := 4;
            hp.paraloc[side].Alignment:=alignment;
	    { check the alignment, mips O32ABI require a nature alignment  }
	    tmp := align(parasize, alignment) - parasize;
	    while tmp > 0 do
              begin
                inc(intparareg);
	        inc(parasize,4);
                dec(tmp,4);
              end;
               
            hp.paraloc[side].intsize:=paralen;

	    { any non-float args will disable the use the floating regs }
	    { up to two fp args }
	    if (not(paracgsize in [OS_F32, OS_F64])) or (fpparareg = 2) then
              can_use_float := false;

            while paralen>0 do
              begin
                paraloc:=hp.paraloc[side].add_location;
                { We can allocate at maximum 32 bits per register }
                if (paracgsize in [OS_64,OS_S64]) or ((paracgsize in [OS_F32,OS_F64]) and not(can_use_float)) then
                  paraloc^.size:=OS_32
                else
                  paraloc^.size:=paracgsize;
                { ret in param? }
                if vo_is_funcret in hp.varoptions then
                  begin
                    paraloc^.loc:=LOC_REFERENCE;
                    if side=callerside then
                    begin
                      paraloc^.reference.index := NR_STACK_POINTER_REG;
                      paraloc^.reference.offset:=parasize;
                    end
                    else
                    begin
                      paraloc^.reference.index := NR_FRAME_POINTER_REG;
                      paraloc^.reference.offset:=target_info.first_parm_offset+parasize;
                      TMIPSProcinfo(current_procinfo).needs_frame_pointer := true;
                    end;
                    inc(parasize,align(tcgsize2size[paraloc^.size],sizeof(aint)));
		    inc(intparareg);
                  end
                { In case of po_delphi_nested_cc, the parent frame pointer
                  is always passed on the stack. }
                else if (intparareg<=high(tparasupregs)) and
                   (not(vo_is_parentfp in hp.varoptions) or
                    not(po_delphi_nested_cc in p.procoptions)) then
                  begin
		    if (can_use_float) then
                      begin
                        paraloc^.loc:=LOC_FPUREGISTER;
                        if (fpparareg = 0) then
                          reg := RS_F12
                        else
                          reg := RS_F14;
                        if (paraloc^.size = OS_F64) then
                          begin
                            paraloc^.register:=newreg(R_FPUREGISTER, reg, R_SUBFD);
			    inc(fpparareg);
			    inc(intparareg);
			    inc(intparareg);
			    inc(parasize,8);
                          end
                        else
                          begin
                            paraloc^.register:=newreg(R_FPUREGISTER, reg, R_SUBFS);
			    inc(fpparareg);
			    inc(intparareg);
			    inc(parasize,sizeof(aint));
                          end;
                      end
                    else
                      begin
                        paraloc^.loc:=LOC_REGISTER;
                        paraloc^.register:=newreg(R_INTREGISTER,hparasupregs^[intparareg],R_SUBWHOLE);
			inc(intparareg);
			inc(parasize,sizeof(aint));
                      end;
                  end
                else
                  begin
                    paraloc^.loc:=LOC_REFERENCE;
                    if side=callerside then
                      begin
                        paraloc^.reference.index := NR_STACK_POINTER_REG;
                        paraloc^.reference.offset:=parasize;
                      end
                    else
                      begin
                        paraloc^.reference.index := NR_FRAME_POINTER_REG;
                        paraloc^.reference.offset:=target_info.first_parm_offset+parasize;
                        TMIPSProcinfo(current_procinfo).needs_frame_pointer := true;
                      end;
                    inc(parasize,align(tcgsize2size[paraloc^.size],sizeof(aint)));
	    	    inc(intparareg);
                  end;
                dec(paralen,tcgsize2size[paraloc^.size]);
              end; { while }
          end; {for}
          if (parasize < 16) then
            parasize := 16;
      end;


    function TMIPSParaManager.create_varargs_paraloc_info(p : tabstractprocdef; varargspara:tvarargsparalist):longint;
      var
        intparareg,
        parasize : longint;
      begin
        intparareg:=0;
        parasize:=0;
        { calculate the registers for the normal parameters }
        create_paraloc_info_intern(p,callerside,p.paras,intparareg,parasize);
        { append the varargs }
        create_paraloc_info_intern(p,callerside,varargspara,intparareg,parasize);
        result:=parasize;
      end;



    function TMIPSParaManager.create_paraloc_info(p : tabstractprocdef; side: tcallercallee):longint;
      var
        intparareg,
        parasize : longint;
      begin
        intparareg:=0;
        parasize:=0;
        create_paraloc_info_intern(p,side,p.paras,intparareg,parasize);
        { Create Function result paraloc }
        create_funcretloc_info(p,side);
        { We need to return the size allocated on the stack }
        result:=parasize;
      end;


begin
   ParaManager:=TMIPSParaManager.create;
end.
