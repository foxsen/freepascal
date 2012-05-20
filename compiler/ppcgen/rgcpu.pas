{
    Copyright (c) 1998-2002 by Florian Klaempfl

    This unit implements the powerpc specific class for the register
    allocator

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

unit rgcpu;

{$i fpcdefs.inc}

  interface

     uses
       aasmbase,aasmtai,aasmdata,aasmcpu,
       cgbase,cgutils,
       cpubase,
       rgobj;

     type
       trgcpu = class(trgobj)
         procedure do_spill_read(list:TAsmList;pos:tai;const spilltemp:treference;tempreg:tregister);override;
         procedure do_spill_written(list:TAsmList;pos:tai;const spilltemp:treference;tempreg:tregister);override;
       end;

       trgintcpu = class(trgcpu)
{$ifdef user0}
         procedure add_cpu_interferences(p : tai);override;
{$endif user0}
       end;

  implementation

    uses
      verbose, cutils,globtype,
      cgobj,
      procinfo;


    procedure trgcpu.do_spill_read(list:TAsmList;pos:tai;const spilltemp:treference;tempreg:tregister);
      var
        tmpref : treference;
        helplist : TAsmList;
        hreg : tregister;
        ins : Taicpu;
      begin
        if (spilltemp.offset<low(smallint)) or
           (spilltemp.offset>high(smallint)) then
          begin
            helplist:=TAsmList.create;

            if (spilltemp.index<>NR_NO) then
              internalerror(200704201);

            if getregtype(tempreg)=R_INTREGISTER then
              begin
                hreg:=getregisterinline(helplist,[R_SUBWHOLE]);
                {Done by add_cpu_interferences now.
                add_edge(getsupreg(hreg),RS_R0);}
              end
            else
              hreg:=cg.getintregister(helplist,OS_ADDR);

            reference_reset(tmpref,sizeof(aint));
            tmpref.offset:=spilltemp.offset;
            tmpref.refaddr := addr_higha;
            ins:=taicpu.op_reg_reg_ref(A_ADDIS,hreg,spilltemp.base,tmpref);
            add_cpu_interferences(ins);
            helplist.concat(ins);
            tmpref:=spilltemp;
            tmpref.refaddr := addr_low;
            tmpref.base:=hreg;
	    
            ins:=spilling_create_load(tmpref,tempreg);
            add_cpu_interferences(ins);
	    
	    
            helplist.concat(ins);
	    
            if getregtype(tempreg)=R_INTREGISTER then
              ungetregisterinline(helplist,hreg);

            list.insertlistafter(pos,helplist);
            helplist.free;
          end
        else
          inherited do_spill_read(list,pos,spilltemp,tempreg);
      end;


    procedure trgcpu.do_spill_written(list:TAsmList;pos:tai;const spilltemp:treference;tempreg:tregister);
      var
        tmpref : treference;
        helplist : TAsmList;
        hreg : tregister;
        ins : Taicpu;
      begin
        if (spilltemp.offset<low(smallint)) or
           (spilltemp.offset>high(smallint)) then
          begin
            helplist:=TAsmList.create;

            if (spilltemp.index<>NR_NO) then
              internalerror(200704201);

            if getregtype(tempreg)=R_INTREGISTER then
              begin
                hreg:=getregisterinline(helplist,[R_SUBWHOLE]);
                {Done by add_cpu_interferences now.
                add_edge(getsupreg(hreg),RS_R0);}
              end
            else
              hreg:=cg.getintregister(helplist,OS_ADDR);
            reference_reset(tmpref,sizeof(aint));
            tmpref.offset:=spilltemp.offset;
            tmpref.refaddr := addr_higha;
            ins:=taicpu.op_reg_reg_ref(A_ADDIS,hreg,spilltemp.base,tmpref);
            add_cpu_interferences(ins);
            helplist.concat(ins);
            tmpref:=spilltemp;
            tmpref.refaddr := addr_low;
            tmpref.base:=hreg;
            ins:=spilling_create_store(tempreg,tmpref);
            add_cpu_interferences(ins);
            helplist.concat(ins);

            if getregtype(tempreg)=R_INTREGISTER then
              ungetregisterinline(helplist,hreg);

            list.insertlistafter(pos,helplist);
            helplist.free;
          end
        else
          inherited do_spill_written(list,pos,spilltemp,tempreg);
      end;

{$ifdef user0}
    procedure trgintcpu.add_cpu_interferences(p : tai);
      var
        r : tregister;
      begin
        if p.typ=ait_instruction then
          begin
            case taicpu(p).opcode of
              A_ADDI, A_ADDIS,
              A_STB, A_LBZ, A_STBX, A_LBZX, A_STH, A_LHZ, A_STHX, A_LHZX, A_LHA, A_LHAX,
              A_STW, A_LWZ, A_STWX, A_LWZX,
              A_STFS, A_LFS, A_STFSX, A_LFSX, A_STFD, A_LFD, A_STFDX, A_LFDX, A_STFIWX,
              A_STHBRX, A_LHBRX, A_STWBRX, A_LWBRX, A_STWCX_, A_LWARX,
              A_ECIWX, A_ECOWX,
              A_LMW, A_STMW,A_LSWI,A_LSWX,A_STSWI,A_STSWX
{$ifdef cpu64bitalu}
              , A_STD, A_STDX,
              A_LD, A_LDX,
              A_LWA, A_LWAX,
              A_STDCX_,A_LDARX
{$endif cpu64bitalu}
                :
                begin
                  case taicpu(p).oper[1]^.typ of
                    top_reg:
                      add_edge(getsupreg(taicpu(p).oper[1]^.reg),RS_R0);
                    top_ref:
                      if (taicpu(p).oper[1]^.ref^.base <> NR_NO) then
                        add_edge(getsupreg(taicpu(p).oper[1]^.ref^.base),RS_R0);
                  end;
                end;
              A_DCBA, A_DCBI, A_DCBST, A_DCBT, A_DCBTST, A_DCBZ, A_DCBF, A_ICBI:
                begin
                  case taicpu(p).oper[0]^.typ of
                    top_reg:
                      add_edge(getsupreg(taicpu(p).oper[0]^.reg),RS_R0);
                    top_ref:
                      if (taicpu(p).oper[0]^.ref^.base <> NR_NO) then
                        add_edge(getsupreg(taicpu(p).oper[1]^.ref^.base),RS_R0);
                  end;
                end;
            end;
          end;
      end;
{$endif user0}


end.
