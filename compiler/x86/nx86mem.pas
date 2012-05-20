{
    Copyright (c) 1998-2002 by Florian Klaempfl

    Generate x86 assembler for in memory related nodes

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
unit nx86mem;

{$i fpcdefs.inc}

interface
    uses
      globtype,
      cgbase,cpuinfo,cpubase,
      node,nmem,ncgmem;

    type
      tx86vecnode = class(tcgvecnode)
        procedure update_reference_reg_mul(maybe_const_reg:tregister;l:aint);override;
      end;

implementation

    uses
      cutils,verbose,
      aasmtai,aasmdata,
      cgutils,cgobj;

{*****************************************************************************
                             TX86VECNODE
*****************************************************************************}

     { this routine must, like any other routine, not change the contents }
     { of base/index registers of references, as these may be regvars.    }
     { The register allocator can coalesce one LOC_REGISTER being moved   }
     { into another (as their live ranges won't overlap), but not a       }
     { LOC_CREGISTER moved into a LOC_(C)REGISTER most of the time (as    }
     { the live range of the LOC_CREGISTER will most likely overlap the   }
     { the live range of the target LOC_(C)REGISTER)                      }
     { The passed register may be a LOC_CREGISTER as well.                }
     procedure tx86vecnode.update_reference_reg_mul(maybe_const_reg:tregister;l:aint);
       var
         l2 : integer;
         hreg : tregister;
       begin
         { Optimized for x86 to use the index register and scalefactor }
         if location.reference.index=NR_NO then
          begin
            { no preparations needed }
          end
         else if location.reference.base=NR_NO then
          begin
            if (location.reference.scalefactor > 1) then
              hreg:=cg.getaddressregister(current_asmdata.CurrAsmList);
            case location.reference.scalefactor of
             0,1 : hreg:=location.reference.index;
             2 : cg.a_op_const_reg_reg(current_asmdata.CurrAsmList,OP_SHL,OS_ADDR,1,location.reference.index,hreg);
             4 : cg.a_op_const_reg_reg(current_asmdata.CurrAsmList,OP_SHL,OS_ADDR,2,location.reference.index,hreg);
             8 : cg.a_op_const_reg_reg(current_asmdata.CurrAsmList,OP_SHL,OS_ADDR,3,location.reference.index,hreg);
             else
               internalerror(2008091401);
            end;
            location.reference.base:=hreg;
          end
         else
          begin
            hreg:=cg.getaddressregister(current_asmdata.CurrAsmList);
            cg.a_loadaddr_ref_reg(current_asmdata.CurrAsmList,location.reference,hreg);
            reference_reset_base(location.reference,hreg,0,location.reference.alignment);
          end;
         { insert the new index register and scalefactor or
           do the multiplication manual }
         case l of
          1,2,4,8 :
            begin
              location.reference.scalefactor:=l;
              hreg:=maybe_const_reg;
            end;
         else
           begin
              hreg:=cg.getaddressregister(current_asmdata.CurrAsmList);
              if ispowerof2(l,l2) then
                cg.a_op_const_reg_reg(current_asmdata.CurrAsmList,OP_SHL,OS_ADDR,l2,maybe_const_reg,hreg)
              else
                cg.a_op_const_reg_reg(current_asmdata.CurrAsmList,OP_IMUL,OS_ADDR,l,maybe_const_reg,hreg);
           end;
         end;
         location.reference.index:=hreg;
       end;

begin
   cvecnode:=tx86vecnode;
end.
