{
    Copyright (c) 1998-2002 by Florian Klaempfl

    Generate i386 assembler for in memory related nodes

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
unit n386mem;

{$i fpcdefs.inc}

interface

    uses
      globtype,
      cgbase,cpuinfo,cpubase,
      node,nmem,ncgmem,nx86mem;

    type
       ti386addrnode = class(tcgaddrnode)
          procedure pass_generate_code;override;
       end;

       ti386derefnode = class(tcgderefnode)
          procedure pass_generate_code;override;
       end;

       ti386vecnode = class(tx86vecnode)
          procedure pass_generate_code;override;
       end;

implementation

    uses
      systems,
      cutils,verbose,
      symdef,paramgr,
      aasmtai,aasmdata,
      nld,ncon,nadd,
      cgutils,cgobj;

{*****************************************************************************
                             TI386ADDRNODE
*****************************************************************************}

    procedure ti386addrnode.pass_generate_code;

      begin
        inherited pass_generate_code;
        { for use of other segments, not used }
        {if left.location.reference.segment<>NR_NO then
          location.segment:=left.location.reference.segment;}
      end;


{*****************************************************************************
                           TI386DEREFNODE
*****************************************************************************}

    procedure ti386derefnode.pass_generate_code;
      begin
         inherited pass_generate_code;
         if tpointerdef(left.resultdef).is_far then
           location.reference.segment:=NR_FS;
      end;


{*****************************************************************************
                             TI386VECNODE
*****************************************************************************}

    procedure ti386vecnode.pass_generate_code;
      begin
        inherited pass_generate_code;
        if nf_memseg in flags then
          location.reference.segment:=NR_FS;
      end;


begin
   caddrnode:=ti386addrnode;
   cderefnode:=ti386derefnode;
   cvecnode:=ti386vecnode;
end.
