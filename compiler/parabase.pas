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
unit parabase;

{$i fpcdefs.inc}

  interface

    uses
       cclasses,globtype,
       cpubase,cgbase,cgutils,
       symtype, ppu;

    type
       TCGParaReference = record
          index       : tregister;
          offset      : aint;
       end;

       PCGParaLocation = ^TCGParaLocation;
       TCGParaLocation = record
         Next : PCGParaLocation;
         Size : TCGSize; { size of this location }
         Loc  : TCGLoc;
         case TCGLoc of
           LOC_REFERENCE : (reference : TCGParaReference);
           LOC_FPUREGISTER,
           LOC_CFPUREGISTER,
           LOC_MMREGISTER,
           LOC_CMMREGISTER,
           LOC_REGISTER,
           LOC_CREGISTER : (
             {

             * If shiftval > 0:

             The number of bits the value in the register must be shifted to the left before
             it can be stored to memory in the function prolog.
             This is used for passing OS_NO memory blocks less than register size and of "odd"
             (3, 5, 6, 7) size on big endian machines, so that small memory blocks passed via
             registers are properly aligned.

             E.g. the value $5544433 is passed in bits 40-63 of the register (others are zero),
             but they should actually be stored in the first bits of the stack location reserved
             for this value. So they have to be shifted left by this amount of bits before.

             * if shiftval < 0:

             Similar as above, but the shifting must always be done and
               1) for all parameter sizes < regsize
               2) on the caller side
             }
             shiftval : shortint;
             register : tregister);
       end;

       TCGPara = object
          Location  : PCGParalocation;
          IntSize   : tcgint; { size of the total location in bytes }
          Alignment : ShortInt;
          Size      : TCGSize;  { Size of the parameter included in all locations }
          Def       : tdef; { Type of the parameter }
          DefDeref  : tderef;
{$ifdef powerpc}
          composite: boolean; { under the AIX abi, how certain parameters are passed depends on whether they are composite or not }
{$endif powerpc}
          constructor init;
          destructor  done;
          procedure   reset;
          function    getcopy:tcgpara;
          procedure   check_simple_location;
          function    add_location:pcgparalocation;
          procedure   get_location(var newloc:tlocation);

          procedure   buildderef;
          procedure   deref;
          procedure   ppuwrite(ppufile:tcompilerppufile);
          procedure   ppuload(ppufile:tcompilerppufile);
       end;

       tvarargsinfo = (
         va_uses_float_reg
       );

       tparalist = class(TFPObjectList)
          procedure SortParas;
       end;

       tvarargsparalist = class(tparalist)
          varargsinfo : set of tvarargsinfo;
{$ifdef x86_64}
          { x86_64 requires %al to contain the no. SSE regs passed }
          mmregsused  : longint;
{$endif x86_64}
       end;



implementation

    uses
      systems,verbose,
      symsym;


{****************************************************************************
                                TCGPara
****************************************************************************}

    constructor tcgpara.init;
      begin
        alignment:=0;
        size:=OS_NO;
        intsize:=0;
        location:=nil;
        def:=nil;
{$ifdef powerpc}
        composite:=false;
{$endif powerpc}
      end;


    destructor tcgpara.done;
      begin
        reset;
      end;


    procedure tcgpara.reset;
      var
        hlocation : pcgparalocation;
      begin
        while assigned(location) do
          begin
            hlocation:=location^.next;
            dispose(location);
            location:=hlocation;
          end;
        alignment:=0;
        size:=OS_NO;
        intsize:=0;
{$ifdef powerpc}
        composite:=false;
{$endif powerpc}
      end;


    function tcgpara.getcopy:tcgpara;
      var
        hlocation : pcgparalocation;
      begin
        result.init;
        while assigned(location) do
          begin
            hlocation:=result.add_location;
            hlocation^:=location^;
            hlocation^.next:=nil;
            location:=location^.next;
          end;
        result.alignment:=alignment;
        result.size:=size;
        result.intsize:=intsize;
{$ifdef powerpc}
        result.composite:=composite;
{$endif powerpc}
      end;


    function tcgpara.add_location:pcgparalocation;
      var
        prevlocation,
        hlocation : pcgparalocation;
      begin
        prevlocation:=nil;
        hlocation:=location;
        while assigned(hlocation) do
          begin
            prevlocation:=hlocation;
            hlocation:=hlocation^.next;
          end;
        new(hlocation);
        Fillchar(hlocation^,sizeof(tcgparalocation),0);
        if assigned(prevlocation) then
          prevlocation^.next:=hlocation
        else
          location:=hlocation;
        result:=hlocation;
      end;


    procedure tcgpara.check_simple_location;
      begin
        if not assigned(location) then
          internalerror(200408161);
        if assigned(location^.next) then
          internalerror(200408162);
      end;


    procedure tcgpara.get_location(var newloc:tlocation);
      begin
        if not assigned(location) then
          internalerror(200408205);
        fillchar(newloc,sizeof(newloc),0);
        newloc.loc:=location^.loc;
        newloc.size:=size;
        case location^.loc of
          LOC_REGISTER :
            begin
{$ifndef cpu64bitalu}
              if size in [OS_64,OS_S64] then
                begin
                  if not assigned(location^.next) then
                    internalerror(200408206);
                  if (location^.next^.loc<>LOC_REGISTER) then
                    internalerror(200408207);
                  if (target_info.endian = ENDIAN_BIG) then
                    begin
                      newloc.register64.reghi:=location^.register;
                      newloc.register64.reglo:=location^.next^.register;
                    end
                  else
                    begin
                      newloc.register64.reglo:=location^.register;
                      newloc.register64.reghi:=location^.next^.register;
                    end;
                end
              else
{$endif}
                newloc.register:=location^.register;
            end;
          LOC_FPUREGISTER,
          LOC_MMREGISTER :
            newloc.register:=location^.register;
          LOC_REFERENCE :
            begin
              newloc.reference.base:=location^.reference.index;
              newloc.reference.offset:=location^.reference.offset;
              newloc.reference.alignment:=alignment;
            end;
        end;
      end;


    procedure TCGPara.buildderef;
      begin
        defderef.build(def);
      end;


    procedure TCGPara.deref;
      begin
        def:=tdef(defderef.resolve);
      end;


    procedure TCGPara.ppuwrite(ppufile: tcompilerppufile);
      var
        hparaloc: PCGParaLocation;
        nparaloc: byte;
      begin
        ppufile.putbyte(byte(Alignment));
        ppufile.putbyte(ord(Size));
        ppufile.putaint(IntSize);
{$ifdef powerpc}
        ppufile.putbyte(byte(composite));
{$endif}
        ppufile.putderef(defderef);
        nparaloc:=0;
        hparaloc:=location;
        while assigned(hparaloc) do
          begin
            inc(nparaloc);
            hparaloc:=hparaloc^.Next;
          end;
        ppufile.putbyte(nparaloc);
        hparaloc:=location;
        while assigned(hparaloc) do
          begin
            ppufile.putbyte(byte(hparaloc^.Size));
            ppufile.putbyte(byte(hparaloc^.loc));
            case hparaloc^.loc of
              LOC_REFERENCE:
                begin
                  ppufile.putlongint(longint(hparaloc^.reference.index));
                  ppufile.putaint(hparaloc^.reference.offset);
                end;
              LOC_FPUREGISTER,
              LOC_CFPUREGISTER,
              LOC_MMREGISTER,
              LOC_CMMREGISTER,
              LOC_REGISTER,
              LOC_CREGISTER :
                begin
                  ppufile.putbyte(hparaloc^.shiftval);
                  ppufile.putlongint(longint(hparaloc^.register));
                end;
              { This seems to be required for systems using explicitparaloc (eg. MorphOS)
                or otherwise it hits the internalerror below. I don't know if this is
                the proper way to fix this, someone else with clue might want to take a
                look. The compiler cycles on the affected systems with this enabled. (KB) }
              LOC_VOID:
                begin end
              else
                internalerror(2010053115);
            end;
            hparaloc:=hparaloc^.next;
          end;
      end;


    procedure TCGPara.ppuload(ppufile: tcompilerppufile);
      var
        hparaloc: PCGParaLocation;
        nparaloc: byte;
      begin
        reset;
        Alignment:=shortint(ppufile.getbyte);
        Size:=TCgSize(ppufile.getbyte);
        IntSize:=ppufile.getaint;
{$ifdef powerpc}
        composite:=boolean(ppufile.getbyte);
{$endif}
        ppufile.getderef(defderef);
        nparaloc:=ppufile.getbyte;
        while nparaloc>0 do
          begin
            hparaloc:=add_location;
            hparaloc^.size:=TCGSize(ppufile.getbyte);
            hparaloc^.loc:=TCGLoc(ppufile.getbyte);
            case hparaloc^.loc of
              LOC_REFERENCE:
                begin
                  hparaloc^.reference.index:=tregister(ppufile.getlongint);
                  hparaloc^.reference.offset:=ppufile.getaint;
                end;
              LOC_FPUREGISTER,
              LOC_CFPUREGISTER,
              LOC_MMREGISTER,
              LOC_CMMREGISTER,
              LOC_REGISTER,
              LOC_CREGISTER :
                begin
                  hparaloc^.shiftval:=ppufile.getbyte;
                  hparaloc^.register:=tregister(ppufile.getlongint);
                end;
              { This seems to be required for systems using explicitparaloc (eg. MorphOS)
                or otherwise it hits the internalerror below. I don't know if this is
                the proper way to fix this, someone else with clue might want to take a
                look. The compiler cycles on the affected systems with this enabled. (KB) }
              LOC_VOID:
                begin end
              else
                internalerror(2010051301);
            end;
            dec(nparaloc);
          end;
      end;


{****************************************************************************
                          TParaList
****************************************************************************}

    function ParaNrCompare(Item1, Item2: Pointer): Integer;
      var
        I1 : tparavarsym absolute Item1;
        I2 : tparavarsym absolute Item2;
      begin
        Result:=longint(I1.paranr)-longint(I2.paranr);
      end;


    procedure TParaList.SortParas;
      begin
        Sort(@ParaNrCompare);
      end;


end.
