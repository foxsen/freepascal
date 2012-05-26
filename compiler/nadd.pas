{
    Copyright (c) 1998-2002 by Florian Klaempfl

    Type checking and simplification for add nodes

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
unit nadd;

{$i fpcdefs.inc}

{ define addstringopt}

interface

    uses
      node,symtype;

    type
       taddnode = class(tbinopnode)
       private
          resultrealdefderef: tderef;
          function pass_typecheck_internal:tnode;
       public
          resultrealdef : tdef;
          constructor create(tt : tnodetype;l,r : tnode);override;
          constructor ppuload(t:tnodetype;ppufile:tcompilerppufile);override;
          procedure ppuwrite(ppufile:tcompilerppufile);override;
          procedure buildderefimpl;override;
          procedure derefimpl;override;
          function pass_1 : tnode;override;
          function pass_typecheck:tnode;override;
          function simplify(forinline: boolean) : tnode;override;
          function dogetcopy : tnode;override;
          function docompare(p: tnode): boolean; override;
    {$ifdef state_tracking}
          function track_state_pass(exec_known:boolean):boolean;override;
    {$endif}
         protected
          { override the following if you want to implement }
          { parts explicitely in the code generator (JM)    }
          function first_addstring: tnode; virtual;
          function first_addset: tnode; virtual;
          { only implements "muln" nodes, the rest always has to be done in }
          { the code generator for performance reasons (JM)                 }
          function first_add64bitint: tnode; virtual;

          { override and return false if you can handle 32x32->64 }
          { bit multiplies directly in your code generator. If    }
          { this function is overridden to return false, you can  }
          { get multiplies with left/right both s32bit or u32bit, }
          { and resultdef of the muln s64bit or u64bit           }
          function use_generic_mul32to64: boolean; virtual;

          { This routine calls internal runtime library helpers
            for all floating point arithmetic in the case
            where the emulation switches is on. Otherwise
            returns nil, and everything must be done in
            the code generation phase.
          }
          function first_addfloat : tnode; virtual;
         private
           { checks whether a muln can be calculated as a 32bit }
           { * 32bit -> 64 bit                                  }
           function try_make_mul32to64: boolean;
           { Match against the ranges, i.e.:
             var a:1..10;
             begin
               if a>0 then
                 ...
             always evaluates to true. (DM)
           }
           function cmp_of_disjunct_ranges(var res : boolean) : boolean;
       end;
       taddnodeclass = class of taddnode;

    var
       { caddnode is used to create nodes of the add type }
       { the virtual constructor allows to assign         }
       { another class type to caddnode => processor      }
       { specific node types can be created               }
       caddnode : taddnodeclass = taddnode;

implementation

    uses
{$IFNDEF USE_FAKE_SYSUTILS}
      sysutils,
{$ELSE}
      fksysutl,
{$ENDIF}
      globtype,systems,constexp,
      cutils,verbose,globals,widestr,
      symconst,symdef,symsym,symtable,defutil,defcmp,
      cgbase,
      htypechk,pass_1,
      nld,nbas,nmat,ncnv,ncon,nset,nopt,ncal,ninl,nmem,nutils,
      {$ifdef state_tracking}
      nstate,
      {$endif}
      cpuinfo,procinfo;


{*****************************************************************************
                                TADDNODE
*****************************************************************************}

{$maxfpuregisters 0}

    function getbestreal(t1,t2 : tdef) : tdef;
      const
        floatweight : array[tfloattype] of byte =
          (2,3,4,5,0,1,6);
      begin
        if t1.typ=floatdef then
          begin
            result:=t1;
            if t2.typ=floatdef then
              begin
                { when a comp or currency is used, use always the
                  best float type to calculate the result }
                if (tfloatdef(t2).floattype in [s64comp,s64currency]) or
                  (tfloatdef(t2).floattype in [s64comp,s64currency]) then
                  result:=pbestrealtype^
                else
                  if floatweight[tfloatdef(t2).floattype]>floatweight[tfloatdef(t1).floattype] then
                    result:=t2;
              end;
          end
        else if t2.typ=floatdef then
          result:=t2
        else internalerror(200508061);
      end;


    constructor taddnode.create(tt : tnodetype;l,r : tnode);
      begin
         inherited create(tt,l,r);
      end;


    constructor taddnode.ppuload(t: tnodetype; ppufile: tcompilerppufile);
      begin
        inherited ppuload(t, ppufile);
        ppufile.getderef(resultrealdefderef);
      end;


    procedure taddnode.ppuwrite(ppufile: tcompilerppufile);
      begin
        inherited ppuwrite(ppufile);
         ppufile.putderef(resultrealdefderef);
      end;


    procedure taddnode.buildderefimpl;
      begin
        inherited buildderefimpl;
        resultrealdefderef.build(resultrealdef);
      end;


    procedure taddnode.derefimpl;
      begin
        inherited derefimpl;
        resultrealdef:=tdef(resultrealdefderef.resolve);
      end;


    function taddnode.cmp_of_disjunct_ranges(var res : boolean) : boolean;
      var
        hp          : tnode;
        realdef     : tdef;
        v           : tconstexprint;
      begin
        result:=false;
        { check for comparision with known result because the ranges of the operands don't overlap }
        if (is_constintnode(right) and (left.resultdef.typ=orddef) and
            { don't ignore type checks }
            is_subequal(right.resultdef,left.resultdef)) or
           (is_constintnode(left) and (right.resultdef.typ=orddef) and
            { don't ignore type checks }
            is_subequal(left.resultdef,right.resultdef)) then
           begin
             if is_constintnode(right) then
               begin
                 hp:=left;
                 v:=Tordconstnode(right).value;
               end
             else
               begin
                 hp:=right;
                 v:=Tordconstnode(left).value;
               end;

             realdef:=hp.resultdef;
             { stop with finding the real def when we either encounter
                a) an explicit type conversion (then the value has to be
                   re-interpreted)
                b) an "absolute" type conversion (also requires
                   re-interpretation)
             }
             while (hp.nodetype=typeconvn) and
                   ([nf_internal,nf_explicit,nf_absolute] * hp.flags = []) do
               begin
                 hp:=ttypeconvnode(hp).left;
                 realdef:=hp.resultdef;
               end;
             if is_constintnode(left) then
               with torddef(realdef) do
                 case nodetype of
                  ltn:
                    if v<low then
                      begin
                        result:=true;
                        res:=true;
                      end
                    else if v>=high then
                      begin
                        result:=true;
                        res:=false;
                      end;
                  lten:
                    if v<=low then
                      begin
                        result:=true;
                        res:=true;
                      end
                    else if v>high then
                      begin
                        result:=true;
                        res:=false;
                      end;
                  gtn:
                    if v<=low then
                      begin
                        result:=true;
                        res:=false;
                      end
                    else if v>high then
                      begin
                        result:=true;
                        res:=true;
                      end;
                  gten :
                    if v<low then
                      begin
                        result:=true;
                        res:=false;
                      end
                    else if v>=high then
                      begin
                        result:=true;
                        res:=true;
                      end;
                  equaln:
                    if (v<low) or (v>high) then
                      begin
                        result:=true;
                        res:=false;
                      end;
                  unequaln:
                    if (v<low) or (v>high) then
                      begin
                        result:=true;
                        res:=true;
                      end;
                 end
             else
               with torddef(realdef) do
                 case nodetype of
                  ltn:
                    if high<v then
                      begin
                        result:=true;
                        res:=true;
                      end
                    else if low>=v then
                      begin
                        result:=true;
                        res:=false;
                      end;
                  lten:
                    if high<=v then
                      begin
                        result:=true;
                        res:=true;
                      end
                    else if low>v then
                      begin
                        result:=true;
                        res:=false;
                      end;
                  gtn:
                    if high<=v then
                      begin
                        result:=true;
                        res:=false;
                      end
                    else if low>v then
                      begin
                        result:=true;
                        res:=true;
                      end;
                  gten:
                    if high<v then
                      begin
                        result:=true;
                        res:=false;
                      end
                    else if low>=v then
                      begin
                        result:=true;
                        res:=true;
                      end;
                  equaln:
                    if (v<low) or (v>high) then
                      begin
                        result:=true;
                        res:=false;
                      end;
                  unequaln:
                    if (v<low) or (v>high) then
                      begin
                        result:=true;
                        res:=true;
                      end;
                 end;
           end;
      end;


    function taddnode.simplify(forinline : boolean) : tnode;
      var
        t       : tnode;
        lt,rt   : tnodetype;
        rd,ld   : tdef;
        rv,lv,v : tconstexprint;
        rvd,lvd : bestreal;
        ws1,ws2 : pcompilerwidestring;
        concatstrings : boolean;
        c1,c2   : array[0..1] of char;
        s1,s2   : pchar;
        l1,l2   : longint;
        resultset : Tconstset;
        res,
        b       : boolean;
      begin
        result:=nil;

        { load easier access variables }
        rd:=right.resultdef;
        ld:=left.resultdef;
        rt:=right.nodetype;
        lt:=left.nodetype;

        if (nodetype = slashn) and
           (((rt = ordconstn) and
             (tordconstnode(right).value = 0)) or
            ((rt = realconstn) and
             (trealconstnode(right).value_real = 0.0))) then
          begin
            if floating_point_range_check_error then
               begin
                 result:=crealconstnode.create(1,pbestrealtype^);
                 Message(parser_e_division_by_zero);
                 exit;
               end;
          end;

        { both are int constants }
        if (
            (
             is_constintnode(left) and
             is_constintnode(right)
            ) or
            (
             is_constboolnode(left) and
             is_constboolnode(right) and
             (nodetype in [slashn,ltn,lten,gtn,gten,equaln,unequaln,andn,xorn,orn])
            ) or
            (
             is_constenumnode(left) and
             is_constenumnode(right) and
             allowenumop(nodetype))
            ) or
            (
             (lt = pointerconstn) and
             is_constintnode(right) and
             (nodetype in [addn,subn])
            ) or
            (
             (lt in [pointerconstn,niln]) and
             (rt in [pointerconstn,niln]) and
             (nodetype in [ltn,lten,gtn,gten,equaln,unequaln,subn])
            ) then
          begin
             t:=nil;

             { load values }
             case lt of
               ordconstn:
                 lv:=tordconstnode(left).value;
               pointerconstn:
                 lv:=tpointerconstnode(left).value;
               niln:
                 lv:=0;
               else
                 internalerror(2002080202);
             end;
             case rt of
               ordconstn:
                 rv:=tordconstnode(right).value;
               pointerconstn:
                 rv:=tpointerconstnode(right).value;
               niln:
                 rv:=0;
               else
                 internalerror(2002080203);
             end;
             { type checking already took care of multiplying      }
             { integer constants with pointeddef.size if necessary }
             case nodetype of
               addn :
                 begin
                   v:=lv+rv;
                   if v.overflow then
                     begin
                       Message(parser_e_arithmetic_operation_overflow);
                       { Recover }
                       t:=genintconstnode(0)
                     end
                   else if (lt=pointerconstn) then
                     t := cpointerconstnode.create(qword(v),resultdef)
                   else
                     if is_integer(ld) then
                       t := create_simplified_ord_const(v,resultdef,forinline)
                     else
                       t := cordconstnode.create(v,resultdef,(ld.typ<>enumdef));
                 end;
               subn :
                 begin
                   v:=lv-rv;
                   if v.overflow then
                     begin
                       Message(parser_e_arithmetic_operation_overflow);
                       { Recover }
                       t:=genintconstnode(0)
                     end
                   else if (lt=pointerconstn) then
                     { pointer-pointer results in an integer }
                     if (rt=pointerconstn) then
                       begin
                         if not(nf_has_pointerdiv in flags) then
                           internalerror(2008030101);
                         t := cpointerconstnode.create(qword(v),resultdef)
                       end
                     else
                       t := cpointerconstnode.create(qword(v),resultdef)
                   else
                     if is_integer(ld) then
                       t := create_simplified_ord_const(v,resultdef,forinline)
                     else
                       t:=cordconstnode.create(v,resultdef,(ld.typ<>enumdef));
                 end;
               muln :
                 begin
                   v:=lv*rv;
                   if v.overflow then
                     begin
                       message(parser_e_arithmetic_operation_overflow);
                       { Recover }
                       t:=genintconstnode(0)
                     end
                   else
                     t := create_simplified_ord_const(v,resultdef,forinline)
                 end;
               xorn :
                 if is_integer(ld) then
                   t := create_simplified_ord_const(lv xor rv,resultdef,forinline)
                 else
                   t:=cordconstnode.create(lv xor rv,resultdef,true);
               orn :
                 if is_integer(ld) then
                   t:=create_simplified_ord_const(lv or rv,resultdef,forinline)
                 else
                   t:=cordconstnode.create(lv or rv,resultdef,true);
               andn :
                 if is_integer(ld) then
                   t:=create_simplified_ord_const(lv and rv,resultdef,forinline)
                 else
                   t:=cordconstnode.create(lv and rv,resultdef,true);
               ltn :
                 t:=cordconstnode.create(ord(lv<rv),pasbool8type,true);
               lten :
                 t:=cordconstnode.create(ord(lv<=rv),pasbool8type,true);
               gtn :
                 t:=cordconstnode.create(ord(lv>rv),pasbool8type,true);
               gten :
                 t:=cordconstnode.create(ord(lv>=rv),pasbool8type,true);
               equaln :
                 t:=cordconstnode.create(ord(lv=rv),pasbool8type,true);
               unequaln :
                 t:=cordconstnode.create(ord(lv<>rv),pasbool8type,true);
               slashn :
                 begin
                   { int/int becomes a real }
                   rvd:=rv;
                   lvd:=lv;
                   t:=crealconstnode.create(lvd/rvd,resultrealdef);
                 end;
               else
                 internalerror(2008022101);
             end;
             result:=t;
             exit;
          end
        else if cmp_of_disjunct_ranges(res) then
          begin
            if res then
              t:=Cordconstnode.create(1,pasbool8type,true)
            else
              t:=Cordconstnode.create(0,pasbool8type,true);
              { don't do this optimization, if the variable expression might
                have a side effect }
              if (is_constintnode(left) and might_have_sideeffects(right)) or
                (is_constintnode(right) and might_have_sideeffects(left)) then
                t.free
              else
                result:=t;
              exit;
          end;

        { Add,Sub,Mul with constant 0, 1 or -1?  }
        if is_constintnode(right) and is_integer(left.resultdef) then
          begin
            if tordconstnode(right).value = 0 then
              begin
                case nodetype of
                  addn,subn:
                   result := left.getcopy;
                  muln:
                   result:=cordconstnode.create(0,resultdef,true);
                end;
              end
            else if tordconstnode(right).value = 1 then
              begin
                case nodetype of
                  muln:
                   result := left.getcopy;
                end;
              end
{$ifdef VER2_2}
            else if (tordconstnode(right).value.svalue = -1) and (tordconstnode(right).value.signed) then
{$else}
            else if tordconstnode(right).value = -1 then
{$endif}
              begin
                case nodetype of
                  muln:
                   result := cunaryminusnode.create(left.getcopy);
                end;
              end;
            if assigned(result) then
              exit;
          end;
        if is_constintnode(left) and is_integer(right.resultdef) then
          begin
            if tordconstnode(left).value = 0 then
              begin
                case nodetype of
                  addn:
                   result := right.getcopy;
                  subn:
                   result := cunaryminusnode.create(right.getcopy);
                  muln:
                   result:=cordconstnode.create(0,right.resultdef,true);
                end;
              end
            else if tordconstnode(left).value = 1 then
              begin
                case nodetype of
                  muln:
                   result := right.getcopy;
                end;
              end
{$ifdef VER2_2}
            else if (tordconstnode(left).value.svalue = -1) and (tordconstnode(left).value.signed) then
{$else}
            else if tordconstnode(left).value = -1 then
{$endif}
              begin
                case nodetype of
                  muln:
                   result := cunaryminusnode.create(right.getcopy);
                end;
              end;
            if assigned(result) then
              exit;
          end;

      { both real constants ? }
        if (lt=realconstn) and (rt=realconstn) then
          begin
             lvd:=trealconstnode(left).value_real;
             rvd:=trealconstnode(right).value_real;
             case nodetype of
                addn :
                  t:=crealconstnode.create(lvd+rvd,resultrealdef);
                subn :
                  t:=crealconstnode.create(lvd-rvd,resultrealdef);
                muln :
                  t:=crealconstnode.create(lvd*rvd,resultrealdef);
                starstarn:
                  begin
                    if lvd<0 then
                     begin
                       Message(parser_e_invalid_float_operation);
                       t:=crealconstnode.create(0,resultrealdef);
                     end
                    else if lvd=0 then
                      t:=crealconstnode.create(1.0,resultrealdef)
                    else
                      t:=crealconstnode.create(exp(ln(lvd)*rvd),resultrealdef);
                  end;
                slashn :
                  t:=crealconstnode.create(lvd/rvd,resultrealdef);
                ltn :
                  t:=cordconstnode.create(ord(lvd<rvd),pasbool8type,true);
                lten :
                  t:=cordconstnode.create(ord(lvd<=rvd),pasbool8type,true);
                gtn :
                  t:=cordconstnode.create(ord(lvd>rvd),pasbool8type,true);
                gten :
                  t:=cordconstnode.create(ord(lvd>=rvd),pasbool8type,true);
                equaln :
                  t:=cordconstnode.create(ord(lvd=rvd),pasbool8type,true);
                unequaln :
                  t:=cordconstnode.create(ord(lvd<>rvd),pasbool8type,true);
                else
                  internalerror(2008022102);
             end;
             result:=t;
             exit;
          end;

        { first, we handle widestrings, so we can check later for }
        { stringconstn only                                       }

        { widechars are converted above to widestrings too }
        { this isn't ver y efficient, but I don't think    }
        { that it does matter that much (FK)               }
        if (lt=stringconstn) and (rt=stringconstn) and
          (tstringconstnode(left).cst_type in [cst_widestring,cst_unicodestring]) and
          (tstringconstnode(right).cst_type in [cst_widestring,cst_unicodestring]) then
          begin
             initwidestring(ws1);
             initwidestring(ws2);
             copywidestring(pcompilerwidestring(tstringconstnode(left).value_str),ws1);
             copywidestring(pcompilerwidestring(tstringconstnode(right).value_str),ws2);
             case nodetype of
                addn :
                  begin
                     concatwidestrings(ws1,ws2);
                     t:=cstringconstnode.createunistr(ws1);
                  end;
                ltn :
                  t:=cordconstnode.create(byte(comparewidestrings(ws1,ws2)<0),pasbool8type,true);
                lten :
                  t:=cordconstnode.create(byte(comparewidestrings(ws1,ws2)<=0),pasbool8type,true);
                gtn :
                  t:=cordconstnode.create(byte(comparewidestrings(ws1,ws2)>0),pasbool8type,true);
                gten :
                  t:=cordconstnode.create(byte(comparewidestrings(ws1,ws2)>=0),pasbool8type,true);
                equaln :
                  t:=cordconstnode.create(byte(comparewidestrings(ws1,ws2)=0),pasbool8type,true);
                unequaln :
                  t:=cordconstnode.create(byte(comparewidestrings(ws1,ws2)<>0),pasbool8type,true);
                else
                  internalerror(2008022103);
             end;
             donewidestring(ws1);
             donewidestring(ws2);
             result:=t;
             exit;
          end;

        { concating strings ? }
        concatstrings:=false;

        if (lt=ordconstn) and (rt=ordconstn) and
           is_char(ld) and is_char(rd) then
          begin
             c1[0]:=char(int64(tordconstnode(left).value));
             c1[1]:=#0;
             l1:=1;
             c2[0]:=char(int64(tordconstnode(right).value));
             c2[1]:=#0;
             l2:=1;
             s1:=@c1[0];
             s2:=@c2[0];
             concatstrings:=true;
          end
        else if (lt=stringconstn) and (rt=ordconstn) and is_char(rd) then
          begin
             s1:=tstringconstnode(left).value_str;
             l1:=tstringconstnode(left).len;
             c2[0]:=char(int64(tordconstnode(right).value));
             c2[1]:=#0;
             s2:=@c2[0];
             l2:=1;
             concatstrings:=true;
          end
        else if (lt=ordconstn) and (rt=stringconstn) and is_char(ld) then
          begin
             c1[0]:=char(int64(tordconstnode(left).value));
             c1[1]:=#0;
             l1:=1;
             s1:=@c1[0];
             s2:=tstringconstnode(right).value_str;
             l2:=tstringconstnode(right).len;
             concatstrings:=true;
          end
        else if (lt=stringconstn) and (rt=stringconstn) then
          begin
             s1:=tstringconstnode(left).value_str;
             l1:=tstringconstnode(left).len;
             s2:=tstringconstnode(right).value_str;
             l2:=tstringconstnode(right).len;
             concatstrings:=true;
          end;
        if concatstrings then
          begin
             case nodetype of
                addn :
                  begin
                    t:=cstringconstnode.createpchar(concatansistrings(s1,s2,l1,l2),l1+l2);
                    typecheckpass(t);
                    tstringconstnode(t).changestringtype(resultdef);
                  end;
                ltn :
                  t:=cordconstnode.create(byte(compareansistrings(s1,s2,l1,l2)<0),pasbool8type,true);
                lten :
                  t:=cordconstnode.create(byte(compareansistrings(s1,s2,l1,l2)<=0),pasbool8type,true);
                gtn :
                  t:=cordconstnode.create(byte(compareansistrings(s1,s2,l1,l2)>0),pasbool8type,true);
                gten :
                  t:=cordconstnode.create(byte(compareansistrings(s1,s2,l1,l2)>=0),pasbool8type,true);
                equaln :
                  t:=cordconstnode.create(byte(compareansistrings(s1,s2,l1,l2)=0),pasbool8type,true);
                unequaln :
                  t:=cordconstnode.create(byte(compareansistrings(s1,s2,l1,l2)<>0),pasbool8type,true);
                else
                  internalerror(2008022104);
             end;
             result:=t;
             exit;
          end;

        { set constant evaluation }
        if (right.nodetype=setconstn) and
           not assigned(tsetconstnode(right).left) and
           (left.nodetype=setconstn) and
           not assigned(tsetconstnode(left).left) then
          begin
             case nodetype of
               addn :
                 begin
                   resultset:=tsetconstnode(right).value_set^ + tsetconstnode(left).value_set^;
                   t:=csetconstnode.create(@resultset,resultdef);
                 end;
                muln :
                  begin
                    resultset:=tsetconstnode(right).value_set^ * tsetconstnode(left).value_set^;
                    t:=csetconstnode.create(@resultset,resultdef);
                  end;
               subn :
                  begin
                    resultset:=tsetconstnode(left).value_set^ - tsetconstnode(right).value_set^;
                            t:=csetconstnode.create(@resultset,resultdef);
                  end;
               symdifn :
                  begin
                    resultset:=tsetconstnode(right).value_set^ >< tsetconstnode(left).value_set^;
                        t:=csetconstnode.create(@resultset,resultdef);
                  end;
               unequaln :
                  begin
                    b:=tsetconstnode(right).value_set^ <> tsetconstnode(left).value_set^;
                    t:=cordconstnode.create(byte(b),pasbool8type,true);
                  end;
               equaln :
                  begin
                    b:=tsetconstnode(right).value_set^ = tsetconstnode(left).value_set^;
                    t:=cordconstnode.create(byte(b),pasbool8type,true);
                  end;
               lten :
                  begin
                    b:=tsetconstnode(left).value_set^ <= tsetconstnode(right).value_set^;
                    t:=cordconstnode.create(byte(b),pasbool8type,true);
                  end;
               gten :
                  begin
                    b:=tsetconstnode(left).value_set^ >= tsetconstnode(right).value_set^;
                    t:=cordconstnode.create(byte(b),pasbool8type,true);
                  end;
                else
                  internalerror(2008022105);
             end;
             result:=t;
             exit;
          end;

        { slow simplifications }
        if (cs_opt_level2 in current_settings.optimizerswitches) then
          begin
            { the comparison is might be expensive and the nodes are usually only
              equal if some previous optimizations were done so don't check
              this simplification always
            }
            if is_boolean(left.resultdef) and is_boolean(right.resultdef) and
               { even when short circuit boolean evaluation is active, this
                 optimization cannot be performed in case the node has
                 side effects, because this can change the result (e.g., in an
                 or-node that calls the same function twice and first returns
                 false and then true because of a global state change }
               not might_have_sideeffects(left) then
              begin
                if left.isequal(right) then
                  begin
                    case nodetype of
                      andn,orn:
                        begin
                          result:=left;
                          left:=nil;
                          exit;
                        end;
                      {
                      xorn:
                        begin
                          result:=cordconstnode.create(0,resultdef,true);
                          exit;
                        end;
                      }
                    end;
                  end;
              end;

            { using sqr(x) for reals instead of x*x might reduces register pressure and/or
              memory accesses while sqr(<real>) has no drawback }
            if
{$ifdef cpufpemu}
               (current_settings.fputype<>fpu_soft) and
               not(cs_fp_emulation in current_settings.moduleswitches) and
{$endif cpufpemu}
               (nodetype=muln) and
               is_real(left.resultdef) and is_real(right.resultdef) and
               left.isequal(right) and
               not(might_have_sideeffects(left)) then
              begin
                result:=cinlinenode.create(in_sqr_real,false,left);
                left:=nil;
                exit;
              end;
{$ifdef cpurox}
            { optimize (i shl x) or (i shr (bitsizeof(i)-x)) into rol(x,i) (and different flavours with shl/shr swapped etc.) }
            if (nodetype=orn)
{$ifndef cpu64bitalu}
               and (left.resultdef.typ=orddef) and
               not(torddef(left.resultdef).ordtype in [s64bit,u64bit,scurrency])
{$endif cpu64bitalu}
              then
              begin
                if (left.nodetype=shrn) and (right.nodetype=shln) and
                   is_constintnode(tshlshrnode(left).right) and
                   is_constintnode(tshlshrnode(right).right) and
                   (tordconstnode(tshlshrnode(right).right).value>0) and
                   (tordconstnode(tshlshrnode(left).right).value>0) and
                   tshlshrnode(left).left.isequal(tshlshrnode(right).left) and
                   not(might_have_sideeffects(tshlshrnode(left).left)) then
                   begin
                     if tordconstnode(tshlshrnode(left).right).value=
                       tshlshrnode(left).left.resultdef.size*8-tordconstnode(tshlshrnode(right).right).value then
                       begin
                         result:=cinlinenode.create(in_ror_x_y,false,
                           ccallparanode.create(tshlshrnode(left).right,
                           ccallparanode.create(tshlshrnode(left).left,nil)));
                         tshlshrnode(left).left:=nil;
                         tshlshrnode(left).right:=nil;
                         exit;
                       end
                     else if tordconstnode(tshlshrnode(right).right).value=
                       tshlshrnode(left).left.resultdef.size*8-tordconstnode(tshlshrnode(left).right).value then
                       begin
                         result:=cinlinenode.create(in_rol_x_y,false,
                           ccallparanode.create(tshlshrnode(right).right,
                           ccallparanode.create(tshlshrnode(left).left,nil)));
                         tshlshrnode(left).left:=nil;
                         tshlshrnode(right).right:=nil;
                         exit;
                       end;
                   end;
                if (left.nodetype=shln) and (right.nodetype=shrn) and
                   is_constintnode(tshlshrnode(left).right) and
                   is_constintnode(tshlshrnode(right).right) and
                   (tordconstnode(tshlshrnode(right).right).value>0) and
                   (tordconstnode(tshlshrnode(left).right).value>0) and
                   tshlshrnode(left).left.isequal(tshlshrnode(right).left) and
                   not(might_have_sideeffects(tshlshrnode(left).left)) then
                   begin
                     if tordconstnode(tshlshrnode(left).right).value=
                       tshlshrnode(left).left.resultdef.size*8-tordconstnode(tshlshrnode(right).right).value then
                       begin
                         result:=cinlinenode.create(in_rol_x_y,false,
                           ccallparanode.create(tshlshrnode(left).right,
                           ccallparanode.create(tshlshrnode(left).left,nil)));
                         tshlshrnode(left).left:=nil;
                         tshlshrnode(left).right:=nil;
                         exit;
                       end
                     else if tordconstnode(tshlshrnode(right).right).value=
                       tshlshrnode(left).left.resultdef.size*8-tordconstnode(tshlshrnode(left).right).value then
                       begin
                         result:=cinlinenode.create(in_ror_x_y,false,
                           ccallparanode.create(tshlshrnode(right).right,
                           ccallparanode.create(tshlshrnode(left).left,nil)));
                         tshlshrnode(left).left:=nil;
                         tshlshrnode(right).right:=nil;
                         exit;
                       end;
                   end;
              end;
{$endif cpurox}
          end;
      end;


    function taddnode.dogetcopy: tnode;
      var
        n: taddnode;
      begin
        n:=taddnode(inherited dogetcopy);
        n.resultrealdef:=resultrealdef;
        result:=n;
      end;


    function taddnode.docompare(p: tnode): boolean;
      begin
        result:=
          inherited docompare(p) and
          equal_defs(taddnode(p).resultrealdef,resultrealdef);
      end;


    function taddnode.pass_typecheck:tnode;
      begin
        { This function is small to keep the stack small for recursive of
          large + operations }
        typecheckpass(left);
        typecheckpass(right);
        result:=pass_typecheck_internal;
      end;


    function taddnode.pass_typecheck_internal:tnode;
      var
        hp          : tnode;
        rd,ld,nd    : tdef;
        hsym        : tfieldvarsym;
        llow,lhigh,
        rlow,rhigh  : tconstexprint;
        strtype     : tstringtype;
        res,
        b           : boolean;
        lt,rt       : tnodetype;
        ot          : tnodetype;
{$ifdef state_tracking}
        factval     : Tnode;
        change      : boolean;
{$endif}

      begin
         result:=nil;
         { avoid any problems with type parameters later on }
         if is_typeparam(left.resultdef) or is_typeparam(right.resultdef) then
           begin
             resultdef:=cundefinedtype;
             exit;
           end;

         { both left and right need to be valid }
         set_varstate(left,vs_read,[vsf_must_be_valid]);
         set_varstate(right,vs_read,[vsf_must_be_valid]);
         if codegenerror then
           exit;

         { tp procvar support }
         maybe_call_procvar(left,true);
         maybe_call_procvar(right,true);

         { convert array constructors to sets, because there is no other operator
           possible for array constructors }
         if is_array_constructor(left.resultdef) then
          begin
            arrayconstructor_to_set(left);
            typecheckpass(left);
          end;
         if is_array_constructor(right.resultdef) then
          begin
            arrayconstructor_to_set(right);
            typecheckpass(right);
          end;

         { allow operator overloading }
         hp:=self;
         if isbinaryoverloaded(hp) then
           begin
              result:=hp;
              exit;
           end;
         { Stop checking when an error was found in the operator checking }
         if codegenerror then
           begin
             result:=cerrornode.create;
             exit;
           end;


         { Kylix allows enum+ordconstn in an enum type declaration, we need to do
           the conversion here before the constant folding }
         if (m_delphi in current_settings.modeswitches) and
            (blocktype in [bt_type,bt_const_type,bt_var_type]) then
          begin
            if (left.resultdef.typ=enumdef) and
               (right.resultdef.typ=orddef) then
             begin
               { insert explicit typecast to default signed int }
               left:=ctypeconvnode.create_internal(left,sinttype);
               typecheckpass(left);
             end
            else
             if (left.resultdef.typ=orddef) and
                (right.resultdef.typ=enumdef) then
              begin
                { insert explicit typecast to default signed int }
                right:=ctypeconvnode.create_internal(right,sinttype);
                typecheckpass(right);
              end;
          end;

        { is one a real float, then both need to be floats, this
          need to be done before the constant folding so constant
          operation on a float and int are also handled }
{$ifdef x86}
        { use extended as default real type only when the x87 fpu is used }
  {$ifdef i386}
        if not(current_settings.fputype=fpu_x87) then
          resultrealdef:=s64floattype
        else
          resultrealdef:=pbestrealtype^;
  {$endif i386}
  {$ifdef x86_64}
        { x86-64 has no x87 only mode, so use always double as default }
        resultrealdef:=s64floattype;
  {$endif x86_6}
{$else not x86}
        resultrealdef:=pbestrealtype^;
{$endif not x86}

        if (right.resultdef.typ=floatdef) or (left.resultdef.typ=floatdef) then
         begin
           { when both floattypes are already equal then use that
             floattype for results }
           if (right.resultdef.typ=floatdef) and
              (left.resultdef.typ=floatdef) and
              (tfloatdef(left.resultdef).floattype=tfloatdef(right.resultdef).floattype) then
             resultrealdef:=left.resultdef
           { when there is a currency type then use currency, but
             only when currency is defined as float }
           else
            if (is_currency(right.resultdef) or
                is_currency(left.resultdef)) and
               ((s64currencytype.typ = floatdef) or
                (nodetype <> slashn)) then
             begin
               resultrealdef:=s64currencytype;
               inserttypeconv(right,resultrealdef);
               inserttypeconv(left,resultrealdef);
             end
           else
            begin
              resultrealdef:=getbestreal(left.resultdef,right.resultdef);
              inserttypeconv(right,resultrealdef);
              inserttypeconv(left,resultrealdef);
            end;
         end;

        { If both operands are constant and there is a unicodestring
          or unicodestring then convert everything to unicodestring }
        if is_constnode(right) and is_constnode(left) and
           (is_unicodestring(right.resultdef) or
            is_unicodestring(left.resultdef)) then
          begin
            inserttypeconv(right,cunicodestringtype);
            inserttypeconv(left,cunicodestringtype);
          end;

        { If both operands are constant and there is a widechar
          or widestring then convert everything to widestring. This
          allows constant folding like char+widechar }
        if is_constnode(right) and is_constnode(left) and
           (is_widestring(right.resultdef) or
            is_widestring(left.resultdef) or
            is_widechar(right.resultdef) or
            is_widechar(left.resultdef)) then
          begin
            inserttypeconv(right,cwidestringtype);
            inserttypeconv(left,cwidestringtype);
          end;

        { load easier access variables }
        rd:=right.resultdef;
        ld:=left.resultdef;
        rt:=right.nodetype;
        lt:=left.nodetype;

         { 4 character constant strings are compatible with orddef }
         { in macpas mode (become cardinals)                       }
         if (m_mac in current_settings.modeswitches) and
            { only allow for comparisons, additions etc are }
            { normally program errors                       }
            (nodetype in [ltn,lten,gtn,gten,unequaln,equaln]) and
            (((lt=stringconstn) and
              (tstringconstnode(left).len=4) and
              (rd.typ=orddef)) or
             ((rt=stringconstn) and
              (tstringconstnode(right).len=4) and
              (ld.typ=orddef))) then
           begin
             if (rt=stringconstn) then
               begin
                 inserttypeconv(right,u32inttype);
                 rt:=right.nodetype;
                 rd:=right.resultdef;
               end
             else
               begin
                 inserttypeconv(left,u32inttype);
                 lt:=left.nodetype;
                 ld:=left.resultdef;
               end;
           end;

         { but an int/int gives real/real! }
         if (nodetype=slashn) and not(is_vector(left.resultdef)) and not(is_vector(right.resultdef)) then
          begin
            if is_currency(left.resultdef) and
               is_currency(right.resultdef) then
              { In case of currency, converting to float means dividing by 10000 }
              { However, since this is already a division, both divisions by     }
              { 10000 are eliminated when we divide the results -> we can skip   }
              { them.                                                            }
              if s64currencytype.typ = floatdef then
                begin
                  { there's no s64comptype or so, how do we avoid the type conversion?
                  left.resultdef := s64comptype;
                  right.resultdef := s64comptype; }
                end
              else
                begin
                  left.resultdef := s64inttype;
                  right.resultdef := s64inttype;
                end;
            inserttypeconv(right,resultrealdef);
            inserttypeconv(left,resultrealdef);
          end

         { if both are orddefs then check sub types }
         else if (ld.typ=orddef) and (rd.typ=orddef) then
           begin
              { set for & and | operations in macpas mode: they only work on }
              { booleans, and always short circuit evaluation                }
              if (nf_short_bool in flags) then
                begin
                  if not is_boolean(ld) then
                    begin
                      inserttypeconv(left,pasbool8type);
                      ld := left.resultdef;
                    end;
                  if not is_boolean(rd) then
                    begin
                      inserttypeconv(right,pasbool8type);
                      rd := right.resultdef;
                    end;
                end;

             { 2 booleans? }
             if (is_boolean(ld) and is_boolean(rd)) then
              begin
                case nodetype of
                  xorn,
                  andn,
                  orn:
                    begin
                      { Make sides equal to the largest boolean }
                      if (torddef(left.resultdef).size>torddef(right.resultdef).size) or
                        (is_cbool(left.resultdef) and not is_cbool(right.resultdef)) then
                        begin
                          right:=ctypeconvnode.create_internal(right,left.resultdef);
                          ttypeconvnode(right).convtype:=tc_bool_2_bool;
                          typecheckpass(right);
                        end
                      else if (torddef(left.resultdef).size<torddef(right.resultdef).size) or
                        (not is_cbool(left.resultdef) and is_cbool(right.resultdef)) then
                        begin
                          left:=ctypeconvnode.create_internal(left,right.resultdef);
                          ttypeconvnode(left).convtype:=tc_bool_2_bool;
                          typecheckpass(left);
                        end;
                    end;
                  ltn,
                  lten,
                  gtn,
                  gten:
                    begin
                      { convert both to pasbool to perform the comparison (so
                        that longbool(4) = longbool(2), since both represent
                        "true" }
                      inserttypeconv(left,pasbool8type);
                      inserttypeconv(right,pasbool8type);
                    end;
                  unequaln,
                  equaln:
                    begin
                      if not(cs_full_boolean_eval in current_settings.localswitches) or
                         (nf_short_bool in flags) then
                       begin
                         { Remove any compares with constants }
                         if (left.nodetype=ordconstn) then
                          begin
                            hp:=right;
                            b:=(tordconstnode(left).value<>0);
                            ot:=nodetype;
                            left.free;
                            left:=nil;
                            right:=nil;
                            if (not(b) and (ot=equaln)) or
                               (b and (ot=unequaln)) then
                             begin
                               hp:=cnotnode.create(hp);
                             end;
                            result:=hp;
                            exit;
                          end;
                         if (right.nodetype=ordconstn) then
                          begin
                            hp:=left;
                            b:=(tordconstnode(right).value<>0);
                            ot:=nodetype;
                            right.free;
                            right:=nil;
                            left:=nil;
                            if (not(b) and (ot=equaln)) or
                               (b and (ot=unequaln)) then
                             begin
                               hp:=cnotnode.create(hp);
                             end;
                            result:=hp;
                            exit;
                          end;
                       end;
                      { Delphi-compatibility: convert both to pasbool to
                        perform the equality comparison }
                      inserttypeconv(left,pasbool8type);
                      inserttypeconv(right,pasbool8type);
                    end;
                  else
                    begin
                      CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),ld.typename,rd.typename);
                      result:=cnothingnode.create;
                      exit;
                    end;
                end;
              end
             { Both are chars? }
             else if is_char(rd) and is_char(ld) then
               begin
                 if nodetype=addn then
                  begin
                    resultdef:=cshortstringtype;
                    if not(is_constcharnode(left) and is_constcharnode(right)) then
                     begin
                       inserttypeconv(left,cshortstringtype);
{$ifdef addstringopt}
                       hp := genaddsstringcharoptnode(self);
                       result := hp;
                       exit;
{$endif addstringopt}
                     end
                  end
                else if not(nodetype in [ltn,lten,gtn,gten,unequaln,equaln]) then
                  begin
                    CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),ld.typename,rd.typename);
                    result:=cnothingnode.create;
                    exit;
                  end;
               end
             { There is a widechar? }
             else if is_widechar(rd) or is_widechar(ld) then
               begin
                 { widechar+widechar gives unicodestring }
                 if nodetype=addn then
                   begin
                     inserttypeconv(left,cunicodestringtype);
                     if (torddef(rd).ordtype<>uwidechar) then
                       inserttypeconv(right,cwidechartype);
                     resultdef:=cunicodestringtype;
                   end
                 else
                   begin
                     if (torddef(ld).ordtype<>uwidechar) then
                       inserttypeconv(left,cwidechartype);
                     if (torddef(rd).ordtype<>uwidechar) then
                       inserttypeconv(right,cwidechartype);
                   end;
               end
             { is there a currency type ? }
             else if ((torddef(rd).ordtype=scurrency) or (torddef(ld).ordtype=scurrency)) then
               begin
                  if (torddef(ld).ordtype<>scurrency) then
                   inserttypeconv(left,s64currencytype);
                  if (torddef(rd).ordtype<>scurrency) then
                   inserttypeconv(right,s64currencytype);
               end
             { leave some constant integer expressions alone in case the
               resultdef of the integer types doesn't influence the outcome,
               because the forced type conversions below can otherwise result
               in unexpected results (such as high(qword)<high(int64) returning
               true because high(qword) gets converted to int64) }
             else if is_integer(ld) and is_integer(rd) and
                     (lt=ordconstn) and (rt=ordconstn) and
                     (nodetype in [equaln,unequaln,gtn,gten,ltn,lten]) then
               begin
               end
             { "and" does't care about the sign of integers }
             { "xor", "or" and compares don't need extension to native int }
             { size either as long as both values are signed or unsigned   }
             { "xor" and "or" also don't care about the sign if the values }
             { occupy an entire register                                   }
             { don't do it if either type is 64 bit, since in that case we }
             { can't safely find a "common" type                           }
             else if is_integer(ld) and is_integer(rd) and
                     not is_64bitint(ld) and not is_64bitint(rd) and
                     ((nodetype=andn) or
                      ((nodetype in [orn,xorn,equaln,unequaln,gtn,gten,ltn,lten]) and
                       not(is_signed(ld) xor is_signed(rd)))) then
               begin
                 if (rd.size>ld.size) or
                    { Delphi-compatible: prefer unsigned type for "and" with equal size }
                    ((rd.size=ld.size) and
                     not is_signed(rd)) then
                   begin
                     if (rd.size=ld.size) and
                        is_signed(ld) then
                       inserttypeconv_internal(left,rd)
                     else
                       begin
                         { not to left right.resultdef, because that may
                           cause a range error if left and right's def don't
                           completely overlap }
                         nd:=get_common_intdef(torddef(ld),torddef(rd),true);
                         inserttypeconv(left,nd);
                         inserttypeconv(right,nd);
                       end;
                   end
                 else
                   begin
                     if (rd.size=ld.size) and
                        is_signed(rd) then
                       inserttypeconv_internal(right,ld)
                     else
                       begin
                         nd:=get_common_intdef(torddef(ld),torddef(rd),true);
                         inserttypeconv(left,nd);
                         inserttypeconv(right,nd);
                       end;
                   end
               end
             { is there a signed 64 bit type ? }
             else if ((torddef(rd).ordtype=s64bit) or (torddef(ld).ordtype=s64bit)) then
               begin
                  if (torddef(ld).ordtype<>s64bit) then
                   inserttypeconv(left,s64inttype);
                  if (torddef(rd).ordtype<>s64bit) then
                   inserttypeconv(right,s64inttype);
               end
             { is there a unsigned 64 bit type ? }
             else if ((torddef(rd).ordtype=u64bit) or (torddef(ld).ordtype=u64bit)) then
               begin
                  if (torddef(ld).ordtype<>u64bit) then
                   inserttypeconv(left,u64inttype);
                  if (torddef(rd).ordtype<>u64bit) then
                   inserttypeconv(right,u64inttype);
               end
             { 64 bit cpus do calculations always in 64 bit }
{$ifndef cpu64bitaddr}
             { is there a cardinal? }
             else if ((torddef(rd).ordtype=u32bit) or (torddef(ld).ordtype=u32bit)) then
               begin
                 { convert positive constants to u32bit }
                 if (torddef(ld).ordtype<>u32bit) and
                    is_constintnode(left) and
                    (tordconstnode(left).value >= 0) then
                   inserttypeconv(left,u32inttype);
                 if (torddef(rd).ordtype<>u32bit) and
                    is_constintnode(right) and
                    (tordconstnode(right).value >= 0) then
                   inserttypeconv(right,u32inttype);
                 { when one of the operand is signed or the operation is subn then perform
                   the operation in 64bit, can't use rd/ld here because there
                   could be already typeconvs inserted.
                   This is compatible with the code below for other unsigned types (PFV) }
                 if is_signed(left.resultdef) or
                    is_signed(right.resultdef) or
                    (nodetype=subn) then
                   begin
                     if nodetype<>subn then
                       CGMessage(type_h_mixed_signed_unsigned);
                     { mark as internal in case added for a subn, so }
                     { ttypeconvnode.simplify can remove the 64 bit  }
                     { typecast again if semantically correct. Even  }
                     { if we could detect that here already, we      }
                     { mustn't do it here because that would change  }
                     { overload choosing behaviour etc. The code in  }
                     { ncnv.pas is run after that is already decided }
                     if (not is_signed(left.resultdef) and
                         not is_signed(right.resultdef)) or
                        (nodetype in [orn,xorn]) then
                       include(flags,nf_internal);
                     inserttypeconv(left,s64inttype);
                     inserttypeconv(right,s64inttype);
                   end
                 else
                   begin
                     if (torddef(left.resultdef).ordtype<>u32bit) then
                       inserttypeconv(left,u32inttype);
                     if (torddef(right.resultdef).ordtype<>u32bit) then
                       inserttypeconv(right,u32inttype);
                   end;
               end
{$endif cpu64bitaddr}
             { generic ord conversion is sinttype }
             else
               begin
                 { When there is a signed type or there is a minus operation
                   we convert to signed int. Otherwise (both are unsigned) we keep
                   the result also unsigned. This is compatible with Delphi (PFV) }
                 if is_signed(ld) or
                    is_signed(rd) or
                    (nodetype=subn) then
                   begin
{$ifdef cpunodefaultint}
                     { for small cpus we use the smallest common type }
                     nd:=get_common_intdef(torddef(ld),torddef(rd),false);
                     inserttypeconv(right,nd);
                     inserttypeconv(left,nd);
{$else cpunodefaultint}
                     inserttypeconv(right,sinttype);
                     inserttypeconv(left,sinttype);
{$endif cpunodefaultint}
                   end
                 else
                   begin
                     inserttypeconv(right,uinttype);
                     inserttypeconv(left,uinttype);
                   end;
               end;
           end

         { if both are floatdefs, conversion is already done before constant folding }
         else if (ld.typ=floatdef) then
           begin
             if not(nodetype in [addn,subn,muln,slashn,equaln,unequaln,ltn,lten,gtn,gten]) then
               CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),ld.typename,rd.typename);
           end

         { left side a setdef, must be before string processing,
           else array constructor can be seen as array of char (PFV) }
         else if (ld.typ=setdef) then
          begin
             if not(nodetype in [addn,subn,symdifn,muln,equaln,unequaln,lten,gten]) then
              CGMessage(type_e_set_operation_unknown);
             { right must either be a set or a set element }
             if (rd.typ<>setdef) and
                (rt<>setelementn) then
               CGMessage(type_e_mismatch)
             { Make operands the same setdef. If one's elementtype fits   }
             { entirely inside the other's, pick the one with the largest }
             { range.  Otherwise create a new setdef with a range which   }
             { can contain both.                                          }
             else if not(equal_defs(ld,rd)) then
              begin
                { note: ld cannot be an empty set with elementdef=nil in }
                { case right is not a set, arrayconstructor_to_set takes }
                { care of that                                           }

                { 1: rd is a set with an assigned elementdef, and ld is    }
                {    either an empty set without elementdef or a set whose }
                {    elementdef fits in rd's elementdef -> convert to rd   }
                if ((rd.typ=setdef) and
                    assigned(tsetdef(rd).elementdef) and
                    (not assigned(tsetdef(ld).elementdef) or
                     is_in_limit(ld,rd))) then
                  inserttypeconv(left,rd)
                { 2: rd is either an empty set without elementdef or a set }
                {    whose elementdef fits in ld's elementdef, or a set    }
                {    element whose def fits in ld's elementdef -> convert  }
                {    to ld. ld's elementdef can't be nil here, is caught   }
                {    previous case and "note:" above                       }
                else if ((rd.typ=setdef) and
                         (not assigned(tsetdef(rd).elementdef) or
                          is_in_limit(rd,ld))) or
                        ((rd.typ<>setdef) and
                         is_in_limit(rd,tsetdef(ld).elementdef)) then
                   if (rd.typ=setdef) then
                    inserttypeconv(right,ld)
                  else
                    inserttypeconv(right,tsetdef(ld).elementdef)
                { 3: otherwise create setdef which encompasses both, taking }
                {    into account empty sets without elementdef             }
                else
                  begin
                    if assigned(tsetdef(ld).elementdef) then
                      begin
                        llow:=tsetdef(ld).setbase;
                        lhigh:=tsetdef(ld).setmax;
                      end;
                    if (rd.typ=setdef) then
                      if assigned(tsetdef(rd).elementdef) then
                        begin
                          rlow:=tsetdef(rd).setbase;
                          rhigh:=tsetdef(rd).setmax;
                        end
                      else
                        begin
                          { ld's elementdef must have been valid }
                          rlow:=llow;
                          rhigh:=lhigh;
                        end
                    else
                      getrange(rd,rlow,rhigh);
                    if not assigned(tsetdef(ld).elementdef) then
                      begin
                        llow:=rlow;
                        lhigh:=rhigh;
                      end;
                    nd:=tsetdef.create(tsetdef(ld).elementdef,min(llow,rlow),max(lhigh,rhigh));
                    inserttypeconv(left,nd);
                    if (rd.typ=setdef) then
                      inserttypeconv(right,nd)
                    else
                       inserttypeconv(right,tsetdef(nd).elementdef);
                  end;
              end;
          end
         { pointer comparision and subtraction }
         else if (
                  (rd.typ=pointerdef) and (ld.typ=pointerdef)
                 ) or
                 { compare/add pchar to variable (not stringconst) char arrays
                   by addresses like BP/Delphi }
                 (
                  (nodetype in [equaln,unequaln,subn,addn]) and
                  (
                   ((is_pchar(ld) or (lt=niln)) and is_chararray(rd) and (rt<>stringconstn)) or
                   ((is_pchar(rd) or (rt=niln)) and is_chararray(ld) and (lt<>stringconstn))
                  )
                 ) then
          begin
            { convert char array to pointer }
            if is_chararray(rd) then
              begin
                inserttypeconv(right,charpointertype);
                rd:=right.resultdef;
              end
            else if is_chararray(ld) then
              begin
                inserttypeconv(left,charpointertype);
                ld:=left.resultdef;
              end;

            case nodetype of
               equaln,unequaln :
                 begin
                    if is_voidpointer(right.resultdef) then
                      inserttypeconv(right,left.resultdef)
                    else if is_voidpointer(left.resultdef) then
                      inserttypeconv(left,right.resultdef)
                    else if not(equal_defs(ld,rd)) then
                      IncompatibleTypes(ld,rd);
                    { now that the type checking is done, convert both to charpointer, }
                    { because methodpointers are 8 bytes even though only the first 4  }
                    { bytes must be compared. This can happen here if we are in        }
                    { TP/Delphi mode, because there @methodpointer = voidpointer (but  }
                    { a voidpointer of 8 bytes). A conversion to voidpointer would be  }
                    { optimized away, since the result already was a voidpointer, so   }
                    { use a charpointer instead (JM)                                   }
{$ifndef jvm}
                    inserttypeconv_internal(left,charpointertype);
                    inserttypeconv_internal(right,charpointertype);
{$else jvm}
                    inserttypeconv_internal(left,java_jlobject);
                    inserttypeconv_internal(right,java_jlobject);
{$endif jvm}
                 end;
               ltn,lten,gtn,gten:
                 begin
                    if (cs_extsyntax in current_settings.moduleswitches) then
                     begin
                       if is_voidpointer(right.resultdef) then
                        inserttypeconv(right,left.resultdef)
                       else if is_voidpointer(left.resultdef) then
                        inserttypeconv(left,right.resultdef)
                       else if not(equal_defs(ld,rd)) then
                        IncompatibleTypes(ld,rd);
                     end
                    else
                     CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),ld.typename,rd.typename);
                 end;
               subn:
                 begin
                    if (cs_extsyntax in current_settings.moduleswitches) then
                      begin
                        if is_voidpointer(right.resultdef) then
                        begin
                          if is_big_untyped_addrnode(right) then
                            CGMessage1(type_w_untyped_arithmetic_unportable,node2opstr(nodetype));
                          inserttypeconv(right,left.resultdef)
                        end
                        else if is_voidpointer(left.resultdef) then
                          inserttypeconv(left,right.resultdef)
                        else if not(equal_defs(ld,rd)) then
                          IncompatibleTypes(ld,rd);
                      end
                    else
                      CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),ld.typename,rd.typename);

                    if not(nf_has_pointerdiv in flags) and
                      (tpointerdef(rd).pointeddef.size>1) then
                      begin
                        hp:=getcopy;
                        include(hp.flags,nf_has_pointerdiv);
                        result:=cmoddivnode.create(divn,hp,cordconstnode.create(tpointerdef(rd).pointeddef.size,sinttype,false));
                      end;
                    resultdef:=sinttype;
                    exit;
                 end;
               else
                 CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),ld.typename,rd.typename);
            end;
          end

         { is one of the operands a string?,
           chararrays are also handled as strings (after conversion), also take
           care of chararray+chararray and chararray+char.
           Note: Must be done after pointerdef+pointerdef has been checked, else
           pchar is converted to string }
         else if (rd.typ=stringdef) or
                 (ld.typ=stringdef) or
                 { stringconstn's can be arraydefs }
                 (lt=stringconstn) or
                 (rt=stringconstn) or
                 ((is_pchar(rd) or is_chararray(rd) or is_char(rd) or is_open_chararray(rd) or
                   is_pwidechar(rd) or is_widechararray(rd) or is_widechar(rd) or is_open_widechararray(rd)) and
                  (is_pchar(ld) or is_chararray(ld) or is_char(ld) or is_open_chararray(ld) or
                   is_pwidechar(ld) or is_widechararray(ld) or is_widechar(ld) or is_open_widechararray(ld))) then
          begin
            if (nodetype in [addn,equaln,unequaln,lten,gten,ltn,gtn]) then
              begin
                { Is there a unicodestring? }
                if is_unicodestring(rd) or is_unicodestring(ld) or
                   ((m_default_unicodestring in current_settings.modeswitches) and
                    (cs_refcountedstrings in current_settings.localswitches) and
                    (
                     is_pwidechar(rd) or is_widechararray(rd) or is_open_widechararray(rd) or (lt = stringconstn) or
                     is_pwidechar(ld) or is_widechararray(ld) or is_open_widechararray(ld) or (rt = stringconstn)
                    )
                   ) then
                  strtype:=st_unicodestring
                else
                { Is there a widestring? }
                  if is_widestring(rd) or is_widestring(ld) or
                     is_pwidechar(rd) or is_widechararray(rd) or is_widechar(rd) or is_open_widechararray(rd) or
                     is_pwidechar(ld) or is_widechararray(ld) or is_widechar(ld) or is_open_widechararray(ld) then
                    strtype:=st_widestring
                else
                  if is_ansistring(rd) or is_ansistring(ld) or
                     ((cs_refcountedstrings in current_settings.localswitches) and
                     //todo: Move some of this to longstring's then they are implemented?
                      (
                       is_pchar(rd) or (is_chararray(rd) and (rd.size > 255)) or is_open_chararray(rd) or (lt = stringconstn) or
                       is_pchar(ld) or (is_chararray(ld) and (ld.size > 255)) or is_open_chararray(ld) or (rt = stringconstn)
                      )
                     ) then
                    strtype:=st_ansistring
                else
                  if is_longstring(rd) or is_longstring(ld) then
                    strtype:=st_longstring
                else
                  begin
                    { TODO: todo: add a warning/hint here if one converting a too large array}
                    { nodes is PChar, array [with size > 255] or OpenArrayOfChar.
                      Note: Delphi halts with error if "array [0..xx] of char"
                           is assigned to ShortString and string length is less
                           then array size }
                    strtype:= st_shortstring;
                  end;

                // Now convert nodes to common string type
                case strtype of
                  st_widestring :
                    begin
                      if not(is_widestring(rd)) then
                        inserttypeconv(right,cwidestringtype);
                      if not(is_widestring(ld)) then
                        inserttypeconv(left,cwidestringtype);
                    end;
                  st_unicodestring :
                    begin
                      if not(is_unicodestring(rd)) then
                        inserttypeconv(right,cunicodestringtype);
                      if not(is_unicodestring(ld)) then
                        inserttypeconv(left,cunicodestringtype);
                    end;
                  st_ansistring :
                    begin
                      { use same code page if possible (don't force same code
                        page in case both are ansistrings with code page <>
                        CP_NONE, since then data loss can occur (the ansistring
                        helpers will convert them at run time to an encoding
                        that can represent both encodings) }
                      if is_ansistring(ld) and
                         (tstringdef(ld).encoding<>0) and
                         (tstringdef(ld).encoding<>globals.CP_NONE) and
                         (not is_ansistring(rd) or
                          (tstringdef(rd).encoding=0) or
                          (tstringdef(rd).encoding=globals.CP_NONE)) then
                        inserttypeconv(right,ld)
                      else if is_ansistring(rd) and
                         (tstringdef(rd).encoding<>0) and
                         (tstringdef(rd).encoding<>globals.CP_NONE) and
                         (not is_ansistring(ld) or
                          (tstringdef(ld).encoding=0) or
                          (tstringdef(ld).encoding=globals.CP_NONE)) then
                        inserttypeconv(left,rd)
                      else
                        begin
                          if not is_ansistring(ld) then
                            inserttypeconv(left,getansistringdef);
                          if not is_ansistring(rd) then
                            inserttypeconv(right,getansistringdef);
                        end;
                    end;
                  st_longstring :
                    begin
                      if not(is_longstring(rd)) then
                        inserttypeconv(right,clongstringtype);
                      if not(is_longstring(ld)) then
                        inserttypeconv(left,clongstringtype);
                     end;
                   st_shortstring :
                     begin
                       if not(is_shortstring(ld)) then
                         inserttypeconv(left,cshortstringtype);
                       { don't convert char, that can be handled by the optimized node }
                       if not(is_shortstring(rd) or is_char(rd)) then
                         inserttypeconv(right,cshortstringtype);
                     end;
                   else
                     internalerror(2005101);
                end;
              end
            else
              CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),ld.typename,rd.typename);
          end

         { implicit pointer object type comparison }
         else if is_implicit_pointer_object_type(rd) or is_implicit_pointer_object_type(ld) then
          begin
            if (nodetype in [equaln,unequaln]) then
              begin
                if is_implicit_pointer_object_type(rd) and is_implicit_pointer_object_type(ld) then
                 begin
                   if tobjectdef(rd).is_related(tobjectdef(ld)) then
                    inserttypeconv(right,left.resultdef)
                   else
                    inserttypeconv(left,right.resultdef);
                 end
                else if is_implicit_pointer_object_type(rd) then
                  inserttypeconv(left,right.resultdef)
                else
                  inserttypeconv(right,left.resultdef);
              end
            else
              CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),ld.typename,rd.typename);
          end

         else if (rd.typ=classrefdef) and (ld.typ=classrefdef) then
          begin
            if (nodetype in [equaln,unequaln]) then
              begin
                if tobjectdef(tclassrefdef(rd).pointeddef).is_related(
                        tobjectdef(tclassrefdef(ld).pointeddef)) then
                  inserttypeconv(right,left.resultdef)
                else
                  inserttypeconv(left,right.resultdef);
              end
            else
              CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),ld.typename,rd.typename);
          end

         { allow comparison with nil pointer }
         else if is_implicit_pointer_object_type(rd) or (rd.typ=classrefdef) then
          begin
            if (nodetype in [equaln,unequaln]) then
              inserttypeconv(left,right.resultdef)
            else
              CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),ld.typename,rd.typename);
          end

         else if is_implicit_pointer_object_type(ld) or (ld.typ=classrefdef) then
          begin
            if (nodetype in [equaln,unequaln]) then
              inserttypeconv(right,left.resultdef)
            else
              CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),ld.typename,rd.typename);
          end

       { support procvar=nil,procvar<>nil }
         else if ((ld.typ=procvardef) and (rt=niln)) or
                 ((rd.typ=procvardef) and (lt=niln)) then
          begin
            if not(nodetype in [equaln,unequaln]) then
              CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),ld.typename,rd.typename);
            { find proc field in methodpointer record }
            hsym:=tfieldvarsym(trecorddef(methodpointertype).symtable.Find('proc'));
            if not assigned(hsym) then
              internalerror(200412043);
            { For methodpointers compare only tmethodpointer.proc }
            if (rd.typ=procvardef) and
               (not tprocvardef(rd).is_addressonly) then
              begin
                right:=csubscriptnode.create(
                           hsym,
                           ctypeconvnode.create_internal(right,methodpointertype));
                typecheckpass(right);
               end;
            if (ld.typ=procvardef) and
               (not tprocvardef(ld).is_addressonly) then
              begin
                left:=csubscriptnode.create(
                          hsym,
                          ctypeconvnode.create_internal(left,methodpointertype));
                typecheckpass(left);
              end;
          end

       { support dynamicarray=nil,dynamicarray<>nil }
         else if (is_dynamic_array(ld) and (rt=niln)) or
                 (is_dynamic_array(rd) and (lt=niln)) or
                 (is_dynamic_array(ld) and is_dynamic_array(rd)) then
          begin
            if not(nodetype in [equaln,unequaln]) then
              CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),ld.typename,rd.typename);
          end

{$ifdef SUPPORT_MMX}
       { mmx support, this must be before the zero based array
         check }
         else if (cs_mmx in current_settings.localswitches) and
                 is_mmx_able_array(ld) and
                 is_mmx_able_array(rd) and
                 equal_defs(ld,rd) then
            begin
              case nodetype of
                addn,subn,xorn,orn,andn:
                  ;
                { mul is a little bit restricted }
                muln:
                  if not(mmx_type(ld) in [mmxu16bit,mmxs16bit,mmxfixed16]) then
                    CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),ld.typename,rd.typename);
                else
                  CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),ld.typename,rd.typename);
              end;
            end
{$endif SUPPORT_MMX}
         { vector support, this must be before the zero based array
           check }
         else if (cs_support_vectors in current_settings.globalswitches) and
                 is_vector(ld) and
                 is_vector(rd) and
                 equal_defs(ld,rd) then
            begin
              if not(nodetype in [addn,subn,xorn,orn,andn,muln,slashn]) then
                CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),ld.typename,rd.typename);
              { both defs must be equal, so taking left or right as resultdef doesn't matter }
              resultdef:=left.resultdef;
            end

         { this is a little bit dangerous, also the left type }
         { pointer to should be checked! This broke the mmx support      }
         else if (rd.typ=pointerdef) or
                 (is_zero_based_array(rd) and (rt<>stringconstn)) then
          begin
            if is_zero_based_array(rd) then
              begin
                resultdef:=getpointerdef(tarraydef(rd).elementdef);
                inserttypeconv(right,resultdef);
              end
            else
              resultdef:=right.resultdef;
            inserttypeconv(left,sinttype);
            if nodetype=addn then
              begin
                if not(cs_extsyntax in current_settings.moduleswitches) or
                   (not (is_pchar(ld) or is_chararray(ld) or is_open_chararray(ld) or is_widechar(ld) or is_widechararray(ld) or is_open_widechararray(ld)) and
                    not(cs_pointermath in current_settings.localswitches) and
                    not((ld.typ=pointerdef) and tpointerdef(ld).has_pointer_math)) then
                  CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),ld.typename,rd.typename);
                if (rd.typ=pointerdef) and
                   (tpointerdef(rd).pointeddef.size>1) then
                   begin
                     left:=caddnode.create(muln,left,
                       cordconstnode.create(tpointerdef(rd).pointeddef.size,sinttype,true));
                     typecheckpass(left);
                   end;
              end
            else
              CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),ld.typename,rd.typename);
          end

         else if (ld.typ=pointerdef) or
                 (is_zero_based_array(ld) and (lt<>stringconstn)) then
           begin
             if is_zero_based_array(ld) then
               begin
                  resultdef:=getpointerdef(tarraydef(ld).elementdef);
                  inserttypeconv(left,resultdef);
               end
             else
               resultdef:=left.resultdef;

             inserttypeconv(right,sinttype);
             if nodetype in [addn,subn] then
               begin
                 if (lt=niln) then
                   CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),'NIL',rd.typename);
                 if not(cs_extsyntax in current_settings.moduleswitches) or
                   (not (is_pchar(ld) or is_chararray(ld) or is_open_chararray(ld) or is_widechar(ld) or is_widechararray(ld) or is_open_widechararray(ld)) and
                    not(cs_pointermath in current_settings.localswitches) and
                    not((ld.typ=pointerdef) and tpointerdef(ld).has_pointer_math)) then
                   CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),ld.typename,rd.typename);
                 if (ld.typ=pointerdef) then
                 begin
                   if is_big_untyped_addrnode(left) then
                     CGMessage1(type_w_untyped_arithmetic_unportable,node2opstr(nodetype));
                   if (tpointerdef(ld).pointeddef.size>1) then
                   begin
                     right:=caddnode.create(muln,right,
                       cordconstnode.create(tpointerdef(ld).pointeddef.size,sinttype,true));
                     typecheckpass(right);
                   end
                 end else
                   if is_zero_based_array(ld) and
                      (tarraydef(ld).elementdef.size>1) then
                     begin
                       right:=caddnode.create(muln,right,
                         cordconstnode.create(tarraydef(ld).elementdef.size,sinttype,true));
                       typecheckpass(right);
                     end;
               end
             else
               CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),ld.typename,rd.typename);
           end

         else if (rd.typ=procvardef) and
                 (ld.typ=procvardef) and
                 equal_defs(rd,ld) then
          begin
            if (nodetype in [equaln,unequaln]) then
              begin
                if tprocvardef(rd).is_addressonly then
                  begin
                    inserttypeconv_internal(right,voidpointertype);
                    inserttypeconv_internal(left,voidpointertype);
                  end
                else
                  begin
                    { find proc field in methodpointer record }
                    hsym:=tfieldvarsym(trecorddef(methodpointertype).symtable.Find('proc'));
                    if not assigned(hsym) then
                      internalerror(200412043);
                    { Compare tmehodpointer(left).proc }
                    right:=csubscriptnode.create(
                                 hsym,
                                 ctypeconvnode.create_internal(right,methodpointertype));
                    typecheckpass(right);
                    left:=csubscriptnode.create(
                                 hsym,
                                 ctypeconvnode.create_internal(left,methodpointertype));
                     typecheckpass(left);
                  end;
              end
            else
              CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),ld.typename,rd.typename);
          end

         { enums }
         else if (ld.typ=enumdef) and (rd.typ=enumdef) then
          begin
            if allowenumop(nodetype) then
              inserttypeconv(right,left.resultdef)
            else
              CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),ld.typename,rd.typename);
          end

         { generic conversion, this is for error recovery }
         else
          begin
            inserttypeconv(left,sinttype);
            inserttypeconv(right,sinttype);
          end;

         if cmp_of_disjunct_ranges(res) then
           begin
             if res then
               CGMessage(type_w_comparison_always_true)
             else
               CGMessage(type_w_comparison_always_false);
           end;

         { set resultdef if not already done }
         if not assigned(resultdef) then
          begin
             case nodetype of
                ltn,lten,gtn,gten,equaln,unequaln :
                  resultdef:=pasbool8type;
                slashn :
                  resultdef:=resultrealdef;
                addn:
                  begin
                    { for strings, return is always a 255 char string }
                    if is_shortstring(left.resultdef) then
                      resultdef:=cshortstringtype
                    else
                    { for ansistrings set resultdef to assignment left node
                      if it is an assignment and left node expects ansistring }
                    if is_ansistring(left.resultdef) and
                       assigned(aktassignmentnode) and
                       (aktassignmentnode.right=self) and
                       is_ansistring(aktassignmentnode.left.resultdef) then
                      resultdef:=aktassignmentnode.left.resultdef
                    else
                      resultdef:=left.resultdef;
                  end;
                else
                  resultdef:=left.resultdef;
             end;
          end;

         { when the result is currency we need some extra code for
           multiplication and division. this should not be done when
           the muln or slashn node is created internally }
         if not(nf_is_currency in flags) and
            is_currency(resultdef) then
          begin
            case nodetype of
              slashn :
                begin
                  { slashn will only work with floats }
                  hp:=caddnode.create(muln,getcopy,crealconstnode.create(10000.0,s64currencytype));
                  include(hp.flags,nf_is_currency);
                  result:=hp;
                end;
              muln :
                begin
                  if s64currencytype.typ=floatdef then
                    hp:=caddnode.create(slashn,getcopy,crealconstnode.create(10000.0,s64currencytype))
                  else
                    hp:=cmoddivnode.create(divn,getcopy,cordconstnode.create(10000,s64currencytype,false));
                  include(hp.flags,nf_is_currency);
                  result:=hp
                end;
            end;
          end;

         if not codegenerror and
            not assigned(result) then
           result:=simplify(false);
      end;


    function taddnode.first_addstring: tnode;
      const
        swap_relation: array [ltn..unequaln] of Tnodetype=(gtn, gten, ltn, lten, equaln, unequaln);
      var
        p: tnode;
        newstatement : tstatementnode;
        tempnode (*,tempnode2*) : ttempcreatenode;
        cmpfuncname: string;
        para: tcallparanode;
      begin
        { when we get here, we are sure that both the left and the right }
        { node are both strings of the same stringtype (JM)              }
        case nodetype of
          addn:
            begin
              if (left.nodetype=stringconstn) and (tstringconstnode(left).len=0) then
                begin
                  result:=right;
                  left.free;
                  left:=nil;
                  right:=nil;
                  exit;
                end;
              if (right.nodetype=stringconstn) and (tstringconstnode(right).len=0) then
                begin
                  result:=left;
                  left:=nil;
                  right.free;
                  right:=nil;
                  exit;
                end;
              { create the call to the concat routine both strings as arguments }
              if assigned(aktassignmentnode) and
                  (aktassignmentnode.right=self) and
                  (aktassignmentnode.left.resultdef=resultdef) and
                  valid_for_var(aktassignmentnode.left,false) then
                begin
                  para:=ccallparanode.create(
                          right,
                          ccallparanode.create(
                            left,
                            ccallparanode.create(aktassignmentnode.left.getcopy,nil)
                          )
                        );
                  if is_ansistring(resultdef) then
                    para:=ccallparanode.create(
                            cordconstnode.create(
                              getparaencoding(resultdef),
                              u16inttype,
                              true
                            ),
                            para
                          );
                  result:=ccallnode.createintern(
                            'fpc_'+tstringdef(resultdef).stringtypname+'_concat',
                            para
                          );
                  include(aktassignmentnode.flags,nf_assign_done_in_right);
                  firstpass(result);
                end
              else
                begin
                  result:=internalstatements(newstatement);
                  tempnode:=ctempcreatenode.create(resultdef,resultdef.size,tt_persistent,true);
                  addstatement(newstatement,tempnode);
                  { initialize the temp, since it will be passed to a
                    var-parameter (and finalization, which is performed by the
                    ttempcreate node and which takes care of the initialization
                    on native targets, is a noop on managed VM targets) }
                  if (target_info.system in systems_managed_vm) and
                     is_managed_type(resultdef) then
                    addstatement(newstatement,cinlinenode.create(in_setlength_x,
                      false,
                      ccallparanode.create(genintconstnode(0),
                        ccallparanode.create(ctemprefnode.create(tempnode),nil))));
                  para:=ccallparanode.create(
                          right,
                          ccallparanode.create(
                            left,
                            ccallparanode.create(ctemprefnode.create(tempnode),nil)
                          )
                        );
                  if is_ansistring(resultdef) then
                    para:=ccallparanode.create(
                            cordconstnode.create(
                              getparaencoding(resultdef),
                              u16inttype,
                              true
                            ),
                            para
                          );
                  addstatement(
                    newstatement,
                    ccallnode.createintern(
                      'fpc_'+tstringdef(resultdef).stringtypname+'_concat',
                      para
                    )
                  );
                  addstatement(newstatement,ctempdeletenode.create_normal_temp(tempnode));
                  addstatement(newstatement,ctemprefnode.create(tempnode));
                end;
              { we reused the arguments }
              left := nil;
              right := nil;
            end;
          ltn,lten,gtn,gten,equaln,unequaln :
            begin
              { generate better code for comparison with empty string, we
                only need to compare the length with 0 }
              if (nodetype in [equaln,unequaln,gtn,gten,ltn,lten]) and
                { windows widestrings are too complicated to be handled optimized }
                not(is_widestring(left.resultdef) and (target_info.system in systems_windows)) and
                 (((left.nodetype=stringconstn) and (tstringconstnode(left).len=0)) or
                  ((right.nodetype=stringconstn) and (tstringconstnode(right).len=0))) then
                begin
                  { switch so that the constant is always on the right }
                  if left.nodetype = stringconstn then
                    begin
                      p := left;
                      left := right;
                      right := p;
                      nodetype:=swap_relation[nodetype];
                    end;
                  if is_shortstring(left.resultdef) or
                     (nodetype in [gtn,gten,ltn,lten]) or
                     (target_info.system in systems_managed_vm) then
                    { compare the length with 0 }
                    result := caddnode.create(nodetype,
                      cinlinenode.create(in_length_x,false,left),
                      cordconstnode.create(0,s32inttype,false))
                  else
                    begin
                      (*
                      if is_widestring(left.resultdef) and
                        (target_info.system in system_windows) then
                        begin
                          { windows like widestrings requires that we also check the length }
                          result:=internalstatements(newstatement);
                          tempnode:=ctempcreatenode.create(voidpointertype,voidpointertype.size,tt_persistent,true);
                          tempnode2:=ctempcreatenode.create(resultdef,resultdef.size,tt_persistent,true);
                          addstatement(newstatement,tempnode);
                          addstatement(newstatement,tempnode2);
                          { poor man's cse }
                          addstatement(newstatement,cassignmentnode.create(ctemprefnode.create(tempnode),
                            ctypeconvnode.create_internal(left,voidpointertype))
                          );
                          addstatement(newstatement,cassignmentnode.create(ctemprefnode.create(tempnode2),
                            caddnode.create(orn,
                              caddnode.create(nodetype,
                                ctemprefnode.create(tempnode),
                                cpointerconstnode.create(0,voidpointertype)
                              ),
                              caddnode.create(nodetype,
                                ctypeconvnode.create_internal(cderefnode.create(ctemprefnode.create(tempnode)),s32inttype),
                                cordconstnode.create(0,s32inttype,false)
                              )
                            )
                          ));
                          addstatement(newstatement,ctempdeletenode.create_normal_temp(tempnode));
                          addstatement(newstatement,ctempdeletenode.create_normal_temp(tempnode2));
                          addstatement(newstatement,ctemprefnode.create(tempnode2));
                        end
                      else
                      *)
                        begin
                          { compare the pointer with nil (for ansistrings etc), }
                          { faster than getting the length (JM)                 }
                          result:= caddnode.create(nodetype,
                            ctypeconvnode.create_internal(left,voidpointertype),
                            cpointerconstnode.create(0,voidpointertype));
                        end;
                    end;
                  { left is reused }
                  left := nil;
                  { right isn't }
                  right.free;
                  right := nil;
                  exit;
                end;
              { no string constant -> call compare routine }
              cmpfuncname := 'fpc_'+tstringdef(left.resultdef).stringtypname+'_compare';
              { for equality checks use optimized version }
              if nodetype in [equaln,unequaln] then
                cmpfuncname := cmpfuncname + '_equal';

              result := ccallnode.createintern(cmpfuncname,
                ccallparanode.create(right,ccallparanode.create(left,nil)));
              { and compare its result with 0 according to the original operator }
              result := caddnode.create(nodetype,result,
                cordconstnode.create(0,s32inttype,false));
              left := nil;
              right := nil;
            end;
        end;
      end;


    function taddnode.first_addset : tnode;

      procedure call_varset_helper(const n : string);
        var
          newstatement : tstatementnode;
          temp    : ttempcreatenode;
        begin
          { add two var sets }
          result:=internalstatements(newstatement);

          { create temp for result }
          temp:=ctempcreatenode.create(resultdef,resultdef.size,tt_persistent,true);
          addstatement(newstatement,temp);

          addstatement(newstatement,ccallnode.createintern(n,
            ccallparanode.create(cordconstnode.create(resultdef.size,sinttype,false),
            ccallparanode.create(ctemprefnode.create(temp),
            ccallparanode.create(right,
            ccallparanode.create(left,nil)))))
          );

          { remove reused parts from original node }
          left:=nil;
          right:=nil;
          { the last statement should return the value as
            location and type, this is done be referencing the
            temp and converting it first from a persistent temp to
            normal temp }
          addstatement(newstatement,ctempdeletenode.create_normal_temp(temp));
          addstatement(newstatement,ctemprefnode.create(temp));
        end;

      var
        procname: string[31];
        tempn: tnode;
        newstatement : tstatementnode;
        temp    : ttempcreatenode;
      begin
        result:=nil;
        case nodetype of
          equaln,unequaln,lten,gten:
            begin
              case nodetype of
                equaln,unequaln:
                  procname := 'fpc_varset_comp_sets';
                lten,gten:
                  begin
                    procname := 'fpc_varset_contains_sets';
                    { (left >= right) = (right <= left) }
                    if nodetype = gten then
                      begin
                        tempn := left;
                        left := right;
                        right := tempn;
                      end;
                    end;
                end;
                result := ccallnode.createinternres(procname,
                  ccallparanode.create(cordconstnode.create(left.resultdef.size,sinttype,false),
                  ccallparanode.create(right,
                  ccallparanode.create(left,nil))),resultdef);
                { left and right are reused as parameters }
                left := nil;
                right := nil;
                { for an unequaln, we have to negate the result of comp_sets }
                if nodetype = unequaln then
                  result := cnotnode.create(result);
            end;
          addn:
            begin
              { optimize first loading of a set }
              if (right.nodetype=setelementn) and
                  not(assigned(tsetelementnode(right).right)) and
                  is_emptyset(left) then
                begin
                  result:=internalstatements(newstatement);

                  { create temp for result }
                  temp:=ctempcreatenode.create(resultdef,resultdef.size,tt_persistent,true);
                  addstatement(newstatement,temp);

                  { adjust for set base }
                  tsetelementnode(right).left:=caddnode.create(subn,
                    ctypeconvnode.create_internal(tsetelementnode(right).left,sinttype),
                    cordconstnode.create(tsetdef(resultdef).setbase,sinttype,false));

                  addstatement(newstatement,ccallnode.createintern('fpc_varset_create_element',
                    ccallparanode.create(ctemprefnode.create(temp),
                    ccallparanode.create(cordconstnode.create(resultdef.size,sinttype,false),
                    ccallparanode.create(tsetelementnode(right).left,nil))))
                  );

                  { the last statement should return the value as
                    location and type, this is done be referencing the
                    temp and converting it first from a persistent temp to
                    normal temp }
                  addstatement(newstatement,ctempdeletenode.create_normal_temp(temp));
                  addstatement(newstatement,ctemprefnode.create(temp));

                  tsetelementnode(right).left := nil;
                end
              else
                begin
                  if right.nodetype=setelementn then
                    begin
                      result:=internalstatements(newstatement);

                      { create temp for result }
                      temp:=ctempcreatenode.create(resultdef,resultdef.size,tt_persistent,true);
                      addstatement(newstatement,temp);

                      { adjust for set base }
                      tsetelementnode(right).left:=caddnode.create(subn,
                        ctypeconvnode.create_internal(tsetelementnode(right).left,sinttype),
                        cordconstnode.create(tsetdef(resultdef).setbase,sinttype,false));

                      { add a range or a single element? }
                      if assigned(tsetelementnode(right).right) then
                        begin
                          { adjust for set base }
                          tsetelementnode(right).right:=caddnode.create(subn,
                            ctypeconvnode.create_internal(tsetelementnode(right).right,sinttype),
                            cordconstnode.create(tsetdef(resultdef).setbase,sinttype,false));
                          addstatement(newstatement,ccallnode.createintern('fpc_varset_set_range',
                            ccallparanode.create(cordconstnode.create(resultdef.size,sinttype,false),
                            ccallparanode.create(tsetelementnode(right).right,
                            ccallparanode.create(tsetelementnode(right).left,
                            ccallparanode.create(ctemprefnode.create(temp),
                            ccallparanode.create(left,nil))))))
                          );
                        end
                      else
                        addstatement(newstatement,ccallnode.createintern('fpc_varset_set',
                          ccallparanode.create(cordconstnode.create(resultdef.size,sinttype,false),
                          ccallparanode.create(ctypeconvnode.create_internal(tsetelementnode(right).left,sinttype),
                          ccallparanode.create(ctemprefnode.create(temp),
                          ccallparanode.create(left,nil)))))
                        );
                      { remove reused parts from original node }
                      tsetelementnode(right).right:=nil;
                      tsetelementnode(right).left:=nil;
                      left:=nil;
                      { the last statement should return the value as
                        location and type, this is done be referencing the
                        temp and converting it first from a persistent temp to
                        normal temp }
                      addstatement(newstatement,ctempdeletenode.create_normal_temp(temp));
                      addstatement(newstatement,ctemprefnode.create(temp));
                    end
                  else
                    call_varset_helper('fpc_varset_add_sets');
                end
            end;
          subn:
            call_varset_helper('fpc_varset_sub_sets');
          symdifn:
            call_varset_helper('fpc_varset_symdif_sets');
          muln:
            call_varset_helper('fpc_varset_mul_sets');
          else
            internalerror(200609241);
        end;
      end;


    function taddnode.use_generic_mul32to64: boolean;
      begin
        result := true;
      end;


    function taddnode.try_make_mul32to64: boolean;

      function canbe32bitint(v: tconstexprint): boolean;
        begin
          result := ((v >= int64(low(longint))) and (v <= int64(high(longint)))) or
                    ((v >= qword(low(cardinal))) and (v <= qword(high(cardinal))))
        end;

      var
        temp: tnode;
      begin
        result := false;
        if ((left.nodetype = typeconvn) and
            is_integer(ttypeconvnode(left).left.resultdef) and
            (not(torddef(ttypeconvnode(left).left.resultdef).ordtype in [u64bit,s64bit,scurrency])) and
           (((right.nodetype = ordconstn) and canbe32bitint(tordconstnode(right).value)) or
            ((right.nodetype = typeconvn) and
             is_integer(ttypeconvnode(right).left.resultdef) and
             not(torddef(ttypeconvnode(right).left.resultdef).ordtype in [u64bit,s64bit,scurrency])) and
             ((is_signed(ttypeconvnode(left).left.resultdef) =
               is_signed(ttypeconvnode(right).left.resultdef)) or
              (is_signed(ttypeconvnode(left).left.resultdef) and
               (torddef(ttypeconvnode(right).left.resultdef).ordtype in [u8bit,u16bit]))))) then
          begin
            temp := ttypeconvnode(left).left;
            ttypeconvnode(left).left := nil;
            left.free;
            left := temp;
            if (right.nodetype = typeconvn) then
              begin
                temp := ttypeconvnode(right).left;
                ttypeconvnode(right).left := nil;
                right.free;
                right := temp;
              end;
            if (is_signed(left.resultdef)) then
              begin
                inserttypeconv_internal(left,s32inttype);
                inserttypeconv_internal(right,s32inttype);
              end
            else
              begin
                inserttypeconv_internal(left,u32inttype);
                inserttypeconv_internal(right,u32inttype);
              end;
            firstpass(left);
            firstpass(right);
            result := true;
          end;
      end;


    function taddnode.first_add64bitint: tnode;
      var
        procname: string[31];
        temp: tnode;
        power: longint;
      begin
        result := nil;
        { create helper calls mul }
        if nodetype <> muln then
          exit;

        { make sure that if there is a constant, that it's on the right }
        if left.nodetype = ordconstn then
          begin
            temp := right;
            right := left;
            left := temp;
          end;

        { can we use a shift instead of a mul? }
        if not (cs_check_overflow in current_settings.localswitches) and
           (right.nodetype = ordconstn) and
           ispowerof2(tordconstnode(right).value,power) then
          begin
            tordconstnode(right).value := power;
            result := cshlshrnode.create(shln,left,right);
            { left and right are reused }
            left := nil;
            right := nil;
            { return firstpassed new node }
            exit;
          end;

        if not(use_generic_mul32to64) and
           try_make_mul32to64 then
          exit;

        { when currency is used set the result of the
          parameters to s64bit, so they are not converted }
        if is_currency(resultdef) then
          begin
            left.resultdef:=s64inttype;
            right.resultdef:=s64inttype;
          end;

        { otherwise, create the parameters for the helper }
        right := ccallparanode.create(
          cordconstnode.create(ord(cs_check_overflow in current_settings.localswitches),pasbool8type,true),
          ccallparanode.create(right,ccallparanode.create(left,nil)));
        left := nil;
        { only qword needs the unsigned code, the
          signed code is also used for currency }
        if is_signed(resultdef) then
          procname := 'fpc_mul_int64'
        else
          procname := 'fpc_mul_qword';
        result := ccallnode.createintern(procname,right);
        right := nil;
      end;


    function taddnode.first_addfloat : tnode;
      var
        procname: string[31];
        { do we need to reverse the result ? }
        notnode : boolean;
        fdef : tdef;
      begin
        result := nil;
        notnode := false;
        { In non-emulation mode, real opcodes are
          emitted for floating point values.
        }
        if not (cs_fp_emulation in current_settings.moduleswitches) then
          exit;

        if not(target_info.system in systems_wince) then
          begin
            case tfloatdef(left.resultdef).floattype of
              s32real:
                begin
                  fdef:=search_system_type('FLOAT32REC').typedef;
                  procname:='float32';
                end;
              s64real:
                begin
                  fdef:=search_system_type('FLOAT64').typedef;
                  procname:='float64';
                end;
              {!!! not yet implemented
              s128real:
              }
              else
                internalerror(2005082601);
            end;

            case nodetype of
              addn:
                procname:=procname+'_add';
              muln:
                procname:=procname+'_mul';
              subn:
                procname:=procname+'_sub';
              slashn:
                procname:=procname+'_div';
              ltn:
                procname:=procname+'_lt';
              lten:
                procname:=procname+'_le';
              gtn:
                begin
                  procname:=procname+'_le';
                  notnode:=true;
                end;
              gten:
                begin
                  procname:=procname+'_lt';
                  notnode:=true;
                end;
              equaln:
                procname:=procname+'_eq';
              unequaln:
                begin
                  procname:=procname+'_eq';
                  notnode:=true;
                end;
              else
                CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),left.resultdef.typename,right.resultdef.typename);
            end;
          end
        else
          begin
            case nodetype of
              addn:
                procname:='ADD';
              muln:
                procname:='MUL';
              subn:
                procname:='SUB';
              slashn:
                procname:='DIV';
              ltn:
                procname:='LT';
              lten:
                procname:='LE';
              gtn:
                procname:='GT';
              gten:
                procname:='GE';
              equaln:
                procname:='EQ';
              unequaln:
                procname:='NE';
              else
                CGMessage3(type_e_operator_not_supported_for_types,node2opstr(nodetype),left.resultdef.typename,right.resultdef.typename);
            end;
            case tfloatdef(left.resultdef).floattype of
              s32real:
                begin
                  procname:=procname+'S';
                  if nodetype in [addn,muln,subn,slashn] then
                    procname:=lower(procname);
                end;
              s64real:
                procname:=procname+'D';
              {!!! not yet implemented
              s128real:
              }
              else
                internalerror(2005082602);
            end;

          end;
        { cast softfpu result? }
        if not(target_info.system in systems_wince) then
          begin
            if nodetype in [ltn,lten,gtn,gten,equaln,unequaln] then
              resultdef:=pasbool8type;
            result:=ctypeconvnode.create_internal(ccallnode.createintern(procname,ccallparanode.create(
                ctypeconvnode.create_internal(right,fdef),
                ccallparanode.create(
                  ctypeconvnode.create_internal(left,fdef),nil))),resultdef);
          end
        else
          result:=ccallnode.createintern(procname,ccallparanode.create(right,
             ccallparanode.create(left,nil)));
        left:=nil;
        right:=nil;

        { do we need to reverse the result }
        if notnode then
          result:=cnotnode.create(result);
      end;


    function taddnode.pass_1 : tnode;
      var
{$ifdef addstringopt}
         hp      : tnode;
{$endif addstringopt}
         rd,ld   : tdef;
         i       : longint;
         lt,rt   : tnodetype;
{$ifdef cpuneedsmulhelper}
         procname : string[32];
{$endif cpuneedsmulhelper}
      begin
         result:=nil;
         { Can we optimize multiple string additions into a single call?
           This need to be done on a complete tree to detect the multiple
           add nodes and is therefor done before the subtrees are processed }
         if canbemultistringadd(self) then
           begin
             result:=genmultistringadd(self);
             exit;
           end;
         { first do the two subtrees }
         firstpass(left);
         firstpass(right);

         if codegenerror then
           exit;

         { load easier access variables }
         rd:=right.resultdef;
         ld:=left.resultdef;
         rt:=right.nodetype;
         lt:=left.nodetype;

         { int/int gives real/real! }
         if nodetype=slashn then
           begin
{$ifdef cpufpemu}
             if (current_settings.fputype=fpu_soft) or (cs_fp_emulation in current_settings.moduleswitches) then
               begin
                 result:=first_addfloat;
                 if assigned(result) then
                   exit;
               end;
{$endif cpufpemu}
             expectloc:=LOC_FPUREGISTER;
           end

         { if both are orddefs then check sub types }
         else if (ld.typ=orddef) and (rd.typ=orddef) then
           begin
             { optimize multiplacation by a power of 2 }
             if not(cs_check_overflow in current_settings.localswitches) and
                (nodetype = muln) and
                (((left.nodetype = ordconstn) and
                  ispowerof2(tordconstnode(left).value,i)) or
                 ((right.nodetype = ordconstn) and
                  ispowerof2(tordconstnode(right).value,i))) then
               begin
                 if left.nodetype = ordconstn then
                   begin
                     tordconstnode(left).value := i;
                     result := cshlshrnode.create(shln,right,left);
                   end
                 else
                   begin
                     tordconstnode(right).value := i;
                     result := cshlshrnode.create(shln,left,right);
                   end;
                 left := nil;
                 right := nil;
                 exit;
               end;

           { 2 booleans ? }
             if is_boolean(ld) and is_boolean(rd) then
              begin
                if (not(cs_full_boolean_eval in current_settings.localswitches) or
                    (nf_short_bool in flags)) and
                   (nodetype in [andn,orn]) then
                  expectloc:=LOC_JUMP
                else
                 begin
                   if nodetype in [ltn,lten,gtn,gten,equaln,unequaln] then
                     expectloc:=LOC_FLAGS
                   else
                     expectloc:=LOC_REGISTER;
                 end;
              end
             else
             { Both are chars? only convert to shortstrings for addn }
              if is_char(ld) then
               begin
                 if nodetype=addn then
                  internalerror(200103291);
                 expectloc:=LOC_FLAGS;
               end
{$ifndef cpu64bitalu}
              { is there a 64 bit type ? }
             else if (torddef(ld).ordtype in [s64bit,u64bit,scurrency]) then
               begin
                 result := first_add64bitint;
                 if assigned(result) then
                   exit;
                  if nodetype in [addn,subn,muln,andn,orn,xorn] then
                    expectloc:=LOC_REGISTER
                  else
                    expectloc:=LOC_JUMP;
               end
{$endif cpu64bitalu}
{$ifndef cpuneedsmulhelper}
             { is there a cardinal? }
             else if (torddef(ld).ordtype=u32bit) then
               begin
                  if nodetype in [addn,subn,muln,andn,orn,xorn] then
                    expectloc:=LOC_REGISTER
                  else
                    expectloc:=LOC_FLAGS;
               end
{$endif cpuneedsmulhelper}
             { generic s32bit conversion }
             else
               begin
{$ifdef cpuneedsmulhelper}
                 if (nodetype=muln) and not(torddef(resultdef).ordtype in [u8bit,s8bit]) then
                   begin
                     result := nil;

                     case torddef(resultdef).ordtype of
                       s16bit:
                         procname := 'fpc_mul_integer';
                       u16bit:
                         procname := 'fpc_mul_word';
                       s32bit:
                         procname := 'fpc_mul_longint';
                       u32bit:
                         procname := 'fpc_mul_dword';
                       else
                         internalerror(2011022301);
                     end;
                     result := ccallnode.createintern(procname,
                       ccallparanode.create(cordconstnode.create(0,pasbool8type,false),
                       ccallparanode.create(right,
                       ccallparanode.create(left,nil))));
                     left := nil;
                     right := nil;
                     firstpass(result);
                     exit;
                   end;
{$endif cpuneedsmulhelper}
                  if nodetype in [addn,subn,muln,andn,orn,xorn] then
                    expectloc:=LOC_REGISTER
                  else
                    expectloc:=LOC_FLAGS;
               end;
           end

         { left side a setdef, must be before string processing,
           else array constructor can be seen as array of char (PFV) }
         else if (ld.typ=setdef) then
           begin
             { small sets are handled inline by the compiler.
               small set doesn't have support for adding ranges }
             if is_smallset(ld) and
                not(
                    (right.nodetype=setelementn) and
                    assigned(tsetelementnode(right).right)
                   ) then
               begin
                 if nodetype in [ltn,lten,gtn,gten,equaln,unequaln] then
                   expectloc:=LOC_FLAGS
                 else
                   expectloc:=LOC_REGISTER;
               end
             else
               begin
                 result := first_addset;
                 if assigned(result) then
                   exit;
                 expectloc:=LOC_CREFERENCE;
               end;
           end

         { compare pchar by addresses like BP/Delphi }
         else if is_pchar(ld) then
           begin
             if nodetype in [addn,subn,muln,andn,orn,xorn] then
               expectloc:=LOC_REGISTER
             else
               expectloc:=LOC_FLAGS;
           end

         { is one of the operands a string }
         else if (ld.typ=stringdef) then
            begin
              if is_widestring(ld) then
                begin
                   { this is only for add, the comparisaion is handled later }
                   expectloc:=LOC_REGISTER;
                end
              else if is_unicodestring(ld) then
                begin
                   { this is only for add, the comparisaion is handled later }
                   expectloc:=LOC_REGISTER;
                end
              else if is_ansistring(ld) then
                begin
                   { this is only for add, the comparisaion is handled later }
                   expectloc:=LOC_REGISTER;
                end
              else if is_longstring(ld) then
                begin
                   { this is only for add, the comparisaion is handled later }
                   expectloc:=LOC_REFERENCE;
                end
              else
                begin
{$ifdef addstringopt}
                   { can create a call which isn't handled by callparatemp }
                   if canbeaddsstringcharoptnode(self) then
                     begin
                       hp := genaddsstringcharoptnode(self);
                       pass_1 := hp;
                       exit;
                     end
                   else
{$endif addstringopt}
                     begin
                       { Fix right to be shortstring }
                       if is_char(right.resultdef) then
                        begin
                          inserttypeconv(right,cshortstringtype);
                          firstpass(right);
                        end;
                     end;
{$ifdef addstringopt}
                   { can create a call which isn't handled by callparatemp }
                   if canbeaddsstringcsstringoptnode(self) then
                     begin
                       hp := genaddsstringcsstringoptnode(self);
                       pass_1 := hp;
                       exit;
                     end;
{$endif addstringopt}
                end;
             { otherwise, let addstring convert everything }
              result := first_addstring;
              exit;
           end

         { is one a real float ? }
         else if (rd.typ=floatdef) or (ld.typ=floatdef) then
            begin
{$ifdef cpufpemu}
             if (current_settings.fputype=fpu_soft) or (cs_fp_emulation in current_settings.moduleswitches) then
               begin
                 result:=first_addfloat;
                 if assigned(result) then
                   exit;
               end;
{$endif cpufpemu}
              if nodetype in [addn,subn,muln,andn,orn,xorn] then
                expectloc:=LOC_FPUREGISTER
              else
                expectloc:=LOC_FLAGS;
            end

         { pointer comperation and subtraction }
         else if (ld.typ=pointerdef) then
            begin
              if nodetype in [addn,subn,muln,andn,orn,xorn] then
                expectloc:=LOC_REGISTER
              else
                expectloc:=LOC_FLAGS;
           end

         else if is_implicit_pointer_object_type(ld) then
            begin
              expectloc:=LOC_FLAGS;
            end

         else if (ld.typ=classrefdef) then
            begin
              expectloc:=LOC_FLAGS;
            end

         { support procvar=nil,procvar<>nil }
         else if ((ld.typ=procvardef) and (rt=niln)) or
                 ((rd.typ=procvardef) and (lt=niln)) then
            begin
              expectloc:=LOC_FLAGS;
            end

{$ifdef SUPPORT_MMX}
       { mmx support, this must be before the zero based array
         check }
         else if (cs_mmx in current_settings.localswitches) and is_mmx_able_array(ld) and
                 is_mmx_able_array(rd) then
            begin
              expectloc:=LOC_MMXREGISTER;
            end
{$endif SUPPORT_MMX}

         else if (rd.typ=pointerdef) or (ld.typ=pointerdef) then
            begin
              expectloc:=LOC_REGISTER;
            end

         else  if (rd.typ=procvardef) and
                  (ld.typ=procvardef) and
                  equal_defs(rd,ld) then
           begin
             expectloc:=LOC_FLAGS;
           end

         else if (ld.typ=enumdef) then
           begin
              expectloc:=LOC_FLAGS;
           end

{$ifdef SUPPORT_MMX}
         else if (cs_mmx in current_settings.localswitches) and
                 is_mmx_able_array(ld) and
                 is_mmx_able_array(rd) then
            begin
              expectloc:=LOC_MMXREGISTER;
            end
{$endif SUPPORT_MMX}

         { the general solution is to convert to 32 bit int }
         else
           begin
             expectloc:=LOC_REGISTER;
           end;
      end;

{$ifdef state_tracking}
    function Taddnode.track_state_pass(exec_known:boolean):boolean;

    var factval:Tnode;

    begin
    track_state_pass:=false;
    if left.track_state_pass(exec_known) then
      begin
        track_state_pass:=true;
        left.resultdef:=nil;
        do_typecheckpass(left);
      end;
    factval:=aktstate.find_fact(left);
    if factval<>nil then
        begin
        track_state_pass:=true;
            left.destroy;
            left:=factval.getcopy;
        end;
    if right.track_state_pass(exec_known) then
        begin
        track_state_pass:=true;
        right.resultdef:=nil;
        do_typecheckpass(right);
        end;
    factval:=aktstate.find_fact(right);
    if factval<>nil then
        begin
        track_state_pass:=true;
            right.destroy;
            right:=factval.getcopy;
        end;
    end;
{$endif}

end.
