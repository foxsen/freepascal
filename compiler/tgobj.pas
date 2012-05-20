{
    Copyright (c) 1998-2002 by Florian Klaempfl

    This unit implements the base object for temp. generator

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
{#@abstract(Temporary reference allocator unit)
  Temporary reference allocator unit. This unit contains
  all which is related to allocating temporary memory
  space on the stack, as required, by the code generator.
}

unit tgobj;

{$i fpcdefs.inc}

  interface

    uses
      cclasses,
      globals,globtype,
      symtype,
      cpubase,cpuinfo,cgbase,cgutils,
      aasmbase,aasmtai,aasmdata;

    type
      ptemprecord = ^ttemprecord;
      ttemprecord = record
         temptype   : ttemptype;
         pos        : longint;
         size       : longint;
         def        : tdef;
         next       : ptemprecord;
         nextfree   : ptemprecord; { for faster freeblock checking }
{$ifdef EXTDEBUG}
         posinfo,
         releaseposinfo : tfileposinfo;
{$endif}
      end;


       {# Generates temporary variables }
       ttgobj = class
       protected
          { contains all free temps using nextfree links }
          tempfreelist  : ptemprecord;
          function alloctemp(list: TAsmList; size,alignment : longint; temptype : ttemptype; def:tdef) : longint; virtual;
          procedure freetemp(list: TAsmList; pos:longint;temptypes:ttemptypeset);
          procedure gettempinternal(list: TAsmList; size, alignment : longint;temptype:ttemptype;def: tdef;out ref : treference);
       public
          { contains all temps }
          templist      : ptemprecord;
          { Offsets of the first/last temp }
          firsttemp,
          lasttemp      : longint;
          direction : shortint;
          constructor create;virtual;reintroduce;
          {# Clear and free the complete linked list of temporary memory
             locations. The list is set to nil.}
          procedure resettempgen;
          {# Sets the first offset from the frame pointer or stack pointer where
             the temporary references will be allocated. It is to note that this
             value should always be negative.

             @param(l start offset where temps will start in stack)
          }
          procedure setfirsttemp(l : longint); virtual;

          { version of gettemp that is compatible with hlcg-based targets;
            always use in common code, only use gettemp in cgobj and
            architecture-specific backends.

            the forcesize parameter is so that it can be used for defs that
            don't have an inherent size (e.g., array of const) }
          procedure gethltemp(list: TAsmList; def: tdef; forcesize: aint; temptype: ttemptype; out ref: treference); virtual;
          procedure gethltemptyped(list: TAsmList; def: tdef; temptype: ttemptype; out ref: treference); virtual;
          procedure gettemp(list: TAsmList; size, alignment : longint;temptype:ttemptype;out ref : treference);
          procedure gettemptyped(list: TAsmList; def:tdef;temptype:ttemptype;out ref : treference);
          procedure ungettemp(list: TAsmList; const ref : treference);

          function sizeoftemp(list: TAsmList; const ref: treference): longint;
          function changetemptype(list: TAsmList; const ref:treference;temptype:ttemptype):boolean;
          function gettypeoftemp(const ref:treference): ttemptype;

          {# Returns TRUE if the reference ref is allocated in temporary volatile memory space,
             otherwise returns FALSE.

             @param(ref reference to verify)
          }
          function istemp(const ref : treference) : boolean;
          {# Frees a reference @var(ref) which was allocated in the volatile temporary memory space.
             The freed space can later be reallocated and reused. If this reference
             is not in the temporary memory, it is simply not freed.
          }
          procedure ungetiftemp(list: TAsmList; const ref : treference);

          { Allocate space for a local }
          procedure getlocal(list: TAsmList; size : longint;def:tdef;var ref : treference);
          procedure getlocal(list: TAsmList; size : longint; alignment : shortint; def:tdef;var ref : treference); virtual;
          procedure UnGetLocal(list: TAsmList; const ref : treference);
       end;
       ttgobjclass = class of ttgobj;

     var
       tg: ttgobj;
       tgobjclass: ttgobjclass = ttgobj;

    procedure location_freetemp(list:TAsmList; const l : tlocation);


implementation

    uses
       cutils,
       systems,verbose,
       procinfo,
       symconst
       ;


    const
      FreeTempTypes = [tt_free,tt_freenoreuse,tt_freeregallocator];

{$ifdef EXTDEBUG}
      TempTypeStr : array[ttemptype] of string[18] = (
          '<none>',
          'free','normal','persistant',
          'noreuse','freenoreuse',
          'regallocator','freeregallocator'
      );
{$endif EXTDEBUG}

      Used2Free : array[ttemptype] of ttemptype = (
        tt_none,
        tt_none,tt_free,tt_free,
        tt_freenoreuse,tt_none,
        tt_freeregallocator,tt_none
      );


{*****************************************************************************
                                    Helpers
*****************************************************************************}

    procedure location_freetemp(list:TAsmList; const l : tlocation);
      begin
        if (l.loc in [LOC_REFERENCE,LOC_CREFERENCE]) then
         tg.ungetiftemp(list,l.reference);
      end;


{*****************************************************************************
                                    TTGOBJ
*****************************************************************************}

    constructor ttgobj.create;

     begin
       tempfreelist:=nil;
       templist:=nil;
       { we could create a new child class for this but I don't if it is worth the effort (FK) }
{$if defined(powerpc) or defined(powerpc64) or defined(avr) or defined(jvm)}
       direction:=1;
{$else}
       direction:=-1;
{$endif}
     end;


    procedure ttgobj.resettempgen;
      var
         hp : ptemprecord;
      begin
        { Clear the old templist }
        while assigned(templist) do
         begin
{$ifdef EXTDEBUG}
           if not(templist^.temptype in FreeTempTypes) then
             begin
               Comment(V_Warning,'tgobj: (ResetTempgen) temp at pos '+tostr(templist^.pos)+
                       ' with size '+tostr(templist^.size)+' and type '+TempTypeStr[templist^.temptype]+
                       ' from pos '+tostr(templist^.posinfo.line)+':'+tostr(templist^.posinfo.column)+
                       ' not freed at the end of the procedure');
             end;
{$endif EXTDEBUG}
           hp:=templist;
           templist:=hp^.next;
           dispose(hp);
         end;
        templist:=nil;
        tempfreelist:=nil;
        firsttemp:=0;
        lasttemp:=0;
      end;


    procedure ttgobj.setfirsttemp(l : longint);
      begin
         { this is a negative value normally }
         if l*direction>=0 then
          begin
            if odd(l) then
             inc(l,direction);
          end
         else
           internalerror(200204221);
         firsttemp:=l;
         lasttemp:=l;
      end;


    function ttgobj.AllocTemp(list: TAsmList; size,alignment : longint; temptype : ttemptype;def : tdef) : longint;
      var
         tl,htl,
         bestslot,bestprev,
         hprev,hp : ptemprecord;
         freetype : ttemptype;
         bestatend,
         fitatbegin,
         fitatend : boolean;
      begin
         AllocTemp:=0;
         bestprev:=nil;
         bestslot:=nil;
         tl:=nil;
         bestatend:=false;

         if size=0 then
          begin
{$ifdef EXTDEBUG}
            Comment(V_Warning,'tgobj: (AllocTemp) temp of size 0 requested, allocating 4 bytes');
{$endif}
            size:=4;
          end;

         freetype:=Used2Free[temptype];
         if freetype=tt_none then
           internalerror(200208201);
         size:=align(size,alignment);
         { First check the tmpfreelist, but not when
           we don't want to reuse an already allocated block }
         if assigned(tempfreelist) and
            (temptype<>tt_noreuse) then
          begin
            hprev:=nil;
            hp:=tempfreelist;
            while assigned(hp) do
             begin
{$ifdef EXTDEBUG}
               if not(hp^.temptype in FreeTempTypes) then
                 Comment(V_Warning,'tgobj: (AllocTemp) temp at pos '+tostr(hp^.pos)+ ' in freelist is not set to tt_free !');
{$endif}
               { Check only slots that are
                  - free
                  - share the same type
                  - contain enough space
                  - has a correct alignment }
               if (hp^.temptype=freetype) and
                  (hp^.def=def) and
                  (hp^.size>=size) and
                  ((hp^.pos=align(hp^.pos,alignment)) or
                   (hp^.pos+hp^.size-size = align(hp^.pos+hp^.size-size,alignment))) then
                begin
                  { Slot is the same size then leave immediatly }
                  if (hp^.size=size) then
                   begin
                     bestprev:=hprev;
                     bestslot:=hp;
                     break;
                   end
                  else
                   begin
                     { we can fit a smaller block either at the begin or at }
                     { the end of a block. For direction=-1 we prefer the   }
                     { end, for direction=1 we prefer the begin (i.e.,      }
                     { always closest to the source). We also try to use    }
                     { the block with the worst possible alignment that     }
                     { still suffices. And we pick the block which will     }
                     { have the best alignmenment after this new block is   }
                     { substracted from it.                                 }
                     fitatend:=(hp^.pos+hp^.size-size)=align(hp^.pos+hp^.size-size,alignment);
                     fitatbegin:=hp^.pos=align(hp^.pos,alignment);
                     if assigned(bestslot) then
                       begin
                         fitatend:=fitatend and
                           ((not bestatend and
                             (direction=-1)) or
                            (bestatend and
                             isbetteralignedthan(abs(bestslot^.pos+hp^.size-size),abs(hp^.pos+hp^.size-size),current_settings.alignment.localalignmax)));
                         fitatbegin:=fitatbegin and
                           (not bestatend or
                            (direction=1)) and
                           isbetteralignedthan(abs(hp^.pos+size),abs(bestslot^.pos+size),current_settings.alignment.localalignmax);
                       end;
                     if fitatend and
                        fitatbegin then
                       if isbetteralignedthan(abs(hp^.pos+hp^.size-size),abs(hp^.pos+size),current_settings.alignment.localalignmax) then
                         fitatbegin:=false
                       else if isbetteralignedthan(abs(hp^.pos+size),abs(hp^.pos+hp^.size-size),current_settings.alignment.localalignmax) then
                         fitatend:=false
                       else if (direction=1) then
                         fitatend:=false
                       else
                         fitatbegin:=false;
                     if fitatend or
                        fitatbegin then
                      begin
                        bestprev:=hprev;
                        bestslot:=hp;
                        bestatend:=fitatend;
                      end;
                   end;
                end;
               hprev:=hp;
               hp:=hp^.nextfree;
             end;
          end;
         { Reuse an old temp ? }
         if assigned(bestslot) then
          begin
            if bestslot^.size=size then
             begin
               tl:=bestslot;
               { Remove from the tempfreelist }
               if assigned(bestprev) then
                 bestprev^.nextfree:=tl^.nextfree
               else
                 tempfreelist:=tl^.nextfree;
             end
            else
             begin
               { Duplicate bestlost and the block in the list }
               new(tl);
               move(bestslot^,tl^,sizeof(ttemprecord));
               tl^.next:=bestslot^.next;
               bestslot^.next:=tl;
               { Now we split the block in 2 parts. Depending on the direction
                 we need to resize the newly inserted block or the old reused block.
                 For direction=1 we can use tl for the new block. For direction=-1 we
                 will be reusing bestslot and resize the new block, that means we need
                 to swap the pointers }
               if (direction=-1) xor
                  bestatend then
                 begin
                   htl:=tl;
                   tl:=bestslot;
                   bestslot:=htl;
                   { Update the tempfreelist to point to the new block }
                   if assigned(bestprev) then
                     bestprev^.nextfree:=bestslot
                   else
                     tempfreelist:=bestslot;
                 end;

               if not bestatend then
                 inc(bestslot^.pos,size)
               else
                 inc(tl^.pos,tl^.size-size);

               { Create new block and resize the old block }
               tl^.size:=size;
               tl^.nextfree:=nil;
               { Resize the old block }
               dec(bestslot^.size,size);
             end;
            tl^.temptype:=temptype;
            tl^.def:=def;
            tl^.nextfree:=nil;
          end
         else
          begin
            { now we can create the templist entry }
            new(tl);
            tl^.temptype:=temptype;
            tl^.def:=def;

            { Extend the temp }
            if direction=-1 then
              begin
                 lasttemp:=(-align(-lasttemp,alignment))-size;
                 tl^.pos:=lasttemp;
              end
            else
              begin
                 tl^.pos:=align(lasttemp,alignment);
                 lasttemp:=tl^.pos+size;
              end;

            tl^.size:=size;
            tl^.next:=templist;
            tl^.nextfree:=nil;
            templist:=tl;
          end;
{$ifdef EXTDEBUG}
         tl^.posinfo:=current_filepos;
         if assigned(tl^.def) then
           list.concat(tai_tempalloc.allocinfo(tl^.pos,tl^.size,'allocated with type '+TempTypeStr[tl^.temptype]+' for def '+tl^.def.typename))
         else
           list.concat(tai_tempalloc.allocinfo(tl^.pos,tl^.size,'allocated with type '+TempTypeStr[tl^.temptype]));
{$else}
         list.concat(tai_tempalloc.alloc(tl^.pos,tl^.size));
{$endif}
         AllocTemp:=tl^.pos;
      end;


    procedure ttgobj.FreeTemp(list: TAsmList; pos:longint;temptypes:ttemptypeset);
      var
         hp,hnext,hprev,hprevfree : ptemprecord;
      begin
         hp:=templist;
         hprev:=nil;
         hprevfree:=nil;
         while assigned(hp) do
          begin
            if (hp^.pos=pos) then
             begin
               { check if already freed }
               if hp^.temptype in FreeTempTypes then
                begin
{$ifdef EXTDEBUG}
                  Comment(V_Warning,'tgobj: (FreeTemp) temp at pos '+tostr(pos)+ ' is already free !');
                  list.concat(tai_tempalloc.allocinfo(hp^.pos,hp^.size,'temp is already freed'));
{$endif}
                  exit;
                end;
               { check type that are allowed to be released }
               if not(hp^.temptype in temptypes) then
                begin
{$ifdef EXTDEBUG}
                  Comment(V_Debug,'tgobj: (Freetemp) temp at pos '+tostr(pos)+ ' has different type ('+TempTypeStr[hp^.temptype]+'), not releasing');
                  list.concat(tai_tempalloc.allocinfo(hp^.pos,hp^.size,'temp has wrong type ('+TempTypeStr[hp^.temptype]+') not releasing'));
{$endif}
                  exit;
                end;
               list.concat(tai_tempalloc.dealloc(hp^.pos,hp^.size));
               { set this block to free }
               hp^.temptype:=Used2Free[hp^.temptype];
               { Update tempfreelist }
               if assigned(hprevfree) then
                begin
                  { Concat blocks when the previous block is free and
                    there is no block assigned for a tdef }
                  if assigned(hprev) and
                     (hp^.temptype=tt_free) and
                     not assigned(hp^.def) and
                     (hprev^.temptype=tt_free) and
                     not assigned(hprev^.def) then
                   begin
                     inc(hprev^.size,hp^.size);
                     if direction=1 then
                       hprev^.pos:=hp^.pos;
                     hprev^.next:=hp^.next;
                     dispose(hp);
                     hp:=hprev;
                   end
                  else
                   hprevfree^.nextfree:=hp;
                end
               else
                begin
                  hp^.nextfree:=tempfreelist;
                  tempfreelist:=hp;
                end;
               { Concat blocks when the next block is free and
                 there is no block assigned for a tdef }
               hnext:=hp^.next;
               if assigned(hnext) and
                  (hp^.temptype=tt_free) and
                  not assigned(hp^.def) and
                  (hnext^.temptype=tt_free) and
                  not assigned(hnext^.def) then
                begin
                  inc(hp^.size,hnext^.size);
                  if direction=1 then
                    hp^.pos:=hnext^.pos;
                  hp^.nextfree:=hnext^.nextfree;
                  hp^.next:=hnext^.next;
                  dispose(hnext);
                end;
               { Stop }
               exit;
             end;
            if (hp^.temptype=tt_free) then
              hprevfree:=hp;
            hprev:=hp;
            hp:=hp^.next;
          end;
      end;


    procedure ttgobj.gethltemp(list: TAsmList; def: tdef; forcesize: aint; temptype: ttemptype; out ref: treference);
      begin
        gettemp(list,forcesize,def.alignment,temptype,ref);
      end;


    procedure ttgobj.gethltemptyped(list: TAsmList; def: tdef; temptype: ttemptype; out ref: treference);
      begin
        gettemptyped(list,def,temptype,ref);
      end;



    procedure ttgobj.gettemp(list: TAsmList; size, alignment : longint;temptype:ttemptype;out ref : treference);
      begin
        gettempinternal(list,size,alignment,temptype,nil,ref);
      end;


    procedure ttgobj.gettempinternal(list: TAsmList; size, alignment : longint;temptype:ttemptype;def: tdef;out ref : treference);
      var
        varalign : shortint;
      begin
        varalign:=used_align(alignment,current_settings.alignment.localalignmin,current_settings.alignment.localalignmax);
        { can't use reference_reset_base, because that will let tgobj depend
          on cgobj (PFV) }
        fillchar(ref,sizeof(ref),0);
        ref.base:=current_procinfo.framepointer;
        ref.offset:=alloctemp(list,size,varalign,temptype,def);
        ref.alignment:=varalign;
      end;


    procedure ttgobj.gettemptyped(list: TAsmList; def:tdef;temptype:ttemptype;out ref : treference);
      begin
        gettempinternal(list,def.size,def.alignment,temptype,def,ref);
      end;


    function ttgobj.istemp(const ref : treference) : boolean;
      begin
         { ref.index = R_NO was missing
           led to problems with local arrays
           with lower bound > 0 (PM) }
         if direction = 1 then
           begin
             istemp:=(ref.base=current_procinfo.framepointer) and
                     (ref.index=NR_NO) and
                     (ref.offset>=firsttemp);
           end
        else
           begin
             istemp:=(ref.base=current_procinfo.framepointer) and
                     (ref.index=NR_NO) and
                     (ref.offset<firsttemp);
           end;
      end;


    function ttgobj.sizeoftemp(list: TAsmList; const ref: treference): longint;
      var
         hp : ptemprecord;
      begin
         SizeOfTemp := -1;
         hp:=templist;
         while assigned(hp) do
           begin
             if (hp^.pos=ref.offset) then
               begin
                 sizeoftemp := hp^.size;
                 exit;
               end;
             hp := hp^.next;
           end;
{$ifdef EXTDEBUG}
         comment(v_debug,'tgobj: (SizeOfTemp) temp at pos '+tostr(ref.offset)+' not found !');
         list.concat(tai_tempalloc.allocinfo(ref.offset,0,'temp not found'));
{$endif}
      end;


    function ttgobj.changetemptype(list: tasmList; const ref:treference; temptype:ttemptype):boolean;
      var
        hp : ptemprecord;
      begin
         ChangeTempType:=false;
         hp:=templist;
         while assigned(hp) do
          begin
            if (hp^.pos=ref.offset) then
             begin
               if hp^.temptype<>tt_free then
                begin
{$ifdef EXTDEBUG}
                  if hp^.temptype=temptype then
                    Comment(V_Warning,'tgobj: (ChangeTempType) temp'+
                       ' at pos '+tostr(ref.offset)+ ' is already of the correct type !');
                  list.concat(tai_tempalloc.allocinfo(hp^.pos,hp^.size,'type changed to '+TempTypeStr[temptype]));
{$endif}
                  ChangeTempType:=true;
                  hp^.temptype:=temptype;
                end
               else
                begin
{$ifdef EXTDEBUG}
                   Comment(V_Warning,'tgobj: (ChangeTempType) temp'+
                      ' at pos '+tostr(ref.offset)+ ' is already freed !');
                  list.concat(tai_tempalloc.allocinfo(hp^.pos,hp^.size,'temp is already freed'));
{$endif}
                end;
               exit;
             end;
            hp:=hp^.next;
          end;
{$ifdef EXTDEBUG}
         Comment(V_Warning,'tgobj: (ChangeTempType) temp'+
            ' at pos '+tostr(ref.offset)+ ' not found !');
         list.concat(tai_tempalloc.allocinfo(ref.offset,0,'temp not found'));
{$endif}
      end;


    function ttgobj.gettypeoftemp(const ref:treference): ttemptype;
      var
        hp : ptemprecord;
      begin
         hp:=templist;
         while assigned(hp) do
          begin
            if (hp^.pos=ref.offset) then
             begin
               if hp^.temptype<>tt_free then
                 result:=hp^.temptype
               else
                 internalerror(2007020810);
               exit;
             end;
            hp:=hp^.next;
          end;
        result:=tt_none;
      end;


    procedure ttgobj.UnGetTemp(list: TAsmList; const ref : treference);
      begin
        FreeTemp(list,ref.offset,[tt_normal,tt_noreuse,tt_persistent,tt_regallocator]);
      end;


    procedure ttgobj.UnGetIfTemp(list: TAsmList; const ref : treference);
      begin
        if istemp(ref) then
          FreeTemp(list,ref.offset,[tt_normal]);
      end;


    procedure ttgobj.getlocal(list: TAsmList; size : longint;def:tdef;var ref : treference);
      begin
        getlocal(list, size, def.alignment, def, ref);
      end;


    procedure ttgobj.getlocal(list: TAsmList; size : longint; alignment : shortint; def:tdef;var ref : treference);
      begin
        alignment:=used_align(alignment,current_settings.alignment.localalignmin,current_settings.alignment.localalignmax);
        { can't use reference_reset_base, because that will let tgobj depend
          on cgobj (PFV) }
        fillchar(ref,sizeof(ref),0);
        ref.base:=current_procinfo.framepointer;
        ref.offset:=alloctemp(list,size,alignment,tt_persistent,nil);
        ref.alignment:=alignment;
      end;


    procedure ttgobj.UnGetLocal(list: TAsmList; const ref : treference);
      begin
        FreeTemp(list,ref.offset,[tt_persistent]);
      end;

end.
