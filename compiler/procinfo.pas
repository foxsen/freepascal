{
    Copyright (c) 1998-2002 by Florian Klaempfl

    Information about the current procedure that is being compiled

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
unit procinfo;

{$i fpcdefs.inc}

  interface

    uses
      { common }
      cclasses,
      { global }
      globtype,globals,verbose,
      { symtable }
      symconst,symtype,symdef,symsym,
      { aasm }
      cpubase,cpuinfo,cgbase,cgutils,
      aasmbase,aasmtai,aasmdata,
      optutils
      ;

    const
      inherited_inlining_flags : tprocinfoflags =
        [pi_do_call,
         { the stack frame can't be removed in this case }
         pi_has_assembler_block,
         pi_uses_exceptions];


    type
       tsavedlabels = array[Boolean] of TAsmLabel;

       { This object gives information on the current routine being
         compiled.
       }
       tprocinfo = class(tlinkedlistitem)
       private
          { list to store the procinfo's of the nested procedures }
          nestedprocs : tlinkedlist;
          procedure addnestedproc(child: tprocinfo);
       public
          { pointer to parent in nested procedures }
          parent : tprocinfo;
          { the definition of the routine itself }
          procdef : tprocdef;
          { nested implicit finalzation procedure, used for platform-specific
            exception handling }
          finalize_procinfo : tprocinfo;
          { file location of begin of procedure }
          entrypos  : tfileposinfo;
          { file location of end of procedure }
          exitpos   : tfileposinfo;
          { local switches at begin of procedure }
          entryswitches : tlocalswitches;
          { local switches at end of procedure }
          exitswitches  : tlocalswitches;

          { Size of the parameters on the stack }
          para_stack_size : pint;

          { Offset of temp after para/local are allocated }
          tempstart : longint;

          { some collected informations about the procedure
            see pi_xxxx constants above
          }
          flags : tprocinfoflags;

          { register used as frame pointer }
          framepointer : tregister;

          { register containing currently the got }
          got : tregister;
          CurrGOTLabel : tasmlabel;

          { Holds the reference used to store all saved registers. }
          save_regs_ref : treference;

          { Last assembler instruction of procedure prologue }
          endprologue_ai : tlinkedlistitem;

          { Amount of stack adjustment after all alignments }
          final_localsize : longint;

          { Labels for TRUE/FALSE condition, BREAK and CONTINUE }
          CurrBreakLabel,
          CurrContinueLabel,
          CurrTrueLabel,
          CurrFalseLabel : tasmlabel;

          { label to leave the sub routine }
          CurrExitLabel : tasmlabel;

          { The code for the routine itself, excluding entry and
            exit code. This is a linked list of tai classes.
          }
          aktproccode : TAsmList;
          { Data (like jump tables) that belongs to this routine }
          aktlocaldata : TAsmList;

          { max. of space need for parameters }
          maxpushedparasize : aint;

          { is this a constructor that calls another constructor on itself
            (either inherited, or another constructor of the same class)?
            Requires different entry code for some targets. }
          ConstructorCallingConstructor: boolean;

          constructor create(aparent:tprocinfo);virtual;
          destructor destroy;override;

          procedure allocate_push_parasize(size:longint);

          function calc_stackframe_size:longint;virtual;

          { Set the address of the first temp, can be used to allocate
            space for pushing parameters }
          procedure set_first_temp_offset;virtual;

          { Generate parameter information }
          procedure generate_parameter_info;virtual;

          { Allocate got register }
          procedure allocate_got_register(list: TAsmList);virtual;

          { get frame pointer }
          procedure init_framepointer; virtual;

          { Destroy the entire procinfo tree, starting from the outermost parent }
          procedure destroy_tree;

          { Store CurrTrueLabel and CurrFalseLabel to saved and generate new ones }
          procedure save_jump_labels(out saved: tsavedlabels);

          { Restore CurrTrueLabel and CurrFalseLabel from saved }
          procedure restore_jump_labels(const saved: tsavedlabels);

          function get_first_nestedproc: tprocinfo;
          function has_nestedprocs: boolean;

          { Add to parent's list of nested procedures even if parent is a 'main' procedure }
          procedure force_nested;
       end;
       tcprocinfo = class of tprocinfo;

    var
       cprocinfo : tcprocinfo;
       { information about the current sub routine being parsed (@var(pprocinfo))}
       current_procinfo : tprocinfo;

implementation

     uses
        cutils,systems,
        tgobj,cgobj,
        paramgr
        ;


{****************************************************************************
                                 TProcInfo
****************************************************************************}

    constructor tprocinfo.create(aparent:tprocinfo);
      begin
        parent:=aparent;
        procdef:=nil;
        para_stack_size:=0;
        flags:=[];
        init_framepointer;
        framepointer:=NR_FRAME_POINTER_REG;
        maxpushedparasize:=0;
        { asmlists }
        aktproccode:=TAsmList.Create;
        aktlocaldata:=TAsmList.Create;
        reference_reset(save_regs_ref,sizeof(aint));
        { labels }
        current_asmdata.getjumplabel(CurrExitLabel);
        current_asmdata.getjumplabel(CurrGOTLabel);
        CurrBreakLabel:=nil;
        CurrContinueLabel:=nil;
        CurrTrueLabel:=nil;
        CurrFalseLabel:=nil;
        if Assigned(parent) and (parent.procdef.parast.symtablelevel>=normal_function_level) then
          parent.addnestedproc(Self);
      end;

    procedure tprocinfo.force_nested;
      begin
        if Assigned(parent) and (parent.procdef.parast.symtablelevel<normal_function_level) then
          parent.addnestedproc(Self);
      end;

    destructor tprocinfo.destroy;
      begin
         nestedprocs.free;
         aktproccode.free;
         aktlocaldata.free;
      end;

    procedure tprocinfo.destroy_tree;
      var
        hp: tprocinfo;
      begin
        hp:=Self;
        while Assigned(hp.parent) do
          hp:=hp.parent;
        hp.Free;
      end;

    procedure tprocinfo.addnestedproc(child: tprocinfo);
      begin
        if nestedprocs=nil then
          nestedprocs:=TLinkedList.Create;
        nestedprocs.insert(child);
      end;

    function tprocinfo.get_first_nestedproc: tprocinfo;
      begin
        if assigned(nestedprocs) then
          result:=tprocinfo(nestedprocs.first)
        else
          result:=nil;
      end;

    function tprocinfo.has_nestedprocs: boolean;
      begin
        result:=assigned(nestedprocs) and (nestedprocs.count>0);
      end;

    procedure tprocinfo.save_jump_labels(out saved: tsavedlabels);
      begin
        saved[false]:=CurrFalseLabel;
        saved[true]:=CurrTrueLabel;
        current_asmdata.getjumplabel(CurrTrueLabel);
        current_asmdata.getjumplabel(CurrFalseLabel);
      end;

    procedure tprocinfo.restore_jump_labels(const saved: tsavedlabels);
      begin
        CurrFalseLabel:=saved[false];
        CurrTrueLabel:=saved[true];
      end;

    procedure tprocinfo.allocate_push_parasize(size:longint);
      begin
        if size>maxpushedparasize then
          maxpushedparasize:=size;
      end;


    function tprocinfo.calc_stackframe_size:longint;
      begin
        result:=Align(tg.direction*tg.lasttemp,current_settings.alignment.localalignmin);
      end;


    procedure tprocinfo.set_first_temp_offset;
      begin
      end;


    procedure tprocinfo.generate_parameter_info;
      begin
        { generate callee paraloc register info, it initialises the size that
          is allocated on the stack }
        procdef.init_paraloc_info(calleeside);
        para_stack_size:=procdef.calleeargareasize;
      end;


    procedure tprocinfo.allocate_got_register(list: TAsmList);
      begin
        { most os/cpu combo's don't use this yet, so not yet abstract }
      end;


    procedure tprocinfo.init_framepointer;
      begin
        { most targets use a constant, but some have a typed constant that must
          be initialized }
      end;


end.
