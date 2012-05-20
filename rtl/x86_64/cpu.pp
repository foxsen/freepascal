{
    This file is part of the Free Pascal run time library.
    Copyright (c) 1999-2000 by Florian Klaempfl

    This unit contains some routines to get informations about the
    processor

    See the file COPYING.FPC, included in this distribution,
    for details about the copyright.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

 **********************************************************************}
{$mode objfpc}
unit cpu;

  interface

  {$ifdef freebsd}                 // FreeBSD 7/8 have binutils version that don't support cmpxchg16b
			           // Unless overridebinutils is defined (for ports usage), use db instead of the instruction
     {$ifndef overridebinutils}
       {$define oldbinutils}
     {$endif}
  {$endif}

    uses
      sysutils;

    function InterlockedCompareExchange128Support : boolean;inline;
    function AESSupport : boolean;inline;

    var
      is_sse3_cpu : boolean = false;

    function InterlockedCompareExchange128(var Target: Int128Rec; NewValue: Int128Rec; Comperand: Int128Rec): Int128Rec;

  implementation

    var
      _AESSupport,
      _InterlockedCompareExchange128Support : boolean;

    function InterlockedCompareExchange128Support : boolean;inline;
      begin
        result:=_InterlockedCompareExchange128Support;
      end;

    function AESSupport : boolean;inline;
      begin
        result:=_AESSupport;
      end;


    function InterlockedCompareExchange128(var Target: Int128Rec; NewValue: Int128Rec; Comperand: Int128Rec): Int128Rec; assembler;
     {
        win64:
          rcx ... pointer to result
          rdx ... target
          r8  ... NewValue
          r9  ... Comperand
      }
    {$ifdef win64}
      asm
        pushq %rbx

        { store result pointer for later use }
        pushq %rcx

        { load new value }
        movq (%r8),%rbx
        movq 8(%r8),%rcx

        { save target pointer for later use }
        movq %rdx,%r8

        { load comperand }
        movq (%r9),%rax
        movq 8(%r9),%rdx

        {$ifdef oldbinutils}
           .byte 0xF0,0x49,0x0F,0xC7,0x08
        {$else}
        lock cmpxchg16b (%r8)
        {$endif}
        { restore result pointer }
        popq %rcx

        { store result }
        movq %rax,(%rcx)
        movq %rdx,8(%rcx)

        popq %rbx
      end;
    {$else win64}
    {
      linux:
        rdi       ... target
        [rsi:rdx] ... NewValue
        [rcx:r8]  ... Comperand
        [rdx:rax] ... result
    }
      asm
        pushq %rbx

        movq %rsi,%rbx          // new value low
        movq %rcx,%rax          // comperand low
        movq %rdx,%rcx          // new value high
        movq %r8,%rdx           // comperand high
        {$ifdef oldbinutils}
        .byte 0xF0,0x48,0x0F,0xC7,0x0F
        {$else}
        lock cmpxchg16b (%rdi)
        {$endif}

        popq %rbx
      end;
    {$endif win64}


    procedure SetupSupport;
      var
        _ecx : longint;
      begin
        asm
           pushq %rbx
           movl $0x00000001,%eax
           cpuid
           movl %ecx,_ecx
           popq %rbx
        end;
        _InterlockedCompareExchange128Support:=(_ecx and $2000)<>0;
        _AESSupport:=(_ecx and $2000000)<>0;
        is_sse3_cpu:=(_ecx and $1)<>0;
      end;

begin
  SetupSupport;
end.
