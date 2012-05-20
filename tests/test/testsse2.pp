{ %OPT=-OaVARMAX=16 -OaVARMIN=16 }
{ %CPU=i386 }
uses
   mmx;

{ only a small test to see if it works in principle }

var
  b : byte;
  q : array[0..15] of byte;

begin
  if is_sse2_cpu then
    asm
{$ifdef FPC_PIC}
       call .LPIC
.LPIC:
       popl %ecx
{$ifdef darwin}
       movdqa    %xmm1,%xmm2
       movdqa    q-.LPIC(%ecx),%xmm4
       psubq     %xmm1,%xmm2
       psubq     q-.LPIC(%ecx),%xmm4
{$else darwin}
       addl      $_GLOBAL_OFFSET_TABLE_,%ecx
       movdqa    %xmm1,%xmm2
       movdqa    q@GOT(%ecx),%xmm4
       psubq     %xmm1,%xmm2
       psubq     q@GOT(%ecx),%xmm4
{$endif darwin}
{$else FPC_PIC}
       movdqa    %xmm1,%xmm2
       movdqa    q,%xmm4
       psubq     %xmm1,%xmm2
       psubq     q,%xmm4
{$endif FPC_PIC}
    end;
end.
