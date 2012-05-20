{
    Copyright (c) 1998-2004 by Florian Klaempfl

    Basic Processor information

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
Unit cpuinfo;

{$i fpcdefs.inc}

Interface

  uses
    globtype;

Type
   bestreal = extended;
   ts32real = single;
   ts64real = double;
   ts80real = extended;
   ts128real = type extended;
   ts64comp = type extended;

   pbestreal=^bestreal;

   { possible supported processors for this target }
   tcputype =
      (cpu_none,
       cpu_386,
       cpu_Pentium,
       cpu_Pentium2,
       cpu_Pentium3,
       cpu_Pentium4,
       cpu_PentiumM
      );

   tfputype =
     (fpu_none,
//      fpu_soft,
      fpu_x87,
      fpu_sse,
      fpu_sse2,
      fpu_sse3
     );


Const
   { calling conventions supported by the code generator }
   supported_calling_conventions : tproccalloptions = [
     pocall_internproc,
     pocall_register,
     pocall_safecall,
     pocall_stdcall,
     pocall_cdecl,
     pocall_cppdecl,
     pocall_far16,
     pocall_pascal,
     pocall_oldfpccall,
     pocall_mwpascal
   ];

   cputypestr : array[tcputype] of string[10] = ('',
     '80386',
     'PENTIUM',
     'PENTIUM2',
     'PENTIUM3',
     'PENTIUM4',
     'PENTIUMM'
   );

   fputypestr : array[tfputype] of string[6] = ('',
//     'SOFT',
     'X87',
     'SSE',
     'SSE2',
     'SSE3'
   );

   sse_singlescalar : set of tfputype = [fpu_sse,fpu_sse2,fpu_sse3];
   sse_doublescalar : set of tfputype = [fpu_sse2,fpu_sse3];

   { Supported optimizations, only used for information }
   supported_optimizerswitches = genericlevel1optimizerswitches+
                                 genericlevel2optimizerswitches+
                                 genericlevel3optimizerswitches-
                                 { no need to write info about those }
                                 [cs_opt_level1,cs_opt_level2,cs_opt_level3]+
                                 [cs_opt_peephole,cs_opt_regvar,cs_opt_stackframe,
                                  cs_opt_asmcse,cs_opt_loopunroll,cs_opt_uncertain,
								  cs_opt_tailrecursion,cs_opt_nodecse];

   level1optimizerswitches = genericlevel1optimizerswitches + [cs_opt_peephole];
   level2optimizerswitches = genericlevel2optimizerswitches + level1optimizerswitches +
     [cs_opt_regvar,cs_opt_stackframe,cs_opt_tailrecursion,cs_opt_nodecse];
   level3optimizerswitches = genericlevel3optimizerswitches + level2optimizerswitches + [{,cs_opt_loopunroll}];

Implementation

end.
