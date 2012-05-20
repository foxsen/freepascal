{
    Copyright (c) 1998-2002 by Peter Vreman

    This unit implements support information structures for BeOS

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
{ This unit implements support information structures for BeOS. }
unit i_beos;

{$i fpcdefs.inc}

  interface

    uses
       systems;

    const
       system_i386_beos_info : tsysteminfo =
          (
            system       : system_i386_BeOS;
            name         : 'Beos for i386';
            shortname    : 'Beos';
            flags        : [tf_under_development,tf_needs_symbol_size,tf_files_case_sensitive,
                            tf_smartlink_sections, tf_smartlink_library];
            cpu          : cpu_i386;
            unit_env     : 'BEOSUNITS';
            extradefines : 'UNIX;HASUNIX';
            exeext       : '';
            defext       : '.def';
            scriptext    : '.sh';
            smartext     : '.sl';
            unitext      : '.ppu';
            unitlibext   : '.ppl';
            asmext       : '.s';
            objext       : '.o';
            resext       : '.res';
            resobjext    : '.or';
            sharedlibext : '.so';
            staticlibext : '.a';
            staticlibprefix : 'libp';
            sharedlibprefix : 'lib';
            sharedClibext : '.so';
            staticClibext : '.a';
            staticClibprefix : 'lib';
            sharedClibprefix : 'lib';
            importlibprefix : 'libimp';
            importlibext : '.a';
            Cprefix      : '';
            newline      : #10;
            dirsep       : '/';
            assem        : as_i386_elf32;
            assemextern  : as_gas;
            link         : nil;
            linkextern   : nil;
            ar           : ar_gnu_ar;
            res          : res_none;
            dbg          : dbg_stabs;
            script       : script_unix;
            endian       : endian_little;
            alignment    :
              (
                procalign       : 4;
                loopalign       : 4;
                jumpalign       : 0;
                constalignmin   : 0;
                constalignmax   : 4;
                varalignmin     : 0;
                varalignmax     : 4;
                localalignmin   : 0;
                localalignmax   : 4;
                recordalignmin  : 0;
                recordalignmax  : 2;
                maxCrecordalign : 4
              );
            first_parm_offset : 8;
            { Stack size used to be 256 K under BeOS. So, it was the value 
              used in previous version of FPC for BeOS (but lost in the road 
              to 2.* ;-).
              According to buildtools/gcc/gcc/config/i386/beos-elf.h in the 
              Haiku's repository, this value was increased to 1Mb since r4.1b3.
              Under R5, this value is even greater. listarea report a default 
              size of 16 Mb for the user stack of the main thread.
              People who still use BeOS nowadays should use R5 (or Haiku), 
              so i use this new value.  
            }
            stacksize    : 16 * 1024 * 1024;
            abi : abi_default
          );

  implementation

initialization
{$ifdef cpu86}
  {$ifdef beos}
    {$ifndef haiku}
      set_source_info(system_i386_beos_info);
    {$endif haiku}
  {$endif beos}
{$endif cpu86}
end.
