{
    Copyright (c) 1998-2008 by Peter Vreman

    This unit implements support information structures for solaris

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
{ This unit implements support information structures for solaris. }
unit i_sunos;

{$i fpcdefs.inc}

  interface

    uses
       systems;

    const
       system_i386_solaris_info : tsysteminfo =
          (
            system       : system_i386_solaris;
            name         : 'Solaris for i386';
            shortname    : 'solaris';
            flags        : [tf_under_development,tf_needs_symbol_size,
                            tf_files_case_sensitive,tf_requires_proper_alignment,
                            tf_smartlink_library,tf_has_winlike_resources];
            cpu          : cpu_i386;
            unit_env     : 'SOLARISUNITS';
            extradefines : 'UNIX;LIBC;SUNOS;HASUNIX';
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
            assemextern  : as_ggas;
            link         : nil;
            linkextern   : nil;
            ar           : ar_gnu_gar;
            res          : res_elf;
            dbg          : dbg_stabs;
            script       : script_unix;
            endian       : endian_little;
            alignment    :
              (
                procalign       : 16;
                loopalign       : 4;
                jumpalign       : 0;
                constalignmin   : 0;
                constalignmax   : 8;
                varalignmin     : 0;
                varalignmax     : 16;
                localalignmin   : 4;
                localalignmax   : 8;
                recordalignmin  : 0;
                recordalignmax  : 16;
                maxCrecordalign : 4
              );
            first_parm_offset : 8;
            stacksize    : 262144;
            abi          : abi_default;
          );


       system_x86_64_solaris_info : tsysteminfo =
          (
            system       : system_x86_64_solaris;
            name         : 'Solaris for x86-64';
            shortname    : 'solaris';
            flags        : [tf_needs_symbol_size,tf_needs_symbol_type,
			    tf_under_development,
                            tf_files_case_sensitive,
                            tf_requires_proper_alignment,tf_smartlink_library,tf_library_needs_pic,
                            tf_has_winlike_resources];
            cpu          : cpu_x86_64;
            unit_env     : 'SOLARISUNITS';
            extradefines : 'UNIX;LIBC;SUNOS;HASUNIX';
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
            assem        : as_ggas{as_x86_64_elf64};
            assemextern  : as_ggas;
            link         : nil;
            linkextern   : nil;
            ar           : ar_gnu_ar;
            res          : res_elf;
            dbg          : dbg_dwarf2;
            script       : script_unix;
            endian       : endian_little;
            alignment    :
              (
                procalign       : 8;
                loopalign       : 4;
                jumpalign       : 0;
                constalignmin   : 0;
                constalignmax   : 8;
                varalignmin     : 0;
                varalignmax     : 16;
                localalignmin   : 4;
                localalignmax   : 16;
                recordalignmin  : 0;
                recordalignmax  : 16;
                maxCrecordalign : 16
              );
            first_parm_offset : 16;
            stacksize    : 8*1024*1024;
            abi : abi_default
          );


       system_sparc_solaris_info : tsysteminfo =
          (
            system       : system_sparc_solaris;
            name         : 'Solaris for SPARC';
            shortname    : 'solaris';
            flags        : [tf_needs_symbol_size,tf_under_development,
                            tf_files_case_sensitive,
                            tf_requires_proper_alignment,tf_smartlink_library,
                            tf_has_winlike_resources];
            cpu          : cpu_SPARC;
            unit_env     : 'SOLARISUNITS';
            extradefines : 'UNIX;LIBC;SUNOS;HASUNIX';
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
            assem        : as_ggas;
            assemextern  : as_ggas;
            link         : nil;
            linkextern   : nil;
            ar           : ar_gnu_gar;
            res          : res_elf;
            dbg          : dbg_stabs;
            script       : script_unix;
            endian       : endian_big;
            alignment    :
              (
                procalign       : 4;
                loopalign       : 4;
                jumpalign       : 0;
                constalignmin   : 4;
                constalignmax   : 8;
                varalignmin     : 4;
                varalignmax     : 8;
                localalignmin   : 4;
                localalignmax   : 8;
                recordalignmin  : 0;
                recordalignmax  : 8;
                maxCrecordalign : 8
              );
            first_parm_offset : 92;
            stacksize    : 262144;
            abi          : abi_default;
          );

  implementation

initialization
{$ifdef CPU86}
  {$ifdef solaris}
    set_source_info(system_i386_solaris_info);
  {$endif solaris}
{$endif CPU86}
{$ifdef CPUX86_64}
  {$ifdef solaris}
    set_source_info(system_x86_64_solaris_info);
  {$endif solaris}
{$endif CPUX86_64}
{$ifdef CPUSparc}
  {$ifdef solaris}
    set_source_info(system_sparc_solaris_info);
  {$endif solaris}
{$endif CPUSparc}

end.
