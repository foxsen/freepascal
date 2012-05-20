{
    This unit implements support information structures for Nintendo DS

    Copyright (c) 1998-2002 by Peter Vreman

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
{ This unit implements support information structures for nds. }
unit i_nds;

{$i fpcdefs.inc}

  interface

    uses
       systems;

    const
       system_arm_nds_info : tsysteminfo =
          (
            system       : system_arm_nds;
            name         : 'Nintendo DS';
            shortname    : 'nds';
            flags        : [tf_needs_symbol_size,tf_files_case_sensitive,
                            tf_requires_proper_alignment,tf_smartlink_sections];
            cpu          : cpu_arm;
            unit_env     : '';
            extradefines : '';
            exeext       : '.bin';
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
            assem        : as_gas;
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
                constalignmax   : 8;//4;
                varalignmin     : 0;
                varalignmax     : 8;//4;
                localalignmin   : 4;
                localalignmax   : 8;
                recordalignmin  : 0;
                recordalignmax  : 8;//4;
                maxCrecordalign : 8//4
              );
            first_parm_offset : 8;
            stacksize    : $3CFF; //15615? or 16384?;
            abi : abi_eabi
          );

  implementation

initialization
{$ifdef arm}
  {$ifdef nds}
    set_source_info(system_arm_nds_info);
  {$endif nds}
{$endif arm}
end.
