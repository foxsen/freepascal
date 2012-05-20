{
    This file is part of the Free Pascal run time library.
    Copyright (c) 2000 by Florian Klaempfl

    It creates pascal units from unicode mapping files

    See the file COPYING.FPC, included in this distribution,
    for details about the copyright.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

 **********************************************************************}
program creumap;

  uses
     charset;

  procedure doerror;

    begin
       writeln('Usage: creumap <cpname> <cpnumber>');
       writeln('cpname : A mapping file called <cpname>.txt must be present');
       writeln('cpnumber : the code page number');
       halt(1);
    end;

  var
     p : punicodemap;
     i : longint;
     t : text;
     e : word;

begin
   if paramcount<>2 then
     doerror;
   Val(paramstr(2),i,e);
   if e<>0 then
     doerror;
     
   p:=loadunicodemapping(paramstr(1),paramstr(1)+'.txt',i);
   if p=nil then
     doerror;
   assign(t,paramstr(1)+'.pp');
   rewrite(t);
   writeln(t,'{ This is an automatically created file, so don''t edit it }');
   writeln(t,'unit ',p^.cpname,';');
   writeln(t);
   writeln(t,'  interface');
   writeln(t);
   writeln(t,'  implementation');
   writeln(t);
   writeln(t,'  uses');
   writeln(t,'     charset;');
   writeln(t);
   writeln(t,'  const');
   writeln(t,'     map : array[0..',p^.lastchar,'] of tunicodecharmapping = (');
   for i:=0 to p^.lastchar do
     begin
        write(t,'       (unicode : ',p^.map[i].unicode,'; flag : ');
        case p^.map[i].flag of
           umf_noinfo : write(t,'umf_noinfo');
           umf_leadbyte : write(t,'umf_leadbyte');
           umf_undefined : write(t,'umf_undefined');
           umf_unused : write(t,'umf_unused');
        end;
        write(t,'; reserved: 0)');
        if i<>p^.lastchar then
          writeln(t,',')
        else
          writeln(t);
     end;
   writeln(t,'     );');
   writeln(t);
   writeln(t,'     unicodemap : tunicodemap = (');
   writeln(t,'       cpname : ''',p^.cpname,''';');
   writeln(t,'       cp : ',p^.cp,';');
   writeln(t,'       map : @map;');
   writeln(t,'       lastchar : ',p^.lastchar,';');
   writeln(t,'       next : nil;');
   writeln(t,'       internalmap : true');
   writeln(t,'     );');
   writeln(t);
   writeln(t,'  begin');
   writeln(t,'     registermapping(@unicodemap)');
   writeln(t,'  end.');
   close(t);
end.
