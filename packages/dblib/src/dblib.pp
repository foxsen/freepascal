{
    This file is part of the Free Component Library (FCL)

    Copyright (c) 2010 by the Free Pascal development team

    Header files Microsoft DB-Library for C: sqlfront.h, sqldb.h
      and FreeTDS: sybdb.h

    See the file COPYING.FPC, included in this distribution,
    for details about the copyright.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

    The Original Code was created by (c) 2010 Ladislav Karrach (Windows)
    for the Free Pascal project.
 **********************************************************************
    FreeTDS (http://www.freetds.org/userguide/choosingtdsprotocol.htm):
      tds version = 5.0 - Sybase System 10 and above
                    7.0 - MS SQL Server 7
                    7.1 - MS SQL Server 2000 (*default*)
                    7.2 - MS SQL Server 2005
                    7.3 - MS SQL Server 2008
      tds version can be set using env.var. TDSVER or in freetds.conf or .freetds.conf
}
unit dblib;

{$IFDEF FPC}{$mode objfpc}{$ENDIF}{$H+}

{ $DEFINE ntwdblib}  //if you are using MS SQL Server Client Library (ntwdblib.dll)
{$IFNDEF ntwdblib}
 {$DEFINE freetds}  //if you are using db-lib from FreeTDS project (MS SQL Server + Sybase support)
{$ENDIF}

{$DEFINE LOAD_DYNAMICALLY}

interface

const
  DBLIBDLL=
{$IFDEF WINDOWS}
  {$IFDEF ntwdblib}'ntwdblib.dll'{$ENDIF}
  {$IFDEF freetds} 'dblib.dll'   {$ENDIF}
{$ELSE}
  {$IFDEF DARWIN}
    'libsybdb.dylib'
  {$ELSE}
    'libsybdb.so'
  {$ENDIF}
{$ENDIF}
  ;

  //from sybdb.h:
  //DBVERSION_xxx are used with dbsetlversion()
  DBVERSION_100= 2; // Sybase TDS 5.0
  DBVERSION_42 = 3; // This can be used for old Microsoft and Sybase servers
  DBVERSION_70 = 4;
  DBVERSION_71 = 5;
  DBVERSION_72 = 6;
  DBVERSION_73 = 7;

  //DBTDS_xxx are returned by DBTDS()
  DBTDS_UNKNOWN= 0;
  DBTDS_42     = 4;  // SQL Server 4.2
  DBTDS_50     = 7;	 // Sybase SQL Server 5.0; use this for connecting to Sybase (ASA or ASE)
  DBTDS_70     = 8;	 // Microsoft SQL Server 7.0
  DBTDS_71     = 9;  // Microsoft SQL Server 2000
  DBTDS_72     = 10; // Microsoft SQL Server 2005
  DBTDS_73     = 11; // Microsoft SQL Server 2008

  //from sqlfront.h:
  DBSETHOST=1;
  DBSETUSER=2;
  DBSETPWD=3;
  DBSETAPP=4;
  DBSETID=5;
  DBSETLANG=6;
  DBSETSECURE=7;
  //These two are defined by Microsoft for dbsetlversion():
  DBVER42={$IFDEF freetds}DBVERSION_42{$ELSE}8{$ENDIF};
  DBVER60={$IFDEF freetds}DBVERSION_71{$ELSE}9{$ENDIF};
  DBSET_LOGINTIME=10;
  DBSETFALLBACK=12;
  //dboptions:
  DBNOAUTOFREE = {$IFDEF freetds}15{$ELSE}8{$ENDIF};
  DBTEXTLIMIT  = {$IFDEF freetds}7{$ELSE}4{$ENDIF};
  DBTEXTSIZE   = {$IFDEF freetds}17{$ELSE}5{$ENDIF};
  DBANSItoOEM  = 14;
  DBOEMtoANSI  = 15;
  DBQUOTEDIDENT= {$IFDEF freetds}35{$ELSE}18{$ENDIF};

  TIMEOUT_IGNORE=-1;
  TIMEOUT_INFINITE=0;

  SUCCEED=1;
  FAIL=0;
  NO_MORE_RESULTS=2;
  NO_MORE_RPC_RESULTS=3;

  MORE_ROWS=-1;
  REG_ROW=MORE_ROWS;
  NO_MORE_ROWS=-2;
  BUF_FULL=-3;     //only if buffering is turned on

  INT_EXIT=0;
  INT_CONTINUE=1;
  INT_CANCEL=2;

  SQLVOID=$1f;
  SQLTEXT=$23;
  SQLVARBINARY=$25;
  SQLINTN=$26;     //all nullable integers
  SQLVARCHAR=$27;
  SQLBINARY=$2d;
  SQLIMAGE=$22;
  SQLCHAR=$2f;
  SQLINT1=$30;
  SQLBIT=$32;
  SQLINT2=$34;
  SQLINT4=$38;
  SQLMONEY=$3c;
  SQLDATETIME=$3d;
  SQLFLT8=$3e;
  SQLFLTN=$6d;
  SQLMONEYN=$6e;
  SQLDATETIMN=$6f;
  SQLFLT4=$3b;
  SQLMONEY4=$7a;
  SQLDATETIM4=$3a;
  SQLDECIMAL=$6a;
  SQLNUMERIC=$6c;
  //from tds.h:
  SYBNTEXT=$63;
  SYBINT8=$7F;
  SYBUNIQUE=$24;
  //XSYBVARCHAR=$A7;
  //XSYBNVARCHAR=$E7;
  //XSYBNCHAR = $EF;
  //XSYBBINARY= $AD;

  MAXTABLENAME ={$IFDEF freetds}512+1{$ELSE}30{$ENDIF};
  MAXCOLNAMELEN={$IFDEF freetds}512+1{$ELSE}30{$ENDIF};
  MAXNUMERICLEN={$IFDEF freetds}32   {$ELSE}16{$ENDIF};
  DBMAXCHAR=256; // Max length of DBVARBINARY and DBVARCHAR, etc.

  DEFAULTPRECISION = 18;
  DEFAULTSCALE     = 0;

  // Used by dbcolinfo:
  CI_REGULAR=1;
  CI_ALTERNATE=2;
  CI_CURSOR=3;

  DBUNKNOWN = 2; //FALSE = 0, TRUE = 1

  // Error codes:
  SYBEFCON = 20002;      // SQL Server connection failed

type
  PLOGINREC=Pointer;
  PDBPROCESS=Pointer;

  RETCODE=integer;
  STATUS=integer;

  INT=longint;
  SHORT=smallint;
  BOOL=longbool;
  ULONG=longword;

  // DB-Library datatypes
  DBCHAR=shortint;
  DBBIT=byte;
  DBTINYINT=byte;
  DBSMALLINT=smallint;   // 16-bit int (short)
  DBUSMALLINT=word;      // 16-bit unsigned int (unsigned short)
  DBINT=longint;         // 32-bit int (int)
  DBFLT8=double;         // 64-bit real (double)
  DBBINARY=byte;

  {$PACKRECORDS C}
  DBDATETIME=packed record
    dtdays: DBINT;
    dttime: ULONG;
  end;
  PDBDATETIME=^DBDATETIME;

  // DBDATEREC structure used by dbdatecrack
  DBDATEREC=packed record
    case boolean of
    false:(
      oldyear:INT;         // 1753 - 9999
      oldmonth: INT;       // 1 - 12
      oldday: INT;         // 1 - 31
      olddayofyear: INT;   // 1 - 366 (in sybdb.h dayofyear and day are changed around!)
      oldweekday: INT;     // 1 - 7  (Mon - Sun)
      oldhour: INT;        // 0 - 23
      oldminute: INT;      // 0 - 59
      oldsecond: INT;      // 0 - 59
      oldmillisecond: INT; // 0 - 999
      oldtzone: INT;       // 0 - 127 (Sybase only!)
    );
    true:(
      year:INT;         // 1753 - 9999
      quarter:INT;      // 1 - 4
      month: INT;       // 1 - 12
      {$IFDEF freetds}
      day: INT;         // 1 - 31
      dayofyear: INT;   // 1 - 366 (in sybdb.h dayofyear and day are changed around!)
      {$ELSE}
      dayofyear: INT;   // 1 - 366 (in sybdb.h dayofyear and day are changed around!)
      day: INT;         // 1 - 31
      {$ENDIF}
      week: INT;        // 1 - 54 (for leap years)
      weekday: INT;     // 1 - 7  (Mon - Sun)
      hour: INT;        // 0 - 23
      minute: INT;      // 0 - 59
      second: INT;      // 0 - 59
      millisecond: INT; // 0 - 999
      tzone: INT;       // 0 - 127 (Sybase only!)
    );
  end;
  PDBDATEREC=^DBDATEREC;

  DBNUMERIC=packed record
   	precision: BYTE;
   	scale: BYTE;
   	sign: BYTE; // 1 = Positive, 0 = Negative
   	val: array[0..MAXNUMERICLEN-1] of BYTE;
  end;

  DBVARYBIN=packed record
    len: {$IFDEF freetds}DBINT{$ELSE}DBSMALLINT{$ENDIF};
    bytes: array[0..DBMAXCHAR-1] of BYTE;
  end;

  DBVARYCHAR=packed record
    len: {$IFDEF freetds}DBINT{$ELSE}DBSMALLINT{$ENDIF};
    str: array[0..DBMAXCHAR-1] of AnsiChar;
  end;

  DBERRHANDLE_PROC=function(dbproc: PDBPROCESS; severity, dberr, oserr:INT; dberrstr, oserrstr:PChar):INT; cdecl;
  DBMSGHANDLE_PROC=function(dbproc: PDBPROCESS; msgno: DBINT; msgstate, severity:INT; msgtext, srvname, procname:PChar; line:DBUSMALLINT):INT; cdecl;

  {$IFDEF ntwdblib}
    {$PACKRECORDS 2}
  {$ENDIF}
  DBCOL=record
   	SizeOfStruct: DBINT;
   	Name: array[0..MAXCOLNAMELEN] of AnsiChar;
   	ActualName: array[0..MAXCOLNAMELEN] of AnsiChar;
   	TableName: array[0..MAXTABLENAME] of AnsiChar;
   	Typ: SHORT;
   	UserType: DBINT;
   	MaxLength: DBINT;
   	Precision: BYTE;
   	Scale: BYTE;
   	VarLength: BOOL;     // TRUE, FALSE
   	Null: BYTE;          // TRUE, FALSE or DBUNKNOWN
   	CaseSensitive: BYTE; // TRUE, FALSE or DBUNKNOWN
   	Updatable: BYTE;     // TRUE, FALSE or DBUNKNOWN
   	Identity: BOOL;      // TRUE, FALSE
  end;
  PDBCOL=^DBCOL;
  {$PACKRECORDS DEFAULT}


var
  DBLibInit: boolean=false; //was dbinit() already called ?

{$IFNDEF LOAD_DYNAMICALLY}
  function dbinit():{$IFDEF freetds}RETCODE{$ELSE}PChar{$ENDIF}; cdecl; external DBLIBDLL;
  function dblogin():PLOGINREC; cdecl; external DBLIBDLL;
  function dbsetlname(login:PLOGINREC; value:PChar; which:INT):RETCODE; cdecl; external DBLIBDLL;
  function dbsetlogintime(seconds:INT):RETCODE; cdecl; external DBLIBDLL;
  function dbsettime(seconds:INT):RETCODE; cdecl; external DBLIBDLL;
  function dberrhandle(handler:DBERRHANDLE_PROC):DBERRHANDLE_PROC; cdecl; external DBLIBDLL;
  function dbmsghandle(handler:DBMSGHANDLE_PROC):DBMSGHANDLE_PROC; cdecl; external DBLIBDLL;
  function dbsetopt(dbproc:PDBPROCESS; option: INT; param:PChar {$IFDEF freetds};int_param:INT{$ENDIF}):RETCODE; cdecl; external DBLIBDLL;
  function dbuse(dbproc:PDBPROCESS; dbname:PChar):RETCODE; cdecl; external DBLIBDLL;
  function dbcmd(dbproc:PDBPROCESS; cmdstring:PChar):RETCODE; cdecl; external DBLIBDLL;
  function dbcmdrow(dbproc:PDBPROCESS):RETCODE; cdecl; external DBLIBDLL;
  function dbsqlexec(dbproc:PDBPROCESS):RETCODE; cdecl; external DBLIBDLL;
  function dbresults(dbproc:PDBPROCESS):RETCODE; cdecl; external DBLIBDLL;
  function dbmorecmds(dbproc:PDBPROCESS):RETCODE; cdecl; external DBLIBDLL;
  function dbnextrow(dbproc:PDBPROCESS):STATUS; cdecl; external DBLIBDLL;
  function dbnumcols(dbproc:PDBPROCESS):INT; cdecl; external DBLIBDLL;
  function dbcolname(dbproc:PDBPROCESS; column:INT):PChar; cdecl; external DBLIBDLL;
  function dbcoltype(dbproc:PDBPROCESS; column:INT):INT; cdecl; external DBLIBDLL;
  function dbcollen(dbproc:PDBPROCESS; column:INT):DBINT; cdecl; external DBLIBDLL;
  function dbcolinfo(dbproc:PDBPROCESS; typ:INT; column:DBINT; computeid:DBINT; dbcol:PDBCOL):RETCODE; cdecl; external DBLIBDLL;
  function dbprtype(token:INT):PChar; cdecl; external DBLIBDLL;
  function dbdatlen(dbproc:PDBPROCESS; column:INT):DBINT; cdecl; external DBLIBDLL;
  function dbdata(dbproc:PDBPROCESS; column:INT):PByte; cdecl; external DBLIBDLL;
  function dbconvert(dbproc:PDBPROCESS; srctype:INT; src:PByte; srclen:DBINT; desttype:INT; dest:PByte; destlen:DBINT):INT; cdecl; external DBLIBDLL;
  function dbdatecrack(dbproc:PDBPROCESS; dateinfo:PDBDATEREC; datetime: PDBDATETIME):RETCODE; cdecl; external DBLIBDLL;
  function dbcount(dbproc:PDBPROCESS):DBINT; cdecl; external DBLIBDLL;
  function dbiscount(dbproc:PDBPROCESS):BOOL; cdecl; external DBLIBDLL;
  function dbcancel(dbproc:PDBPROCESS):RETCODE; cdecl; external DBLIBDLL;
  function dbcanquery(dbproc:PDBPROCESS):RETCODE; cdecl; external DBLIBDLL;
  procedure dbfreelogin(login:PLOGINREC); cdecl; external DBLIBDLL {$IFDEF freetds}name 'dbloginfree'{$ENDIF};
  procedure dbexit(); cdecl; external DBLIBDLL;
  {$IFDEF ntwdblib}
  function dbopen(login:PLOGINREC; servername:PChar):PDBPROCESS; cdecl; external DBLIBDLL;
  function dbclose(dbproc:PDBPROCESS):RETCODE; cdecl; external DBLIBDLL;
  procedure dbwinexit; cdecl; external DBLIBDLL;
  {$ENDIF}
  {$IFDEF freetds}
  function tdsdbopen(login:PLOGINREC; servername:PChar; msdblib:INT):PDBPROCESS; cdecl; external DBLIBDLL;
  function dbtablecolinfo(dbproc:PDBPROCESS; column:DBINT; dbcol:PDBCOL):RETCODE; cdecl; external DBLIBDLL;
  function dbtds(dbproc:PDBPROCESS):INT; cdecl; external DBLIBDLL;
  function dbsetlversion(login:PLOGINREC; version:BYTE):RETCODE; cdecl; external DBLIBDLL;
  function dbservcharset(dbproc:PDBPROCESS):PChar; cdecl; external DBLIBDLL;
  procedure dbclose(dbproc:PDBPROCESS); cdecl; external DBLIBDLL;
  {$ENDIF}
{$ELSE}
  var
  dbinit: function():{$IFDEF freetds}RETCODE{$ELSE}PChar{$ENDIF}; cdecl;
  dblogin: function():PLOGINREC; cdecl;
  dbsetlname: function(login:PLOGINREC; value:PChar; which:INT):RETCODE; cdecl;
  dbsetlogintime: function(seconds:INT):RETCODE; cdecl;
  dbsettime: function(seconds:INT):RETCODE; cdecl;
  dberrhandle: function(handler:DBERRHANDLE_PROC):DBERRHANDLE_PROC; cdecl;
  dbmsghandle: function(handler:DBMSGHANDLE_PROC):DBMSGHANDLE_PROC; cdecl;
  dbsetopt: function(dbproc:PDBPROCESS; option: INT; param:PChar {$IFDEF freetds};int_param:INT{$ENDIF}):RETCODE; cdecl;
  dbuse: function(dbproc:PDBPROCESS; dbname:PChar):RETCODE; cdecl;
  dbcmd: function(dbproc:PDBPROCESS; cmdstring:PChar):RETCODE; cdecl;
  dbcmdrow: function(dbproc:PDBPROCESS):RETCODE; cdecl;
  dbsqlexec: function(dbproc:PDBPROCESS):RETCODE; cdecl;
  dbresults: function(dbproc:PDBPROCESS):RETCODE; cdecl;
  dbmorecmds: function(dbproc:PDBPROCESS):RETCODE; cdecl;
  dbnextrow: function(dbproc:PDBPROCESS):STATUS; cdecl;
  dbnumcols: function(dbproc:PDBPROCESS):INT; cdecl;
  dbcolname: function(dbproc:PDBPROCESS; column:INT):PChar; cdecl;
  dbcoltype: function(dbproc:PDBPROCESS; column:INT):INT; cdecl;
  dbcollen: function(dbproc:PDBPROCESS; column:INT):DBINT; cdecl;
  dbcolinfo: function(dbproc:PDBPROCESS; typ:INT; column:DBINT; computeid:DBINT; dbcol:PDBCOL):RETCODE; cdecl;
  dbprtype: function(token:INT):PChar; cdecl;
  dbdatlen: function(dbproc:PDBPROCESS; column:INT):DBINT; cdecl;
  dbdata: function(dbproc:PDBPROCESS; column:INT):PByte; cdecl;
  dbconvert: function(dbproc:PDBPROCESS; srctype:INT; src:PByte; srclen:DBINT; desttype:INT; dest:PByte; destlen:DBINT):INT; cdecl;
  dbdatecrack: function(dbproc:PDBPROCESS; dateinfo:PDBDATEREC; datetime: PDBDATETIME):RETCODE; cdecl;
  dbcount: function(dbproc:PDBPROCESS):DBINT; cdecl;
  dbiscount: function(dbproc:PDBPROCESS):BOOL; cdecl;
  dbcancel: function(dbproc:PDBPROCESS):RETCODE; cdecl;
  dbcanquery: function(dbproc:PDBPROCESS):RETCODE; cdecl;
  dbexit: procedure(); cdecl;
  dbfreelogin: procedure(login:PLOGINREC); cdecl;
  {$IFDEF ntwdblib}
  dbopen: function(login:PLOGINREC; servername:PChar):PDBPROCESS; cdecl;
  dbclose: function(dbproc:PDBPROCESS):RETCODE; cdecl;
  dbwinexit: procedure; cdecl;
  {$ENDIF}
  {$IFDEF freetds}
  tdsdbopen: function(login:PLOGINREC; servername:PChar; msdblib:INT):PDBPROCESS; cdecl;
  dbtablecolinfo: function(dbproc:PDBPROCESS; column:DBINT; dbcol:PDBCOL):RETCODE; cdecl;
  dbtds: function(dbproc:PDBPROCESS):INT; cdecl;
  dbsetlversion: function(login:PLOGINREC; version:BYTE):RETCODE; cdecl;
  dbservcharset: function(dbproc:PDBPROCESS):PChar; cdecl;
  dbclose: procedure(dbproc:PDBPROCESS); cdecl;
  {$ENDIF}

  DefaultDBLibLibraryName: String = DBLIBDLL;
{$ENDIF}

{$IFDEF ntwdblib}
function tdsdbopen(login:PLOGINREC; servername:PChar; msdblib:INT):PDBPROCESS;
function dbtablecolinfo(dbproc:PDBPROCESS; column:DBINT; dbcol:PDBCOL):RETCODE;
function dbsetlversion(login:PLOGINREC; version:BYTE):RETCODE;
function dbtds(dbproc:PDBPROCESS):INT;
function dbversion():PChar;
{$ENDIF}
{$IFDEF freetds}
function dbopen(login:PLOGINREC; servername:PChar):PDBPROCESS;
procedure dbwinexit;
{$ENDIF}
function dbsetlcharset(login:PLOGINREC; charset:PChar):RETCODE;
function dbsetlsecure(login:PLOGINREC):RETCODE;

procedure InitialiseDBLib(LibraryName : string = '');
procedure ReleaseDBLib;

implementation

{$IFDEF LOAD_DYNAMICALLY}
uses SysUtils, Dynlibs;

var DBLibLibraryHandle: TLibHandle;
    RefCount: integer;

procedure InitialiseDBLib(LibraryName : string);
var libname : string;
begin
  inc(RefCount);
  if RefCount = 1 then
  begin
    if LibraryName='' then
      libname:=DefaultDBLibLibraryName
    else
      libname:=LibraryName;
    DBLibLibraryHandle := LoadLibrary(libname);
    if DBLibLibraryHandle = nilhandle then
    begin
      RefCount := 0;
      raise EInOutError.CreateFmt('Can not load DB-Lib client library "%s". Check your installation.'+LineEnding+'%s',
                                  [libname, SysErrorMessage(GetLastOSError)]);
    end;

   pointer(dbinit) := GetProcedureAddress(DBLibLibraryHandle,'dbinit');
   pointer(dblogin) := GetProcedureAddress(DBLibLibraryHandle,'dblogin');
   pointer(dbsetlname) := GetProcedureAddress(DBLibLibraryHandle,'dbsetlname');
   pointer(dbsetlogintime) := GetProcedureAddress(DBLibLibraryHandle,'dbsetlogintime');
   pointer(dbsettime) := GetProcedureAddress(DBLibLibraryHandle,'dbsettime');
   pointer(dberrhandle) := GetProcedureAddress(DBLibLibraryHandle,'dberrhandle');
   pointer(dbmsghandle) := GetProcedureAddress(DBLibLibraryHandle,'dbmsghandle');
   pointer(dbsetopt) := GetProcedureAddress(DBLibLibraryHandle,'dbsetopt');
   pointer(dbuse) := GetProcedureAddress(DBLibLibraryHandle,'dbuse');
   pointer(dbcmd) := GetProcedureAddress(DBLibLibraryHandle,'dbcmd');
   pointer(dbcmdrow) := GetProcedureAddress(DBLibLibraryHandle,'dbcmdrow');
   pointer(dbsqlexec) := GetProcedureAddress(DBLibLibraryHandle,'dbsqlexec');
   pointer(dbresults) := GetProcedureAddress(DBLibLibraryHandle,'dbresults');
   pointer(dbmorecmds) := GetProcedureAddress(DBLibLibraryHandle,'dbmorecmds');
   pointer(dbnextrow) := GetProcedureAddress(DBLibLibraryHandle,'dbnextrow');
   pointer(dbnumcols) := GetProcedureAddress(DBLibLibraryHandle,'dbnumcols');
   pointer(dbcolname) := GetProcedureAddress(DBLibLibraryHandle,'dbcolname');
   pointer(dbcoltype) := GetProcedureAddress(DBLibLibraryHandle,'dbcoltype');
   pointer(dbcollen) := GetProcedureAddress(DBLibLibraryHandle,'dbcollen');
   pointer(dbcolinfo) := GetProcedureAddress(DBLibLibraryHandle,'dbcolinfo');
   pointer(dbprtype) := GetProcedureAddress(DBLibLibraryHandle,'dbprtype');
   pointer(dbdatlen) := GetProcedureAddress(DBLibLibraryHandle,'dbdatlen');
   pointer(dbdata) := GetProcedureAddress(DBLibLibraryHandle,'dbdata');
   pointer(dbconvert) := GetProcedureAddress(DBLibLibraryHandle,'dbconvert');
   pointer(dbdatecrack) := GetProcedureAddress(DBLibLibraryHandle,'dbdatecrack');
   pointer(dbcount) := GetProcedureAddress(DBLibLibraryHandle,'dbcount');
   pointer(dbiscount) := GetProcedureAddress(DBLibLibraryHandle,'dbiscount');
   pointer(dbcancel) := GetProcedureAddress(DBLibLibraryHandle,'dbcancel');
   pointer(dbcanquery) := GetProcedureAddress(DBLibLibraryHandle,'dbcanquery');
   pointer(dbexit) := GetProcedureAddress(DBLibLibraryHandle,'dbexit');
   pointer(dbfreelogin) := GetProcedureAddress(DBLibLibraryHandle,{$IFDEF freetds}'dbloginfree'{$ELSE}'dbfreelogin'{$ENDIF});
   pointer(dbclose) := GetProcedureAddress(DBLibLibraryHandle,'dbclose');
   {$IFDEF ntwdblib}
   pointer(dbopen) := GetProcedureAddress(DBLibLibraryHandle,'dbopen');
   pointer(dbwinexit) := GetProcedureAddress(DBLibLibraryHandle,'dbwinexit');
   {$ENDIF}
   {$IFDEF freetds}
   pointer(tdsdbopen) := GetProcedureAddress(DBLibLibraryHandle,'tdsdbopen');
   pointer(dbtablecolinfo) := GetProcedureAddress(DBLibLibraryHandle,'dbtablecolinfo');
   pointer(dbtds) := GetProcedureAddress(DBLibLibraryHandle,'dbtds');
   pointer(dbsetlversion) := GetProcedureAddress(DBLibLibraryHandle,'dbsetlversion');
   pointer(dbservcharset) := GetProcedureAddress(DBLibLibraryHandle,'dbservcharset');
   //if not assigned(dbiscount) then
   //  raise EInOutError.Create('Minimum supported version of FreeTDS client library is 0.91!');
   {$ENDIF}
   DBLibInit:=false;
  end;
end;

procedure ReleaseDBLib;
begin
  if RefCount > 0 then dec(RefCount);
  if RefCount = 0 then
  begin
    dbexit;{$IFDEF WINDOWS}dbwinexit;{$ENDIF}
    if UnloadLibrary(DBLibLibraryHandle) then
      DBLibLibraryHandle := NilHandle
    else
      inc(RefCount);
  end;
end;
{$ELSE}
procedure InitialiseDBLib(LibraryName : string);
begin
  //no-op for static linked
end;

procedure ReleaseDBLib;
begin
  //no-op for static linked
end;
{$ENDIF LOAD_DYNAMICALLY}

//functions, which are not implemented by FreeTDS:
{$IFDEF freetds}
function dbopen(login:PLOGINREC; servername:PChar):PDBPROCESS;
begin
  Result:=tdsdbopen(login, servername, 1{1=MSDBLIB or 0=SYBDBLIB});
end;

function dbsetlcharset(login:PLOGINREC; charset:PChar):RETCODE;
begin
  Result:=dbsetlname(login, charset, 10);
end;

function dbsetlsecure(login:PLOGINREC):RETCODE;
begin
  //not implemented; see http://www.freetds.org/userguide/domains.htm
  Result:=SUCCEED;
end;

procedure dbwinexit;
begin
  //do nothing
end;
{$ENDIF}

//functions which are not implemented by ntwdblib:
{$IFDEF ntwdblib}
function tdsdbopen(login:PLOGINREC; servername:PChar; msdblib:INT):PDBPROCESS;
begin
  Result:=dbopen(login, servername);
end;

function dbtablecolinfo(dbproc:PDBPROCESS; column:DBINT; dbcol:PDBCOL):RETCODE;
begin
  Result:=dbcolinfo(dbproc, CI_REGULAR, column, 0, dbcol);
  if dbcol^.VarLength {true also when column is nullable} then
    case dbcol^.Typ of
      SQLCHAR  : dbcol^.Typ := SQLVARCHAR;
      SQLBINARY: dbcol^.Typ := SQLVARBINARY;
    end;
end;

function dbsetlversion(login:PLOGINREC; version:BYTE):RETCODE;
begin
  Result:=dbsetlname(login, nil, version);
end;

function dbsetlcharset(login:PLOGINREC; charset:PChar):RETCODE;
begin
  Result:=SUCCEED;
end;

function dbsetlsecure(login:PLOGINREC):RETCODE;
begin
  Result:=dbsetlname(login, nil, DBSETSECURE);
end;

function dbtds(dbproc:PDBPROCESS):INT;
begin
  Result:=0;
end;

function dbversion():PChar;
begin
  Result:='DB Library version 8.00';
end;
{$ENDIF}

{
//ntwdblib uses low significant values first
//freetds  uses variable length array (based on precision) see numeric.c: tds_numeric_bytes_per_prec
//         and starts from high significant values first
function dbnumerictobcd(dbnum: DBNUMERIC): TBCD;
var i: integer;
    intval,intbase,intdiv: int64;
    bcdval,bcdbase,bcddiv, bcd1: TBCD;
begin
  intval:=0;
  intbase:=1;
  for i:=0 to 6 do
  begin
    intval := intval + dbnum.val[i] * intbase;
    intbase:= intbase*256;
  end;
  bcdval := IntegerToBCD(intval);

  if dbnum.precision > 16 then
  begin
    bcdbase := IntegerToBCD(intbase);
    for i:=7 to length(dbnum.val)-1 do
    begin
      BCDMultiply(bcdbase, integer(dbnum.val[i]), bcd1);
      BCDAdd(bcdval, bcd1, bcdval);
      BCDMultiply(bcdbase, 256, bcdbase);
    end;
  end;

  if dbnum.scale > 18 then
  begin
    bcddiv:=IntegerToBCD(int64(1000000000000000000));
    for i:=19 to dbnum.scale do BCDMultiply(bcddiv, 10, bcddiv);
  end
  else
  begin
    intdiv:=1;
    for i:=1 to dbnum.scale do intdiv:=intdiv*10;
    bcddiv:=IntegerToBCD(intdiv);
  end;

  BCDDivide(bcdval, bcddiv, Result);
  if dbnum.sign=0 then BCDNegate(Result);
end;
}

{$IFNDEF LOAD_DYNAMICALLY}
finalization
  dbexit; {$IFDEF WINDOWS}dbwinexit;{$ENDIF}
{$ENDIF}

end.
