ppcjvm -O2 -g unsupported
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g testintf
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g nested
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g test
if %errorlevel% neq 0 exit /b %errorlevel%
javac -encoding utf-8 -cp ..\..\..\rtl\units\jvm-java;. JavaClass
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. JavaClass
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g sort
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. sort
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g classmeth
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. classmeth
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g classlist
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. classlist
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g testansi
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. testansi
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tcnvstr1
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tcnvstr1
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tcnvstr3
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tcnvstr3
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g testshort
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. testshort
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tarray2
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tarray2
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tarray3
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tarray3
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tnestproc
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tnestproc
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g outpara
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. outpara
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tbytearrres
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tbytearrres
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g forw
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tbyte
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tbyte
if %errorlevel% neq 0 exit /b %errorlevel%
del uenum.ppu
ppcjvm -O2 -g tenum
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tenum
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tprop
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tprop
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tprop2
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tprop2
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tclassproptest
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tclassproptest
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tset3 -dproc
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tset3
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tset3
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tset3
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g taddset
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. taddset
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g taddsetint
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. taddsetint
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tformalpara
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tformalpara
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tvarpara
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tvarpara
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tpvar
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tpvar
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tpvardelphi
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tpvardelphi
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tpvarglobal
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tpvarglobal
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tpvarglobaldelphi
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tpvarglobaldelphi
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tvirtclmeth
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tvirtclmeth
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tdynarrec
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tdynarrec
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tconst
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tconst
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g twith
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. twith
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tint
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tint
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g ttrig
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. ttrig
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g ttrunc
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. ttrunc
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tset1
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tset1
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tabs
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tabs
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tintstr
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tintstr
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g trange1
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. trange1
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g trange2
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. trange2
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g trange3
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. trange3
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tdefpara
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tdefpara
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g getbit
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. getbit
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tthreadvar
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tthreadvar
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tstring1
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tstring1
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tstrreal1
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;.tstrreal1
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g tstrreal2
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tstrreal2
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g -B tval
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tval
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g -B tval5
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tval5
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g -B tstring9
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tstring9
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g -B tstr
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tstr
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g -B tw20212
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tw20212
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g -B tdynarrnil
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tdynarrnil
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g -B tnestdynarr
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. tnestdynarr
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g -B topovl
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. topovl
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g -B tassert
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. -Sa tassert
if %errorlevel% neq 0 exit /b %errorlevel%
ppcjvm -O2 -g -B taddbool
if %errorlevel% neq 0 exit /b %errorlevel%
java -Dfile.encoding=UTF-8 -cp ..\..\..\rtl\units\jvm-java;. -Sa TAddBool
if %errorlevel% neq 0 exit /b %errorlevel%

