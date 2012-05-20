#!/usr/bin/env bash


temps="./check_const_list.sh"

if [ "$1" == "clean" ] ; then
  echo Removing $temps
  rm -f $temps
  exit
fi

if [ "$1" == "verbose" ] ; then
  verbose=1
  shift
else
  verbose=0
fi

os=`uname -s`

if [ "$os" == "NetBSD" ] ; then
  needgsed=1
fi

SED=sed

if [ $needgsed -eq 1 ] ; then
  SED=
  SED=`which gsed`
  if [ "$SED" == "" ] ; then
    echo "GNU sed not found, this script might not work optimally"
    SED=sed
  fi
fi


for file in $@ ; do 

echo "Looking for constants in \"$file\""
$SED  -n "s:.*[[:space:]]\([a-zA-Z_][a-zA-Z_0-9]*\)[[:space:]]*=[[:space:]]*\([-+]*[0-9][xX]*[0-9+-\*/]*\)[[:space:]]*;.*:test_const \1 \2:p" $file  >  check_const_list.sh

test_const ()
{
name=$1
value=$2
if [ $verbose -eq 1 ]; then
  echo "Looking for $name, should be $value"
fi
ok=0
matchvalue=
source=
namelist=`grep -i -n -r "#[[:space:]]*define[[:space:]]*$name[[:space:]]" /usr/include`
# Remove comments
namelist=${namelist//\/\**/}
# Remove trailing spaces
namelist=${namelist%%[[:space:]]}
if [ -n "$namelist" ]; then
  source=${namelist//#define*/}
  if [ $verbose -eq 1 ] ; then
    echo "Exact match found: \"$namelist\"" 
  fi
  matchvalue=`echo ${namelist} |$SED "s|.*#[[:space:]]*define[[:space:]]*$name[[:space:]]*||I" ` 
  if [ $verbose -eq 1 ] ; then
    echo "matchvalue=\"$matchvalue\""
  fi
  matchvalue="${matchvalue#"${matchvalue%%[![:space:]]*}"}"
else
  if [ $verbose -eq 1 ] ; then
    echo "$name not found"
  fi
  namelist2=`grep -i $name -r -n /usr/include`
  if [ -n "$namelist2" ]; then
    echo "Match found: \"$namelist2\""
    source=${namelist2//:*/}
    matchvalue=${namelist//#define*$name2/} 
  fi
fi
if [ "$matchvalue" == "$value" ] ; then
    echo "OK:      Constant \"$name\" value OK: \"$value\" location \"$source\""
else
  if [ "$source" != "" ] ; then
    echo "Warning: Constant \"$name\" has value \"$value\" inside \"$file\" but \"$matchvalue\" location \"$source\"" 
  else
    echo "Warning: Constant \"$name\" has value \"$value\" inside \"$file\" but \"$matchvalue\" in system headers" 
  fi
fi
}

set -f

. ./check_const_list.sh

done

