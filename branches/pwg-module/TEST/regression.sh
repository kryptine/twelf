#!/bin/bash
# TWELF REGRESSION TEST
# Author: Robert J. Simmons
# 
# TEST/regression.sh [ full ]
# Tests the regression suite - only in SML by default, and in multiple
# implementations if the function is passed an argument.
# provides timing information and should stay largely silent if there
# are no problems.

MLTON="mlton"
SML="sml"
SML_FLAGS="-Ccm.verbose=false -Ccompiler-mc.warn-non-exhaustive-match=false sources.cm -Ccompiler-mc.warn-non-exhaustive-bind=false -Ccontrol.poly-eq-warn=false"
POSTFIX=$( date +%y%m%d )
TIME="/usr/bin/time -f%e\treal\n%U\tuser"

#echo "=== Running regression test in SML/NJ ==="
#$TIME $SML $SML_FLAGS sources.cm TEST/quiet.sml TEST/regression.txt
#
#if [ $1 = "" ]
#then
#   echo "==== Completed! ==="
#   exit
#fi

echo "=== Compiling regression test package in MLton ==="
$TIME $MLTON -default-ann "nonexhaustiveMatch ignore" TEST/mlton-regression.cm

echo ""
echo "=== Running regression test in MLton ==="
$TIME TEST/mlton-regression TEST/regression.txt

echo ""
echo "=== Running TALT ==="
$TIME TEST/mlton-regression TEST/regression-talt.txt

echo ""
echo "=== Running TS-LF (Definition of Standard ML) ==="
$TIME TEST/mlton-regression TEST/regression-tslf.txt

echo ""
echo "=== Running misc. public code ==="
$TIME TEST/mlton-regression TEST/regression-public.txt

rm -f TEST/mlton-regression

echo "==== Completed! ==="
 
