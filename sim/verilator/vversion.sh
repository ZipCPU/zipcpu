#!/bin/bash
################################################################################
##
## Filename:	sim/verilator/vversion.sh
## {{{
## Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
##
## Purpose:	To determine whether or not the verilator prefix for internal
##		variables is v__DOT__ or the name of the top level followed by
##	__DOT__.  If it is the later, output -DNEW_VERILATOR, else be silent.
##
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2017-2025, Gisselquist Technology, LLC
## {{{
## This program is free software (firmware): you can redistribute it and/or
## modify it under the terms of the GNU General Public License as published
## by the Free Software Foundation, either version 3 of the License, or (at
## your option) any later version.
##
## This program is distributed in the hope that it will be useful, but WITHOUT
## ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
## for more details.
##
## You should have received a copy of the GNU General Public License along
## with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
## target there if the PDF file isn't present.)  If not, see
## <http://www.gnu.org/licenses/> for a copy.
## }}}
## License:	GPL, v3, as defined and found on www.gnu.org,
## {{{
##		http://www.gnu.org/licenses/gpl.html
##
################################################################################
##
## }}}
if [[ x${VERILATOR_ROOT} != "x" && -x ${VERILATOR_ROOT}/bin/verilator ]];
then
  export VERILATOR=${VERILATOR_ROOT}/bin/verilator
fi
if [[ ! -x ${VERILATOR} ]];
then
  export VERILATOR=verilator
fi
if [[ ! -x `which ${VERILATOR}` ]];
then
  echo "Verilator not found in environment or in path"
  exit -1
fi

VVERLINE=`${VERILATOR} -V | grep -i ^Verilator`
VVER=`echo ${VVERLINE} | cut -d " " -f 2`
LATER=`echo $VVER \>= 3.9 | bc`
if [[ $LATER > 0 ]];
then
  RLATER=`echo $VVER \>= 4.2 | bc`
  if [[ $RLATER > 0 ]];
  then
    ## I'm not quite certain when Verilator started requiring a further
    ## subreference through rootp-> and including the Vdesgin___024root.h
    ## include file.  My best guess is that it is Verilator 4.2, but I don't
    ## know that for certain.  What I do know is that on the development
    ## verrsion 4.211, it requires different semantics to peek at register
    ## names.  This is our attempt to capture that dependency.
    echo "-DROOT_VERILATOR"
  else
    echo "-DNEW_VERILATOR"
  fi
else
  echo "-DOLD_VERILATOR"
fi
exit 0
