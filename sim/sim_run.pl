#!/bin/perl
################################################################################
##
## Filename:	sim_run.pl
## {{{
## Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
##
## Purpose:	
##
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2022-2024, Gisselquist Technology, LLC
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
use Cwd;
$path_cnt = @ARGV;

# Usage: sim_run all
# 	sim_run [cover|iverilog|verilator] [all|<testcasename>+]
## Setup
## {{{
my $verilator_flag = 1;		# To run Icarus, run: perl sim_run.pl iverilog
my $verilator_lint_only = 0;
my $vobjd = "obj_dir";
my $testd = "test";
my $simd  = "rtl";
my $rtld  = "../rtl/export";
my $report= $testd . "/sim_report.txt";
## To run coverage, run: perl sim_run.pl cover
my $coverage_flag = 0;
my $linestr="----------------------------------------";
## Need to find the base verilator directory
my $verilatord;
if (-x "verilator") {
	open(VDEF,"verilator -V |");
	while($line = <VDEF>) {
		if ($line =~ /VERILATOR_ROOT\s*=\s*(\S+)\s*$/) {
			$verilatord = $1;
			# Don't end here, wait for the last VERILATOR_ROOT
			# last;
		}
	} close VDEF;
} else {
	$verilator_flag = 0;
	$verilatord = "";
}
##
##
my $asmconfig =" -POPT_PIPELINED=0"
	. " -POPT_LGDCACHE=0"
	. " -POPT_LGICACHE=0"
	. " -POPT_MPY=0"
	. " -POPT_DIV=0"
	. " -POPT_SHIFTS=0"
	. " -POPT_LOCK=0"
	. " -POPT_EARLY_BRANCHING=0"
	. " -POPT_LOWPOWER=0"
	. " -POPT_DISTRIBUTED_REGS=0"
	. " -POPT_USERMODE=0"
	. " -POPT_CLKGATE=0"
	. " -POPT_DBGPORT=0"
	. " -POPT_TRACE_PORT=0"
	. " -POPT_CIS=0 ";

my $trapconfig =" -POPT_PIPELINED=0"
	. " -POPT_LGDCACHE=0"
	. " -POPT_LGICACHE=0"
	. " -POPT_MPY=0"
	. " -POPT_DIV=0"
	. " -POPT_SHIFTS=1"
	. " -POPT_LOCK=1"
	. " -POPT_EARLY_BRANCHING=0"
	. " -POPT_LOWPOWER=0"
	. " -POPT_DISTRIBUTED_REGS=0"
	. " -POPT_USERMODE=1"
	. " -POPT_CLKGATE=0"
	. " -POPT_DBGPORT=0"
	. " -POPT_TRACE_PORT=0"
	. " -POPT_CIS=0 ";

my $minconfig =" -POPT_PIPELINED=0"
	. " -POPT_LGDCACHE=0"
	. " -POPT_LGICACHE=0"
	. " -POPT_MPY=6"
	. " -POPT_DIV=1"
	. " -POPT_SHIFTS=1"
	. " -POPT_LOCK=1"
	. " -POPT_EARLY_BRANCHING=0"
	. " -POPT_LOWPOWER=0"
	. " -POPT_DISTRIBUTED_REGS=0"
	. " -POPT_USERMODE=1"
	. " -POPT_CLKGATE=0"
	. " -POPT_DBGPORT=1"
	. " -POPT_TRACE_PORT=0"
	. " -POPT_CIS=1 ";

my $pipeconfig =" -POPT_PIPELINED=1"
	. " -POPT_LGDCACHE=2"
	. " -POPT_LGICACHE=2"
	. " -POPT_MPY=6"
	. " -POPT_DIV=1"
	. " -POPT_SHIFTS=1"
	. " -POPT_LOCK=1"
	. " -POPT_EARLY_BRANCHING=1"
	. " -POPT_LOWPOWER=0"
	. " -POPT_DISTRIBUTED_REGS=0"
	. " -POPT_USERMODE=1"
	. " -POPT_CLKGATE=0"
	. " -POPT_DBGPORT=1"
	. " -POPT_TRACE_PORT=0"
	. " -POPT_CIS=1 ";

my $cacheconfig =" -POPT_PIPELINED=1"
	. " -POPT_LGDCACHE=12"
	. " -POPT_LGICACHE=12"
	. " -POPT_MPY=6"
	. " -POPT_DIV=1"
	. " -POPT_SHIFTS=1"
	. " -POPT_LOCK=1"
	. " -POPT_EARLY_BRANCHING=1"
	. " -POPT_LOWPOWER=0"
	. " -POPT_DISTRIBUTED_REGS=0"
	. " -POPT_USERMODE=1"
	. " -POPT_CLKGATE=0"
	. " -POPT_DBGPORT=1"
	. " -POPT_TRACE_PORT=0"
	. " -POPT_CIS=1";

my $lowpowercfg =" -POPT_PIPELINED=1"
	. " -POPT_LGDCACHE=12"
	. " -POPT_LGICACHE=12"
	. " -POPT_MPY=6"
	. " -POPT_DIV=1"
	. " -POPT_SHIFTS=1"
	. " -POPT_LOCK=1"
	. " -POPT_EARLY_BRANCHING=1"
	. " -POPT_LOWPOWER=1"
	. " -POPT_DISTRIBUTED_REGS=0"
	. " -POPT_USERMODE=1"
	. " -POPT_CLKGATE=1"
	. " -POPT_DBGPORT=1"
	. " -POPT_TRACE_PORT=0"
	. " -POPT_CIS=1";

%cfghash = ();
$cfghash{"WBBASM"}  = "-POPT_ZIPBONES=1 $asmconfig";
$cfghash{"WBASM"}   = "-POPT_ZIPBONES=0 $asmconfig";
$cfghash{"WBBTRAP"} = "-POPT_ZIPBONES=1 $trapconfig";
$cfghash{"WBTRAP"}  = "-POPT_ZIPBONES=0 $trapconfig";
$cfghash{"WBBMIN"}  = "-POPT_ZIPBONES=1 $minconfig";
$cfghash{"WBMIN"}   = "-POPT_ZIPBONES=0 $minconfig";
$cfghash{"WBBPIPE"} = "-POPT_ZIPBONES=1 $pipeconfig";
$cfghash{"WBPIPE"}  = "-POPT_ZIPBONES=0 $pipeconfig";
$cfghash{"WBBCACHE"}= "-POPT_ZIPBONES=1 $cacheconfig";
$cfghash{"WBCACHE"} = "-POPT_ZIPBONES=0 $cacheconfig";
$cfghash{"WBBLPWR"} = "-POPT_ZIPBONES=1 $lowpowercfg";
$cfghash{"WBLPWR"}  = "-POPT_ZIPBONES=0 $lowpowercfg";

$cfghash{"AXLASM"}  = "-POPT_ZIPAXIL=1 $asmconfig";
$cfghash{"AXASM"}   = "-POPT_ZIPAXIL=0 $asmconfig";
$cfghash{"AXLTRAP"} = "-POPT_ZIPAXIL=1 $trapconfig";
$cfghash{"AXTRAP"}  = "-POPT_ZIPAXIL=0 $trapconfig";
$cfghash{"AXLMIN"}  = "-POPT_ZIPAXIL=1 $minconfig";
$cfghash{"AXMIN"}   = "-POPT_ZIPAXIL=0 $minconfig";
$cfghash{"AXLPIPE"} = "-POPT_ZIPAXIL=1 $pipeconfig";
$cfghash{"AXPIPE"}  = "-POPT_ZIPAXIL=0 $pipeconfig";
$cfghash{"AXCACHE"} = "-POPT_ZIPAXIL=0 $cacheconfig";
$cfghash{"AXLPWR"}  = "-POPT_ZIPAXIL=0 $lowpowercfg";
##
##
%cfgfiles = ();
$cfgfiles{"WBBASM"}  = "-c rtl/sim_wbfiles.txt -s wb_tb";
$cfgfiles{"WBASM"}   = "-c rtl/sim_wbfiles.txt -s wb_tb";
$cfgfiles{"WBBTRAP"} = "-c rtl/sim_wbfiles.txt -s wb_tb";
$cfgfiles{"WBTRAP"}  = "-c rtl/sim_wbfiles.txt -s wb_tb";
$cfgfiles{"WBBMIN"}  = "-c rtl/sim_wbfiles.txt -s wb_tb";
$cfgfiles{"WBMIN"}   = "-c rtl/sim_wbfiles.txt -s wb_tb";
$cfgfiles{"WBBPIPE"} = "-c rtl/sim_wbfiles.txt -s wb_tb";
$cfgfiles{"WBPIPE"}  = "-c rtl/sim_wbfiles.txt -s wb_tb";
$cfgfiles{"WBBCACHE"}= "-c rtl/sim_wbfiles.txt -s wb_tb";
$cfgfiles{"WBCACHE"} = "-c rtl/sim_wbfiles.txt -s wb_tb";
$cfgfiles{"WBBLPWR"} = "-c rtl/sim_wbfiles.txt -s wb_tb";
$cfgfiles{"WBLPWR"}  = "-c rtl/sim_wbfiles.txt -s wb_tb";

$cfgfiles{"AXLASM"}  = "-c rtl/sim_axfiles.txt -s axi_tb";
$cfgfiles{"AXASM"}   = "-c rtl/sim_axfiles.txt -s axi_tb";
$cfgfiles{"AXLTRAP"} = "-c rtl/sim_axfiles.txt -s axi_tb";
$cfgfiles{"AXTRAP"}  = "-c rtl/sim_axfiles.txt -s axi_tb";
$cfgfiles{"AXLMIN"}  = "-c rtl/sim_axfiles.txt -s axi_tb";
$cfgfiles{"AXMIN"}   = "-c rtl/sim_axfiles.txt -s axi_tb";
$cfgfiles{"AXLPIPE"} = "-c rtl/sim_axfiles.txt -s axi_tb";
$cfgfiles{"AXPIPE"}  = "-c rtl/sim_axfiles.txt -s axi_tb";
$cfgfiles{"AXCACHE"} = "-c rtl/sim_axfiles.txt -s axi_tb";
$cfgfiles{"AXLPWR"}  = "-c rtl/sim_axfiles.txt -s axi_tb";
## }}}

## Process arguments
## {{{
$all_run = 0;
if ($ARGV[0] eq "") {
	print "No test cases given\n";
	exit(0);
} elsif ($ARGV[0] eq "all") {
	$all_run  =1;
	open(SUM,">> $report");
	print(SUM "\nRunning all tests:\n$linestr\n");
	close SUM;
} elsif ($ARGV[0] eq "cover" or $ARGV[0] =~ /^cover/i) {
	$all_run  =1;
	if ($verilatord eq "" or ! -d $verilatord) {
		die "No verilator install directory found at $verilatord";
	}
	$verilator_flag = 1;
	$coverage_flag  = 1;
	open(SUM,">> $report");
	print(SUM "\nRunning all tests for cover:\n$linestr\n");
	close SUM;
} elsif (($ARGV[0] eq "icarus" or $ARGV[0] eq "iverilog") and $ARGV[1] eq "all") {
	$all_run  =1;
	$verilator_flag = 0;
	$coverage_flag  = 0;
	open(SUM,">> $report");
	print(SUM "\nRunning all tests using Icarus:\n$linestr\n");
	close SUM;
} elsif ($ARGV[0] =~ /^verilator/i and ($#ARGV eq 0 or $ARGV[1] eq "all")) {
	$all_run  =1;
	if ($verilatord eq "" or ! -d $verilatord) {
		die "No verilator install directory found at $verilatord";
	}
	$verilator_flag = 1;
	$coverage_flag  = 0;
	open(SUM,">> $report");
	print(SUM "\nRunning all tests with Verilator:\n$linestr\n");
	close SUM;
} elsif ($ARGV[0] eq "icarus" or $ARGV eq "iverilog") {
	$verilator_flag = 0;
	$coverage_flag  = 0;
	@array = @ARGV;
	# Remove the "Icarus" flag
	splice(@array, 0, 1);
} elsif ($ARGV[0] =~ /^verilator/i) {
	if ($verilatord eq "" or ! -d $verilatord) {
		die "No verilator install directory found at $verilatord";
	}
	$verilator_flag = 1;
	$coverage_flag  = 0;
	@array = @ARGV;
	# Remove the "Verilator" flag
	splice(@array, 0, 1);
} else {
	@array = @ARGV;
}
## }}}

## simline: Simulate, given a test configuration
## {{{
sub simline($) {
	my $line = shift;

	my $tstname;
	my $config;
	my $memfil;
	my $confil;
	my $params;

	my $vcddump=0;
	my $vcdfile="";
	my $lint_only = 0;

	while ($line =~ /^(.*)#.*/) {
		$line = $1;
	} if ($line =~ /^\s*(\S+)\s*(\S+)\s*(\S+)\s*(\S+)\s(.*)\s*$/) {
		## {{{
		$tstname = $1;
		$config  = $2;
		$memfil  = $3;
		$confil  = $4;
		$params  = $5;

		## Create an initial timestamp for this run
		## {{{
		($sc,$mn,$hr,$dy,$mo,$yr,$wday,$yday,$isdst)=localtime(time);
		$yr=$yr+1900; $mo=$mo+1;
		$tstamp = sprintf("%04d/%02d/%02d %02d:%02d:%02d",
					$yr,$mo,$dy,$hr,$mn,$sc);
		## }}}

		## Build up the simulation command
		## {{{
		if ($verilator_flag) {
			## Setup the Verilator command
			## {{{
			$lint_only = $verilator_lint_only;

			$cmd = "verilator -Wall -Wno-TIMESCALEMOD --trace";
			# $cmd = $cmd . " -Wno-UNUSED";
			if ($lint_only != 0) {
				$cmd = $cmd . " --lint_only";
			} else {
				if ($coverage_flag) {
					$cmd = $cmd . " --coverage";
				} $cmd = $cmd . " -O3";
			}
			$cmd = $cmd . " -y rtl/ -y ../rtl/ -y ../rtl/core";
			$cmd = $cmd . " -y ../rtl/peripherals -y ../rtl/ex";
			$cmd = $cmd . " -y ../rtl/zipdma";
			$cmd = $cmd . " --prefix $tstname";

			if ($cfgfiles{$config} =~ /-s\s+(\S+)\s/) {
				$toplevel = $1;
			} elsif ($cfgfiles{$config} =~ /-s\s+(\S+)$/) {
				$toplevel = $1;
			} else {
				$toplevel = "no_tb";
			}

			if ($cfghash{$config} ne "") {
				## Must include sim file list and top level
				## as well as any parameters
				$cfgstr = $cfghash{$config};
				$cfgstr =~ s/-P/-G/g;
				$cfgstr =~ s/\"/\\\"/g;
				$cmd = $cmd . " " . $cfgstr;
			}

			$vcddump=0;
			$vcdfile= $testd . "/" . $tstname . ".vcd";
			## printf("CFG-HASH=%s\n", $cfghash{$config});
			if ($cfghash{$config} =~ /DUMP_TO_VCD=(\d+)/) {
				$vcddump=$1;
			} if ($cfghash{$config} =~ /VCD_FILE=.(\S+).$/) {
				$vcdfile=$1;
			} elsif ($cfghash{$config} =~ /VCD_FILE=.(\S+).\s/) {
				$vcdfile=$1;
			}

			$cmd = $cmd . " -GMEM_FILE=\\\"zipsw/$memfil\\\"";
			$cmd = $cmd . " -GCONSOLE_FILE=\\\"$testd/$confil\\\"";

			$cdr = $params;
			while($cdr =~ /\s*(\S+)=(\S+)(.*)$/) {
				$p = $1;
				$v = $2;
				$cdr = $3;

				if ($p =~ /COVDATA_FILE/) {
					## This is a C++ build only parameter
				} elsif ($v =~ /\"(.*)\"/) {
					$str = $1;
					$cmd = $cmd . " -G$p=\\\"$str\\\"";
				} else {
					$cmd = $cmd . " -G$p=$v";
				}

				if ($p =~ /DUMP_TO_VCD/) {
					$vcddump=$v;
				} if ($p =~ /VCD_FILE/) {
					$vcdfile=$v;
				} elsif ($p =~ /VCD_FILE=.(\S+).\s/) {
					$vcdfile=$v;
				}

			}

			if ($verilator_lint_only == 0) {
				$cmd = $cmd . " -cc";
			} $cmd = $cmd . " $toplevel" . ".v";
			## }}}
		} else {
			## Set up the IVerilog command
			## {{{
			$coverage_flag  = 0;

			$cmd = "iverilog -g2012";

			if ($cfgfiles{$config} =~ /-s\s+(\S+)\s/) {
				$toplevel = $1;
			} elsif ($cfgfiles{$config} =~ /-s\s+(\S+)$/) {
				$toplevel = $1;
			} else {
				$toplevel = "no_tb";
			}

			if ($cfghash{$config} ne "") {
				## Must include sim file list and top level
				## as well as any parameters
				$cfgstr = $cfghash{$config};
				$cfgstr =~ s/-P/-P$toplevel./g;
				$cfgstr =~ s/\"/\\\"/g;
				$cmd = $cmd . " " . $cfgstr;
			}

			$cmd = $cmd . " -P$toplevel.MEM_FILE=\\\"zipsw/$memfil\\\"";
			$cmd = $cmd . " -P$toplevel.CONSOLE_FILE=\\\"$testd/$confil\\\"";

			$cdr = $params;
			while($cdr =~ /\s*(\S+)=(\S+)(.*)$/) {
				$p = $1;
				$v = $2;
				$cdr = $3;

				if ($p =~ /COVDATA_FILE/) {
					## This is a C++ build only parameter
				} elsif ($v =~ /\"(.*)\"/) {
					$str = $1;
					$cmd = $cmd . " -P$toplevel.$p=\\\"$str\\\"";
				} else {
					$cmd = $cmd . " -P$toplevel.$p=$v";
				}
			}

			if ($cfgfiles{$config} ne "") {
				$cmd = $cmd . " " . $cfgfiles{$config};
			}

			$cmd = $cmd . " -o $testd/$tstname";
			## }}}
		}
		## }}}

		$sim_log = "test/" . $tstname . ".txt";

		## Build the simulation executable
		## {{{
		if ($lint_only != 0) {
			system "echo \"$tstamp -- Starting lint\" | tee $sim_log";
		} else {
			system "echo \"$tstamp -- Starting build\" | tee $sim_log";
		}

		if (-e "$testd/$tstname") {
			unlink "$testd/$tstname";
		}

		$cmd = $cmd . " |& tee -a $sim_log";
		system "echo \'$cmd\'";
		system "bash -c \'$cmd\'";
		$errB = $?;

		if ($errB ne 0) {
			die "Could not build test!";
		}

		if ($errB == 0 and $verilator_flag) {
			## {{{
			system "cd $vobjd; make -j 12 -f $tstname.mk";
			$errB = $?;
			if ($errB == 0 and $lint_only == 0) {
				$bldcmd = "g++ -Wall";
				# $bldcmd = $bldcmd . " -g -Og";
				$bldcmd = $bldcmd . " -O3";
				$bldcmd = $bldcmd . " -DROOT_VERILATOR -faligned-new";
				if ($vcddump) {
					$bldcmd = $bldcmd . " -DVCD_FILE=\\\"$vcdfile\\\"";
				}

				if ($toplevel eq "axi_tb") {
					$bldcmd = $bldcmd . " -DAXI";
				}
				# $bldcmd = $bldcmd . " -D$config";
				$bldcmd = $bldcmd . " -DBASE=$tstname";
				$bldcmd = $bldcmd . " -DBASEINC='\"$tstname.h\"'";
				$bldcmd = $bldcmd . " -DROOTINC='\"$tstname";
				$bldcmd = $bldcmd . "___024root.h\"'";
				if ($coverage_flag) {
					$bldcmd = $bldcmd . " -DVM_COVERAGE=1";
					if ($params =~ /COVDATA_FILE=(\S.*)/) {
						$bldcmd = $bldcmd . " -DCOVDATA_FILE=\\\"test/$1\\\"";
					} elsif ($cfghash{$config} =~ /COVDATA_FILE=(\S.*)/) {
						$bldcmd = $bldcmd . " -DCOVDATA_FILE=\\\"test/$1\\\"";
					} else {
						$bldcmd = $bldcmd . " -DCOVDATA_FILE=\\\"test/$tstname.dat\\\"";
					}
				}

				# $bldcmd = $bldcmd . " -DCORE=axi_tb__DOT__GEN_ZIPAXIL__DOT__u_cpu__DOT__core";
				$bldcmd = $bldcmd . " -I$verilatord/include";
				$bldcmd = $bldcmd . " -I$verilatord/include/vltstd";
				$bldcmd = $bldcmd . " -I../sw/zasm";
				$bldcmd = $bldcmd . " -I$vobjd";
				$bldcmd = $bldcmd . " $verilatord/include/verilated.cpp";
				$bldcmd = $bldcmd . " $verilatord/include/verilated_vcd_c.cpp";
				$bldcmd = $bldcmd . " $verilatord/include/verilated_threads.cpp";
				if ($coverage_flag) {
					$bldcmd = $bldcmd . " $verilatord/include/verilated_cov.cpp";
				}
				$bldcmd = $bldcmd . " -DBASE=$tstname";
				$bldcmd = $bldcmd . " verilator/vbare_tb.cpp $vobjd/$tstname" . "__ALL.a";
				$bldcmd = $bldcmd . " -lpthread";
				$bldcmd = $bldcmd . " -o $testd/$tstname";

				system "echo $bldcmd";
				system $bldcmd;
				$errB = $?;
			}
			## }}}
		}
		## }}}

		if ($lint_only != 0) {
		} elsif ($errB == 0 and -x "$testd/$tstname") {
			## Run the simulation
			## {{{
			($sc,$mn,$hr,$dy,$mo,$yr,$wday,$yday,$isdst)=localtime(time);
			$yr=$yr+1900; $mo=$mo+1;
			$tstamp = sprintf("%04d/%02d/%02d %02d:%02d:%02d",
					$yr,$mo,$dy,$hr,$mn,$sc);
			system "echo \"$tstamp -- Starting simulation\" | tee -a $sim_log";
			system "$testd/$tstname >> $sim_log";

			## Finish the log with another timestamp
			## {{{
			($sc,$mn,$hr,$dy,$mo,$yr,$wday,$yday,$isdst)=localtime(time);
			$yr=$yr+1900; $mo=$mo+1;
			$tstamp = sprintf("%04d/%02d/%02d %02d:%02d:%02d",
						$yr,$mo,$dy,$hr,$mn,$sc);
			system "echo $tstamp >> $sim_log";
			## }}}

			## Look through the log file(s) for any errors
			## and report them
			## {{{
			system "grep \'ERROR\' $sim_log | sort -u";
			system "grep -q \'ERROR\' $sim_log";
			$errE = $?;
			system "grep -iq \'assert.*fail\' $sim_log";
			$errA = $?;
			system "grep -iq \'fail\' $sim_log";
			$errF = $?;
			system "grep -iq \'TEST SUCCESS\' $sim_log";
			$errS = $?;
			system "grep -v \"Not enough words in the file for the requested range\" $sim_log | grep -iq \'warning\'";
			$warnW = $?;

			open (SUM,">> $report");
			if ($verilator_flag) {
			$msg = sprintf("%s Verilator -- %s", $tstamp, $tstname);
			} else {
			$msg = sprintf("%s IVerilog  -- %s", $tstamp, $tstname);
			}
			if ($errE == 0 or $errA == 0 or $errF == 0) {
				## {{{
				## ERRORs found
				print SUM "ERRORS    $msg\n";
				print     "ERRORS    $msg\n";
				push @failed,$tstname;
				## }}}
			} elsif ($warnW == 0) {
				## {{{
				print SUM "Warnings! $msg\n";
				print     "Warnings! $msg\n";
				push @passed,$tstname;
				## }}}
			# } elsif ($errS != 0) {
				## TEST SUCCESS message not found
			} elsif ($coverage_flag) {
				## {{{
				print SUM "COVERED   $msg\n";
				print     "COVERED   $msg\n";
				push @passed,$tstname;
				## }}}
			} else {
				## {{{
				print SUM "Pass      $msg\n";
				print     "Pass      $msg\n";
				push @passed,$tstname;
				## }}}
			}
			## }}}
			## }}}
		} else {
			## Report that this failed to build
			## {{{
			open (SUM, ">> $report");
			if ($verilator_flag) {
			$msg = sprintf("%s Verilator -- %s", $tstamp, $tstname);
			} else {
			$msg = sprintf("%s IVerilog  -- %s", $tstamp, $tstname);
			}
			print SUM "BLD-FAIL  $msg\n";

			push @failed,$tstname;

			close SUM;
			## }}}
		}
		## }}}
	} else {
		print "No match for line: $line\n";
	}
}
## }}}

## gettest: Look up a test's configuration
## {{{
sub gettest($) {
	my ($key)=@_;
	my	$tstname;

	open(GTL,"sim_testcases.txt");
	while($line = <GTL>) {
		next if ($line =~ /^\s*#/);
		if ($line =~ /^\s*(\S+)\s/) {
			$tstname = $1;
			last if ($tstname eq $key);
		}
	}
	close GTL;
	if ($tstname eq $key) {
		$line;
	} else {
		"# FAIL";
	}
}
## }}}

## Run all tests
## {{{
if (! -d "$testd/") {
	mkdir $testd;
}

if ($all_run) {
	open(TL,"sim_testcases.txt");
	while($line = <TL>) {
		next if ($line =~ /^\s*#/);
		# print "TEST LINE: $line";
		simline($line);
	}

	open(SUM,">> $report");
	if ($coverage_flag) {
		print(SUM "$linestr\nCoverage complete\n\n");
	} else {
		print(SUM "$linestr\nTest run complete\n\n");
	}
	close SUM;
} else {
	foreach $akey (@array) {
		$line = gettest($akey);
		next if ($line =~ /FAIL/);
		# print "TEST LINE: $line";
		simline($line);
	}
}
## }}}
