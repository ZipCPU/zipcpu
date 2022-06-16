#!/bin/perl
use Cwd;
$path_cnt = @ARGV;

# Usage: sim_run all
# 	sim_run <testcasename>
## Setup
## {{{
my $verilator_flag = 0;
my $testd = "test";
my $simd  = "rtl";
my $rtld  = "../rtl/export";
my $report= $testd . "/sim_report.txt";
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
	print(SUM "\nRunning all tests:\n--------------------\n\n");
	close SUM;
} else {
	@array = @ARGV;
}
## }}}

## simline: Simulate, given a test configuration
## {{{
sub simline($) {
	my $line = shift;
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
			$cmd = "verilator -Wall -Wno-TIMESCALEMOD --trace";
			$cmd = $cmd . " -O3";
			$cmd = $cmd . " -y rtl/ -y ../rtl/ -y ../rtl/core -y ../rtl/peripherals -y ../rtl/ex";
			$cmd = $cmd . " --prefix $config";

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

			$cmd = $cmd . " -GMEM_FILE=\\\"zipsw/$memfil\\\"";
			$cmd = $cmd . " -GCONSOLE_FILE=\\\"$testd/$confil\\\"";

			$cdr = $params;
			while($cdr =~ /\s*(\S+)=(\S+)(.*)$/) {
				$p = $1;
				$v = $2;
				$cdr = $3;

				if ($v =~ /\"(.*)\"/) {
					$str = $1;
					$cmd = $cmd . " -G$p=\\\"$str\\\"";
				} else {
					$cmd = $cmd . " -G$p=$v";
				}
			}

			$cmd = $cmd . " -cc $toplevel" . ".v";
		} else {
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

				if ($v =~ /\"(.*)\"/) {
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
		}
		## }}}

		$sim_log = "test/" . $tstname . ".txt";

		## Build the simulation
		## {{{
		system "echo \"$tstamp -- Starting build\" | tee $sim_log";
		if (-e "$testd/$tstname") {
			unlink "$testd/$tstname";
		}

		$cmd = $cmd . " |& tee -a $sim_log";
		system "echo \'$cmd\'";
		system "bash -c \'$cmd\'";
		$errB = $?;

		if ($errB == 0 and $verilator_flag) {
			system "cd obj_dir; make -f V$config.mk";
			$errB = $?;
			if ($errB == 0) {
				$bldcmd = "g++ -Wall -g -Og";
				if ($toplevel eq "axi_tb") {
					$bldcmd = $bldcmd . " -DAXI";
				}
				$bldcmd = $bldcmd . " -D$config";
				$bldcmd = $bldcmd . " -I$verilatord/include";
				$bldcmd = $bmdcmd . " -Iobj_dir";
				$bldcmd = $bmdcmd . " $verilatord/include/verilated.cpp";
				$bldcmd = $bmdcmd . " $verilatord/include/verilated_vcd_c.cpp";
				$bldcmd = $bldcmd . " -DBASE=V$config";
				$bldcmd = $bmdcmd . " verilator/zipcpu_tb.cpp -o $config";
			}
		}
		## }}}

		if ($errB == 0 and -x "$testd/$tstname") {
			## Run the simulation
			## {{{
			($sc,$mn,$hr,$dy,$mo,$yr,$wday,$yday,$isdst)=localtime(time);
			$yr=$yr+1900; $mo=$mo+1;
			$tstamp = sprintf("%04d/%02d/%02d %02d:%02d:%02d",
					$yr,$mo,$dy,$hr,$mn,$sc);
			system "echo \"$tstamp -- Starting simulation\" | tee $sim_log";
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

			open (SUM,">> $report");
			if ($verilator_flag) {
			$msg = sprintf("%s Verilator -- %s", $tstamp, $tstname);
			} else {
			$msg = sprintf("%s IVerilog  -- %s", $tstamp, $tstname);
			}
			if ($errE == 0 or $errA == 0 or $errF == 0) {
				## ERRORs found
				print SUM "ERRORS    $msg\n";
				print     "ERRORS    $msg\n";
				push @failed,$tstname;
			# } elsif ($errS != 0) {
				## TEST SUCCESS message not found
			} else {
				print SUM "PASSED    $msg\n";
				print     "PASSED    $msg\n";
				push @passed,$tstname;
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

	open(GTL,"$simd/sim_testcases.txt");
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
if (! -d "test/") {
	mkdir "test";
}

if ($all_run) {
	open(TL,"$simd/sim_testcases.txt");
	while($line = <TL>) {
		next if ($line =~ /^\s*#/);
		# print "TEST LINE: $line";
		simline($line);
	}
} else {
	foreach $akey (@array) {
		$line = gettest($akey);
		next if ($line =~ /FAIL/);
		# print "TEST LINE: $line";
		simline($line);
	}
}
## }}}
