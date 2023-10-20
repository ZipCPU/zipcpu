#!/usr/bin/perl
################################################################################
##
## Filename:	genreport.pl
## {{{
## Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
##
## Purpose:	To direct the formal verification of particular components of
##		the ZipCPU.
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2023, Gisselquist Technology, LLC
## {{{
## This program is free software (firmware): you can redistribute it and/or
## modify it under the terms of  the GNU General Public License as published
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
##
## License:	GPL, v3, as defined and found on www.gnu.org,
##		http://www.gnu.org/licenses/gpl.html
##
##
################################################################################
##
## }}}

## Variable declarations
## {{{
$dir = ".";
@proofs = (
	"axidcache",
	"axiicache",
	"axilfetch",
	"axilops",
	"axilpipe",
	"axiops",
	"axipipe",
	"busdelay",
	"cpuops",
	"dblfetch",
	"dcache",
	"div",
	"icontrol",
	"idecode",
	"memops",
	"pfcache",
	"pffifo",
	"pipemem",
	"prefetch",
	"wbdblpriarb",
	"wbwatchdog",
	"zipaxil",
	"zipaxi",
	"zipbones",
	"zipcore",
	"zipcounter",
	"zipdma_mm2s",
	"zipdma_s2mm",
	"zipdma_rxgears",
	"zipdma_txgears",
	"zipjiffies",
	"zipmmu",
	"ziptimer"
	);

%desc = (
	"axidcache"	=> "AXI Data cache",
	"axiicache"	=> "AXI Instruction cache",
	"axilfetch"	=> "AXI-Lite instruction fetch",
	"axilops"	=> "Simple AXI-Lite data controller",
	"axilpipe"	=> "AXI-Lite pipelined memory controller",
	"axiops"	=> "Simple AXI data controller",
	"axipipe"	=> "AXI pipelined memory controller",
	"busdelay"	=> "A bus delay",
	"cpuops"	=> "CPU ALU",
	"dblfetch"	=> "WB Instruction fetch, fetches two insns at a time",
	"dcache"	=> "WB Data cache",
	"div"		=> "Divide unit",
	"icontrol"	=> "Interrupt controller",
	"idecode"	=> "Instruction decoder",
	"memops"	=> "Simple WB memory controller",
	"pfcache"	=> "WB instruction fetch and cache",
	"pffifo"	=> "FIFO based WB instruction fetch",
	"pipemem"	=> "WB Pipelined memory controller",
	"prefetch"	=> "Simple WB instruction fetch",
	"wbdblpriarb"	=> "WB double priority arbiter, for global and local buses",
	"wbwatchdog"	=> "WB Watchdog controller",
	"zipaxil"	=> "AXI-Lite ZipCPU wrapper",
	"zipaxi"	=> "AXI ZipCPU wrapper",
	"zipbones"	=> "Simpler Wishbone wrapper",
	"zipcore"	=> "Core ZipCPU",
	"zipcounter"	=> "A simpler peripheral counter",
	"zipdma_mm2s"	=> "WB ZipDMA read half",
	"zipdma_s2mm"	=> "WB ZipDMA write half",
	"zipdma_rxgears"=> "WB ZipDMA incoming gearbox",
	"zipdma_txgears"=> "WB ZipDMA outgoing gearbox",
	"zipjiffies"	=> "ZipCPU Jiffies peripheral",
	"zipmmu"	=> "Zip MMU (deprecated)",
	"ziptimer"	=> "Peripheral timer"
	);
## }}}

## getstatus subroutine
## {{{
# This subroutine runs make, to see if a proof is up to date, or otherwise
# checks the logfile to see what the status was the last time the proof was
# run.
sub getstatus($) {
	my $based = shift;
	my $log = "$based/logfile.txt";

	my $bmc = 0;
	my $ind = 0;
	my $cvr = 0;
	my $ncvr = 0;

	my $PASS = 0;
	my $FAIL = 0;
	my $UNK = 0;
	my $ERR = 0;
	my $terminated = 0;
	my $current = 1;

	# print "<TR><TD>Checking make $based/PASS</TD></TR>\n";

	if (open(MAK, "make -n $based/PASS |")) {
		while($line = <MAK>) {
			if ($line =~ /sby/) {
				$current = 0;
			}
		} close(MAK);
	}

	# print "<TR><TD>Opening log, $log</TD></TR>\n";

	open (LOG, "< $log") or return "No log";
	while($line = <LOG>) {
		# print "<TR><TD>LINE=$line</TD></TR>\n";
		if ($line =~ /DONE.*FAIL/) {
			$FAIL = 1;
			# print "<TR><TD>FAIL match</TD></TR>\n";
		} if ($line =~ /DONE.*PASS/) {
			$PASS = 1;
			# print "<TR><TD>PASS match</TD></TR>\n";
		} if ($line =~ /DONE.*UNKNOWN/) {
			$UNK = 1;
			# print "<TR><TD>UNKNOWN match</TD></TR>\n";
		} if ($line =~ /DONE.*ERROR/) {
			$ERR = 1;
			# print "<TR><TD>ERROR match</TD></TR>\n";
		} if ($line =~ /terminating process/) {
			$terminated = 1;
		} if ($line =~ /Checking cover/) {
			$cvr = 1;
		} if ($line =~ /engine_\d.induction/) {
			$ind = 1;
			# print "<TR><TD>induction match</TD></TR>\n";
		} if ($line =~ /engine_\d.basecase.*Checking assertions in step\s+(\d+)/) {
			if ($1 > $bmc) {
				$bmc = $1;
				# print "<TR><TD>basecase $bmc match</TD></TR>\n";
			}
		} if ($line =~ /engine_\d:.*Writing trace to VCD.*trace(\d+).vcd/) {
			if ($1 > $ncvr) {
				$ncvr = $1+1;
			}
		}
	}
	close(LOG);

	if ($PASS) {
		if ($current == 0) {
			"Out of date";
		} elsif ($cvr) {
			"Cover $ncvr";
		} else {
			"PASS";
		}
	} elsif ($FAIL) {
		"FAIL";
	} elsif ($ERR) {
		"ERROR";
	} elsif (($ind == 0 || $UNK != 0) && $bmc > 0) {
		"BMC $bmc";
	} elsif ($terminated) {
		"Terminated";
	} else {
		"Unknown";
	}
}
## }}}

## Start the HTML output
## {{{
print <<"EOM";
<HTML><HEAD><TITLE>Formal Verification Report</TITLE></HEAD>
<BODY>
<TABLE border>
<TR><TH>Status</TH><TH>Component</TD><TH>Proof</TH><TH>Component description</TH></TR>
EOM
## }}}

## Look up all directory entries
## {{{
# We'll use this result to look for subdirectories that might contain
# log files.
opendir(DIR, $dir) or die "Cannot open directory for reading";
my @dirent = readdir(DIR);
closedir(DIR);

# print "@dirent";
## }}}

# Lookup each components proof
foreach $prf (sort @proofs) {
	my $ndirs=0;
	foreach $dent (@dirent) {
		next if (! -d $dent);
		next if ($dent =~ /^\./);
		next if ($dent !~ /^$prf(_\S+)/);
			$subprf = $1;

		$ndirs = $ndirs+1;
	}

	my $firstd = 1;

	# Find each subproof of the component
	foreach $dent (@dirent) {
		## Filter out the wrong directories
		## {{{
		# print("<TR><TD>DIR $dent</TD></TR>\n");
		# Only look at subdirectories
		next if (! -d $dent);
		next if ($dent =~ /^\./);
		next if ($dent !~ /^$prf(_\S+)/);
			$subprf = $1;
		# print("<TR><TD>$dent matches $prf</TD></TR>\n");
		## }}}

		## Get the resulting status
		$st = getstatus($dent);
		# print("<TR><TD>STATUS = $st</TD></TR>\n");

		## Fill out one entry of our table
		## {{{
		my $tail;
		if ($firstd) {
			print "<TR></TR>\n";
			$tail = "</TD><TD>$prf</TD><TD>$subprf</TD><TD rowspan=$ndirs>$desc{$prf}</TD></TR>\n";
			$firstd = 0;
		} else {
			$tail = "</TD><TD>$prf</TD><TD>$subprf</TD></TR>\n";
		}
		if ($st =~ /PASS/) {
			print "<TR><TD bgcolor=#caeec8>Pass$tail";
		} elsif ($st =~ /Cover\s+(\d+)/) {
			print "<TR><TD bgcolor=#caeec8>$1 Cover points$tail";
		} elsif ($st =~ /FAIL/) {
			print "<TR><TD bgcolor=#ffa4a4>FAIL$tail";
		} elsif ($st =~ /Terminated/) {
			print "<TR><TD bgcolor=#ffa4a4>Terminated$tail";
		} elsif ($st =~ /ERROR/) {
			print "<TR><TD bgcolor=#ffa4a4>ERROR$tail";
		} elsif ($st =~ /Out of date/) {
			print "<TR><TD bgcolor=#ffffca>Out of date$tail";
		} elsif ($st =~ /BMC\s+(\d)+/) {
			print "<TR><TD bgcolor=#ffffca>$1 steps of BMC$tail";
		} elsif ($st =~ /No log/) {
			print "<TR><TD bgcolor=#e5e5e5>No log file found$tail";
		} else {
			print "<TR><TD bgcolor=#e5e5e5>Unknown$tail";
		}
		## }}}
	} if ($myfirstd != 0) {
		print "<TR><TD bgcolor=#e5e5e5>Not found</TD><TD>$prf</TD><TD>&nbsp;</TD><TD rowspan=$ndirs>$desc{$prf}</TD></TR>\n";
	}
}

## Finish the HTML log file
## {{{
print <<"EOM";
</TABLE>
</BODY></HTML>
EOM
## }}}
