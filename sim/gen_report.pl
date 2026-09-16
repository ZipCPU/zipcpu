#!/bin/perl
################################################################################
##
## Filename:	sim/gen_report.pl
## {{{
## Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
##
## Purpose:	Generate an HTML report file, containing the status of the
##		last simulation run.
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2016-2026, Gisselquist Technology, LLC
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
$wbfiles = "rtl/sim_wbfiles.txt";
$axfiles = "rtl/sim_axfiles.txt";
$testlist = "sim_testcases.txt";
$rawreport= "test/sim_report.txt";
$htmlfil= "report.html";
my $last_mtime = 0, $last_wbtime = 0, $last_axtime = 0;
my $last_tstamp = "";

################################################################################
##
## Get the last file modified time
## {{{
open(FLIST, $wbfiles);
while($line = <FLIST>) {
	if ($line =~ /^\s*#/) {
		next;
	} elsif ($line =~ /^\s*(\S+)\s*$/) {
		$fname = $1;
	} else {
		next;
	}

	my ($dev, $ino, $mode, $nlink, $uid, $gid, $rdev, $size,
		$atime, $mtime, $ctime, $blksize, $blocks) = stat($fname);

	if ($mtime > $last_wbtime) {
		$last_wbtime = $mtime;
	} if ($mtime > $last_mtime) {
		$last_mtime = $mtime;
	}
}
close FLIST;

open(FLIST, $axfiles);
while($line = <FLIST>) {
	if ($line =~ /^\s*#/) {
		next;
	} elsif ($line =~ /^\s*(\S+)\s*$/) {
		$fname = $1;
	} else {
		next;
	}

	my ($dev, $ino, $mode, $nlink, $uid, $gid, $rdev, $size,
		$atime, $mtime, $ctime, $blksize, $blocks) = stat($fname);

	if ($mtime > $last_axtime) {
		$last_axtime = $mtime;
	} if ($mtime > $last_mtime) {
		$last_mtime = $mtime;
	}
}
close FLIST;

my $sc, $mn, $hr, $dy, $mo, $yr, $wd, $yd, $isdst;
($sc, $mn, $hr, $dy, $mo, $yr, $wd, $yd, $isdst) = localtime($last_mtime);
$yr = $yr+1900; $mo=$mo+1;
$last_tstamp = sprintf("%04d/%02d/%02d %02d:%02d:%02d",
			$yr,$mo,$dy,$hr,$mn,$sc);
## }}}
################################################################################
##
## Get the latest test result
## {{{
my $n=0;
my %STAT;
my %SCRIPT;
my %MTIME;

open(REPORT, $rawreport);
while($line = <REPORT>) {
	next if ($line =~ /^-/);
	if ($line =~ /^(\S+)\s+(\d\d\d\d.\d\d.\d\d.\d\d:\d\d:\d\d)\s+(\S+)\s+..\s+(\S+)\s*$/) {
		$status = $1;
		$tstamp = $2;
		$tool = $3;
		$test = $4;
		# $SCRIPT{$test} = "../testcases/$test.v";

		$mtime = $last_mtime;
		open(TESTLIST, $testlist);
		while($line = <TESTLIST>) {
			if ($line =~ /^\s*#/) {
				## Skip any comment lines
				next;
			}

			if ($line =~ /^\s*(\S+)\s+(\S+)\s+(\S+)\s+/) {
				$simcase = $1;
				$simenv  = $2;
				$simsource = $3;
				if ($simcase eq $test) {
					$SCRIPT{$test} = "zipsw/$simsource";
					my ($dev, $ino, $mode, $nlink, $uid,
						$gid, $rdev, $size, $atime,
						$mtime, $ctime, $blksize,
						$blocks) = stat($SCRIPT{$test});
					if ($SCRIPT{$test} =~ /(\S+)64.hex/) {
						my	$cfile = "$1.c";
						if (-e $cfile) {
							$SCRIPT{$test} = $cfile;
						}
					} elsif ($SCRIPT{$test} =~ /(\S+).hex/) {
						my	$cfile = "$1.c";
						if (-e $cfile) {
							$SCRIPT{$test} = $cfile;
						}
					}

					if ($simenv =~ /^WB/) {
						$MTIME{$test} = $last_wbtime;
					} elsif ($simenv =~ /^AX/) {
						$MTIME{$test} = $last_axtime;
					} else {
						$MTIME{$test} = $last_mtime;
					}

					if ($mtime > $MTIME{$test}) {
						$MTIME{$test} = $mtime;
					}
					next;
				}
			}
		} close TESTLIST;

		if ("" eq $SCRIPT{$test}) {
			# delete $STAT{$test};
			# delete $TOOL{$test};
			# delete $TSTAMP{$test};
			delete $SCRIPT{$test};
			next;
		}

		if ("$tstamp" lt "$last_tstamp") {
			$STAT{$test} = "Out-of-date";
			$TOOL{$test} = $tool;
			$TSTAMP{$test} = $tstamp;
			next;
		}

		if (exists $STAT{$test}) {
			## Merge results with a potential prior test
			my $last_tool, $last_stat;
			my $last_passing, $passing;

			$last_tool = $TOOL{$test};
			$last_stat = $STAT{$test};

			# Find which results passed
			## {{{
			if (($last_stat =~ /pass/i) or ($last_stat =~ /cover/i)) {
				$last_passing = 1;
			} else {
				$last_passing = 0;
			}

			if (($status =~ /pass/i) or ($status =~ /cover/i)) {
				$passing = 1;
			} else {
				$passing = 0;
			}
			## }}}

			# If they both passed, merge the tool(s)
			if ($passing and $last_passing) {
				## {{{
				if ($last_tool =~ /$tool/) {
					## Don't change the tool report line
					## Same tool, both good statuses ...
				} else {
					## Add to the tool list
					$TOOL{$test} = "$last_tool, $tool";
				}

				if ($status =~ /cover/i
						or $last_stat =~ /cover/i) {
					# Once covered and passing, always covered
					$status = "Covered";
				}
				## }}}
			} else {
				## Always report the last failing tool, or the
				## first passing tool
				$TOOL{$test} = "$tool";
			}

			$STAT{$test} = $status;
		} else {
			$STAT{$test} = $status;
			$TOOL{$test} = $tool;
		}

		$TSTAMP{$test} = $tstamp;
	}
}
## }}}

printf("Last timestamp: $last_tstamp\n");

close REPORT;

foreach $key (sort (keys %STAT)) {
	printf("%-15s %12s $TSTAMP{$key} -- $TOOL{$key}\n", $key, $STAT{$key});
}

open(HTML, "> $htmlfil");
print HTML "<HTML><HEAD><TITLE>Simulation report</TITLE></HEAD><BODY>\n";
print HTML "<H1 align=center>ZipCPU Simulation Report</H1>\n";
print HTML "<P align=center><TABLE border>\n";
print HTML "<TR><TH>Test</TH><TH>Status</TH><TH>Sim Timestamp</TH><TH>Tool</TH></TR>\n";
foreach $key (sort (keys %STAT)) {
	my $lin, $st;

	$st = $STAT{$key};
	$scr = $SCRIPT{$key};
	$clr="white";
	if ($st =~ /fail/i) {
		$clr="#ffa4a";
	} elsif ($st =~ /err/i) {
		$clr="#ffa4a";
	} elsif ($st =~ /warn/i) {
		$clr="#ffffca";
	} elsif ($st =~ /out-of-date/i) {
		$clr="#ffffca";
	} elsif ($st =~ /pass/i) {
		$clr="#caeec8";
	}
	$lin = sprintf("<TR><TH><A HREF=\"%s\">%s</A></TH>"
		. "<TD bgcolor=$clr><A HREF=\"%s\">%s</A></TD>"
		. "<TD>$TSTAMP{$key}</TD>"
		. "<TD>$TOOL{$key}</TD></TR>\n",
		$SCRIPT{$key}, $key,
		"test/" . $key . ".txt", $st);
	print HTML $lin;
}
print HTML "</TABLE></P></BODY></HTML>\n";
close HTML;
