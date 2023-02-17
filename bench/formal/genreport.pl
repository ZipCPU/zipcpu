#!/usr/bin/perl

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
	} elsif ($terminated) {
		"Terminated";
	} elsif ($FAIL) {
		"FAIL";
	} elsif ($ERR) {
		"ERROR";
	} elsif (($ind == 0 || $UNK != 0) && $bmc > 0) {
		"BMC $bmc";
	} else {
		"Unknown";
	}
}

print <<"EOM";
<HTML><HEAD><TITLE>Formal Verification Report</TITLE></HEAD>
<BODY>
<TABLE border>
<TR><TH>Status</TH><TH>Component</TD><TH>Proof</TH></TR>
EOM

opendir(DIR, $dir) or die "Cannot open directory for reading";
my @dirent = readdir(DIR);
closedir(DIR);

# print "@dirent";

foreach $prf (sort @proofs) {
	foreach $dent (@dirent) {
		# print("<TR><TD>DIR $dent</TD></TR>\n");
		# Only look at subdirectories
		next if (! -d $dent);
		next if ($dent =~ /^\./);
		next if ($dent !~ /$prf(_\S+)/);
			$subprf = $1;
		# print("<TR><TD>$dent matches $prf</TD></TR>\n");
		$st = getstatus($dent);
		# print("<TR><TD>STATUS = $st</TD></TR>\n");
		my $tail = "</TD><TD>$prf</TD><TD>$subprf</TD></TR>\n";
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
	}
}

print <<"EOM";
</TABLE>
</BODY></HTML>
EOM



