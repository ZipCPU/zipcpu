#!/bin/perl

## Configuration definitions
## {{{
my $asmconfig =" -chparam OPT_PIPELINED    0"
	. " -chparam OPT_LGDCACHE	0"
	. " -chparam OPT_LGICACHE	0"
	. " -chparam OPT_MPY	0"
	. " -chparam OPT_DIV	0"
	. " -chparam OPT_SHIFTS	0"
	. " -chparam OPT_LOCK	0"
	. " -chparam OPT_EARLY_BRANCHING	0"
	. " -chparam OPT_LOWPOWER	0"
	. " -chparam OPT_DISTRIBUTED_REGS	0"
	. " -chparam OPT_USERMODE	0"
	. " -chparam OPT_CLKGATE	0"
	. " -chparam OPT_DBGPORT	0"
	. " -chparam OPT_TRACE_PORT	0"
	. " -chparam OPT_CIS	0 ";
$asmconfig = $asmconfig . " -chparam ADDRESS_WIDTH 23";

my $trapconfig =" -chparam OPT_PIPELINED    0"
	. " -chparam OPT_LGDCACHE	0"
	. " -chparam OPT_LGICACHE	0"
	. " -chparam OPT_MPY	0"
	. " -chparam OPT_DIV	0"
	. " -chparam OPT_SHIFTS	1"
	. " -chparam OPT_LOCK	1"
	. " -chparam OPT_EARLY_BRANCHING	0"
	. " -chparam OPT_LOWPOWER	0"
	. " -chparam OPT_DISTRIBUTED_REGS	0"
	. " -chparam OPT_USERMODE	1"
	. " -chparam OPT_CLKGATE	0"
	. " -chparam OPT_DBGPORT	0"
	. " -chparam OPT_TRACE_PORT	0"
	. " -chparam OPT_CIS	0 ";
$trapconfig = $trapconfig . " -chparam ADDRESS_WIDTH 23";

my $minconfig =" -chparam OPT_PIPELINED    0"
	. " -chparam OPT_LGDCACHE	0"
	. " -chparam OPT_LGICACHE	0"
	. " -chparam OPT_MPY	6"
	. " -chparam OPT_DIV	1"
	. " -chparam OPT_SHIFTS	1"
	. " -chparam OPT_LOCK	1"
	. " -chparam OPT_EARLY_BRANCHING	0"
	. " -chparam OPT_LOWPOWER	0"
	. " -chparam OPT_DISTRIBUTED_REGS	0"
	. " -chparam OPT_USERMODE	1"
	. " -chparam OPT_CLKGATE	0"
	. " -chparam OPT_DBGPORT	1"
	. " -chparam OPT_TRACE_PORT	0"
	. " -chparam OPT_CIS	1 ";
$minconfig = $minconfig . " -chparam ADDRESS_WIDTH 23";

my $pipeconfig =" -chparam OPT_PIPELINED    1"
	. " -chparam OPT_LGDCACHE	2"
	. " -chparam OPT_LGICACHE	2"
	. " -chparam OPT_MPY	6"
	. " -chparam OPT_DIV	1"
	. " -chparam OPT_SHIFTS	1"
	. " -chparam OPT_LOCK	1"
	. " -chparam OPT_EARLY_BRANCHING	1"
	. " -chparam OPT_LOWPOWER	0"
	. " -chparam OPT_DISTRIBUTED_REGS	0"
	. " -chparam OPT_USERMODE	1"
	. " -chparam OPT_CLKGATE	0"
	. " -chparam OPT_DBGPORT	1"
	. " -chparam OPT_TRACE_PORT	0"
	. " -chparam OPT_CIS	1 ";

my $cacheconfig =" -chparam OPT_PIPELINED    1"
	. " -chparam OPT_LGDCACHE	12"
	. " -chparam OPT_LGICACHE	12"
	. " -chparam OPT_MPY	6"
	. " -chparam OPT_DIV	1"
	. " -chparam OPT_SHIFTS	1"
	. " -chparam OPT_LOCK	1"
	. " -chparam OPT_EARLY_BRANCHING	1"
	. " -chparam OPT_LOWPOWER	0"
	. " -chparam OPT_DISTRIBUTED_REGS	0"
	. " -chparam OPT_USERMODE	1"
	. " -chparam OPT_CLKGATE	0"
	. " -chparam OPT_DBGPORT	1"
	. " -chparam OPT_TRACE_PORT	0"
	. " -chparam OPT_CIS	1 ";

my $lowpowercfg =" -chparam OPT_PIPELINED    1"
	. " -chparam OPT_LGDCACHE	12"
	. " -chparam OPT_LGICACHE	12"
	. " -chparam OPT_MPY	6"
	. " -chparam OPT_DIV	1"
	. " -chparam OPT_SHIFTS	1"
	. " -chparam OPT_LOCK	1"
	. " -chparam OPT_EARLY_BRANCHING	1"
	. " -chparam OPT_LOWPOWER	1"
	. " -chparam OPT_DISTRIBUTED_REGS	0"
	. " -chparam OPT_USERMODE	1"
	. " -chparam OPT_CLKGATE	1"
	. " -chparam OPT_DBGPORT	1"
	. " -chparam OPT_TRACE_PORT	0"
	. " -chparam OPT_CIS	1 ";

my $bonescfg = "";
my $syscfg   = " -chparam OPT_DMA 1 -chparam DMA_LGMEM 10 -chparam OPT_ACCOUNTING 1";
my $axilcfg  = "";
my $axicfg   = "";
## }}}

## Files
## {{{
my @files = (
	## Core ZiPCPU files
	## {{{
	"core/zipcore.v",
	"core/idecode.v", "core/iscachable.v",
	"core/cpuops.v", "core/mpyop.v", "core/slowmpy.v",
	"core/div.v",
	  ## WB memory cores
	"core/zipwb.v",
	"core/prefetch.v", "core/dblfetch.v", "core/pfcache.v",
	"core/memops.v", "core/pipemem.v", "core/dcache.v",
	  ## AXI-lite memory cores
	"core/axilfetch.v",
	"core/axilops.v", "core/axilpipe.v",
	  ## AXI4(full) memory cores
	"core/axiicache.v",
	"core/axiops.v", "core/axipipe.v", "core/axidcache.v",
	## }}}
	## Extras
	## {{{
	  ## Wishbone
	"ex/wbpriarbiter.v", "ex/wbdblpriarb.v",
	  "ex/busdelay.v", "ex/wbarbiter.v",
	  ## AXI
	"ex/skidbuffer.v", "ex/sfifo.v",
	## }}}
	## Peripherals
	## {{{
	"peripherals/ziptimer.v", "peripherals/wbdmac.v",
	"peripherals/icontrol.v", "peripherals/zipcounter.v",
	"peripherals/wbwatchdog.v",
	"peripherals/zipjiffies.v",
	# "peripherals/zipmmu.v",
	## }}}
	## Wrappers
	"zipbones.v", "zipsystem.v",
	"zipaxil.v", "zipaxi.v");
## }}}

my $logfile = "yosys.log";
my $scriptf = "usage.ys";
my $ice40synth = "synth_ice40";
my $xilinxsynth = "synth_xilinx";

sub	calcusage($$$) {
	## {{{
	my($synth,$toplvl,$config)=@_;

	## Build the script
	## {{{
	unlink($scriptf);
	open(SCRIPT, "> $scriptf");
	foreach $key (@files) {
		print SCRIPT "read -sv $key\n";
	}

	print SCRIPT "hierarchy -top $toplvl $config\n";
	print SCRIPT "$synth -flatten -top $toplvl\n";
	print SCRIPT "stat\n";
	close(SCRIPT);
	## }}}
	
	system("yosys -l $logfile -s $scriptf");

	## Read the log, looking for the usage statistics
	## {{{
	$usage = 0;
	open(LOG, "< $logfile");
	while($line = <LOG>) {
		if ($line =~ /Estimated number of LCs:\s*(\d+)\s*$/) {
			$usage = $1;
		} elsif ($line =~ /^\s*SB_LUT4\s*(\d+)\s*$/) {
			$usage = $1;
		}
	} close(LOG);
	## }}}

	$usage
}
## }}}

sub	topusage($$) {
	## {{{
	my($name,$toplvl)=@_;
	my $result = "";

	$result = sprintf("$name ASM:   %5d %5d\n",
		calcusage($ice40synth, $toplvl, $asmconfig),
		calcusage($xilinxsynth, $toplvl, $asmconfig));

	$result = $result . sprintf("$name TRAP:  %5d %5d\n",
		calcusage($ice40synth, $toplvl, $trapconfig),
		calcusage($xilinxsynth, $toplvl, $trapconfig));

	$result = $result . sprintf("$name MIN:   %5d %5d\n",
		calcusage($ice40synth, $toplvl, $minconfig),
		calcusage($xilinxsynth, $toplvl, $minconfig));

	$result = $result . sprintf("$name PIPE:  %5d %5d\n",
		calcusage($ice40synth, $toplvl, $pipeconfig),
		calcusage($xilinxsynth, $toplvl, $pipeconfig));

	if ($toplvl ne "zipaxil") {
		$result = $result . sprintf("$name CACHE: %5d %5d\n",
			calcusage($ice40synth, $toplvl, $cacheconfig),
			calcusage($xilinxsynth, $toplvl, $cacheconfig));

		$result = $result . sprintf("$name LWPWR: %5d %5d\n",
			calcusage($ice40synth, $toplvl, $lowpowercfg),
			calcusage($xilinxsynth, $toplvl, $lowpowercfg));
	}

	$result
}
## }}}

$result = "";
$result = topusage("ZipBones ", "zipbones");
$result = $result . topusage("ZipSystem", "zipsystem");
$result = $result . topusage("ZipAXI-L ", "zipaxil");
$result = $result . topusage("ZipAXI   ", "zipaxi");

## Add a header
$result = "                 iCE40  X7-s\n"
	. "Wrapper   Config  4LUT  6LUT\n"
	. "----------------------------\n" . $result;
print $result;

open(USAGE, "> usage.txt");

print USAGE $result;
close(USAGE);
