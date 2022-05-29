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

my $cacheconfig =" -chparam OPT_PIPELINED 1"
	. " -chparam OPT_LGDCACHE	 12"
	. " -chparam OPT_LGICACHE	 12"
	. " -chparam OPT_MPY		  6"
	. " -chparam OPT_DIV		  1"
	. " -chparam OPT_SHIFTS		  1"
	. " -chparam OPT_LOCK		  1"
	. " -chparam OPT_EARLY_BRANCHING  1"
	. " -chparam OPT_LOWPOWER	  0"
	. " -chparam OPT_DISTRIBUTED_REGS 1"
	. " -chparam OPT_USERMODE	  1"
	. " -chparam OPT_CLKGATE	  0"
	. " -chparam OPT_DBGPORT	  1"
	. " -chparam OPT_TRACE_PORT	  0"
	. " -chparam OPT_CIS		  1";

my $lowpowercfg =" -chparam OPT_PIPELINED 1"
	. " -chparam OPT_LGDCACHE	 12"
	. " -chparam OPT_LGICACHE	 12"
	. " -chparam OPT_MPY		  6"
	. " -chparam OPT_DIV		  1"
	. " -chparam OPT_SHIFTS		  1"
	. " -chparam OPT_LOCK		  1"
	. " -chparam OPT_EARLY_BRANCHING  1"
	. " -chparam OPT_LOWPOWER	  1"
	. " -chparam OPT_DISTRIBUTED_REGS 1"
	. " -chparam OPT_USERMODE	  1"
	. " -chparam OPT_CLKGATE	  1"
	. " -chparam OPT_DBGPORT	  1"
	. " -chparam OPT_TRACE_PORT	  0"
	. " -chparam OPT_CIS		  1";

## Memory configurations
## {{{
my $wbmemopsconfig = " -chparam ADDRESS_WIDTH   30"
		. " -chparam OPT_LOCK            1"
		. " -chparam OPT_ALIGNMENT_ERR   1"
		. " -chparam OPT_LOWPOWER        0";

my $wbpipememconfig = " -chparam ADDRESS_WIDTH  30"
		. " -chparam OPT_LOCK            1"
		. " -chparam OPT_ALIGNMENT_ERR   1";

my $wbdcacheconfig = " -chparam ADDRESS_WIDTH   30"
		. " -chparam LGCACHELEN		10"
		. " -chparam LGNLINES		 7"
		. " -chparam OPT_PIPE            1"
		. " -chparam OPT_LOWPOWER        0";

my $axilopsconfig=" -chparam C_AXI_DATA_WIDTH 32"
		. " -chparam C_AXI_ADDR_WIDTH   30"
		. " -chparam SWAP_WSTRB          1"
		. " -chparam OPT_ALIGNMENT_ERR	 1"
		. " -chparam OPT_LOWPOWER        0";

my $axiopsconfig =" -chparam C_AXI_DATA_WIDTH 32"
		. " -chparam C_AXI_ADDR_WIDTH   30"
		. " -chparam AXI_ID              0"
		. " -chparam SWAP_WSTRB          1"
		. " -chparam OPT_LOCK		 1"
		. " -chparam OPT_ALIGNMENT_ERR	 1"
		. " -chparam OPT_LOWPOWER        0";

my $axilpipeconfig=" -chparam C_AXI_DATA_WIDTH 32"
		. " -chparam C_AXI_ADDR_WIDTH   30"
		. " -chparam SWAP_WSTRB          1"
		. " -chparam OPT_ALIGNMENT_ERR	 1"
		. " -chparam OPT_LOWPOWER        0";

my $axipipeconfig =" -chparam C_AXI_DATA_WIDTH 32"
		. " -chparam C_AXI_ADDR_WIDTH   30"
		. " -chparam AXI_ID              0"
		. " -chparam SWAP_WSTRB          1"
		. " -chparam OPT_LOCK		 1"
		. " -chparam OPT_ALIGNMENT_ERR	 1"
		. " -chparam OPT_LOWPOWER        0";

my $axdcacheconfig =" -chparam C_AXI_DATA_WIDTH 32"
		. " -chparam C_AXI_ADDR_WIDTH   30"
		. " -chparam AXI_ID              0"
		. " -chparam OPT_WRAP            1"
		. " -chparam LGCACHELEN		12"
		. " -chparam LGNLINES		 7"
		. " -chparam SWAP_WSTRB          1"
		. " -chparam OPT_PIPE            1"
		. " -chparam OPT_LOWPOWER        0";
## }}}

my $wbdmaconfig = " -chparam ADDRESS_WIDTH 30"
		. " -chparam LGMEMLEN      32"
		. " -chparam DW            32";

## Instruction fetch configs
## {{{
my $wbprefetchconfig = " -chparam ADDRESS_WIDTH   30"
		. " -chparam DATA_WIDTH           32"
		. " -chparam INSN_WIDTH           32"
		. " -chparam OPT_LITTLE_ENDIAN     0";

my $wbdblfetchconfig = " -chparam ADDRESS_WIDTH   30"
		. " -chparam DATA_WIDTH           32"
		. " -chparam INSN_WIDTH           32"
		. " -chparam OPT_LITTLE_ENDIAN     0";

my $wbpfcacheconfig = " -chparam ADDRESS_WIDTH   30"
		. " -chparam LGCACHELEN          10"
		. " -chparam LGLINES              7";

my $axpfsimpleconfig =" -chparam C_AXI_DATA_WIDTH 32"
		. " -chparam C_AXI_ADDR_WIDTH    30"
		. " -chparam INSN_WIDTH		 32"
		. " -chparam FETCH_LIMIT	  1";

my $axpfdblconfig =" -chparam C_AXI_DATA_WIDTH 32"
		. " -chparam C_AXI_ADDR_WIDTH    30"
		. " -chparam INSN_WIDTH		 32"
		. " -chparam FETCH_LIMIT	  2";

my $axpfcacheconfig =" -chparam C_AXI_DATA_WIDTH 32"
		. " -chparam C_AXI_ADDR_WIDTH    30"
		. " -chparam AXI_ID               0"
		. " -chparam OPT_WRAP             1"
		. " -chparam LGCACHESZ		 12"
		. " -chparam LGLINESZ		  3"
		. " -chparam OPT_LOWPOWER         0";
## }}}

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
my $asicsynth   = "synth";
my $asicpost    = "abc -g cmos2";

sub	calcusage($$$$) {
	## {{{
	my($synth,$toplvl,$config,$postsynth)=@_;

	## Build the script
	## {{{
	unlink($scriptf);
	open(SCRIPT, "> $scriptf");
	foreach $key (@files) {
		print SCRIPT "read -sv $key\n";
	}

	if ($synth eq $ice40synth and $config =~ /OPT_DISTRIBUTED_REGS/) {
		$lclconfig = $config;
		$lclconfig =~ s/OPT_DISTRIBUTED_REGS\s+\d+/OPT_DISTRIBUTED_REGS 0/g;
		print SCRIPT "hierarchy -top $toplvl $lclconfig\n";
	} else {
		print SCRIPT "hierarchy -top $toplvl $config\n";
	}
	print SCRIPT "$synth -flatten -top $toplvl\n";
	if ($postsynth ne "") {
		print SCRIPT "$postsynth\n";
	}
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
		} elsif ($line =~ /^\s*\$_NAND_\s*(\d+)\s*$/) {
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

	$result = sprintf("$name ASM:   %5d %5d %6d\n",
		calcusage($ice40synth, $toplvl, $asmconfig,""),
		calcusage($xilinxsynth,$toplvl, $asmconfig,""),
		calcusage($asicsynth,  $toplvl, $asmconfig,$asicpost));

	$result = $result . sprintf("$name TRAP:  %5d %5d %6d\n",
		calcusage($ice40synth, $toplvl, $trapconfig,""),
		calcusage($xilinxsynth,$toplvl, $trapconfig,""),
		calcusage($asicsynth,  $toplvl, $trapconfig,$asicpost));

	$result = $result . sprintf("$name MIN:   %5d %5d %6d\n",
		calcusage($ice40synth, $toplvl, $minconfig,""),
		calcusage($xilinxsynth,$toplvl, $minconfig,""),
		calcusage($asicsynth,  $toplvl, $minconfig,$asicpost));

	$result = $result . sprintf("$name PIPE:  %5d %5d %6d\n",
		calcusage($ice40synth, $toplvl, $pipeconfig,""),
		calcusage($xilinxsynth,$toplvl, $pipeconfig,""),
		calcusage($asicsynth,  $toplvl, $pipeconfig,$asicpost));

	if ($toplvl ne "zipaxil") {
		$result = $result . sprintf("$name CACHE: %5d %5d %6d\n",
			calcusage($ice40synth, $toplvl, $cacheconfig,""),
			calcusage($xilinxsynth,$toplvl, $cacheconfig,""),
			calcusage($asicsynth,  $toplvl, $cacheconfig,$asicpost));

		$result = $result . sprintf("$name LWPWR: %5d %5d %6d\n",
			calcusage($ice40synth, $toplvl, $lowpowercfg,""),
			calcusage($xilinxsynth,$toplvl, $lowpowercfg,""),
			calcusage($asicsynth,  $toplvl, $lowpowercfg,$asicpost));
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
$result = "                 iCE40  X7-s   RAW\n"
	. "Wrapper   Config  4LUT  6LUT  NANDs\n"
	. "-----------------------------------\n" . $result;
print $result;

open(USAGE, "> usage.txt");

print USAGE $result;

$dcch = sprintf("   WB-MEMOPS   : %5d %5d %6d\n",
		calcusage($ice40synth, "memops", $wbmemopsconfig,""),
		calcusage($xilinxsynth,"memops", $wbmemopsconfig,""),
		calcusage($asicsynth,  "memops", $wbmemopsconfig,$asicpost));

$dcch = $dcch . sprintf("   WB-PIPEMEM  : %5d %5d %6d\n",
		calcusage($ice40synth, "pipemem", $wbpipememconfig,""),
		calcusage($xilinxsynth,"pipemem", $wbpipememconfig,""),
		calcusage($asicsynth,  "pipemem", $wbpipememconfig,$asicpost));

$dcch = $dcch . sprintf("   WB-DCACHE   : %5d %5d %6d\n",
		calcusage($ice40synth, "dcache", $wbdcacheconfig,""),
		calcusage($xilinxsynth,"dcache", $wbdcacheconfig,""),
		calcusage($asicsynth,  "dcache", $wbdcacheconfig,$asicpost));

$dcch = $dcch . sprintf(" AXIL-OPS      : %5d %5d %6d\n",
		calcusage($ice40synth, "axilops", $axilopsconfig,""),
		calcusage($xilinxsynth,"axilops", $axilopsconfig,""),
		calcusage($asicsynth,  "axilops", $axilopsconfig,$asicpost));

$dcch = $dcch . sprintf("  AXI-OPS      : %5d %5d %6d\n",
		calcusage($ice40synth, "axiops", $axiopsconfig,""),
		calcusage($xilinxsynth,"axiops", $axiopsconfig,""),
		calcusage($asicsynth,  "axiops", $axiopsconfig,$asicpost));

$dcch = $dcch . sprintf(" AXIL-PIPE     : %5d %5d %6d\n",
		calcusage($ice40synth, "axilpipe", $axilpipeconfig,""),
		calcusage($xilinxsynth,"axilpipe", $axilpipeconfig,""),
		calcusage($asicsynth,  "axilpipe", $axilpipeconfig,$asicpost));

$dcch = $dcch . sprintf("  AXI-PIPE     : %5d %5d %6d\n",
		calcusage($ice40synth, "axipipe", $axipipeconfig,""),
		calcusage($xilinxsynth,"axipipe", $axipipeconfig,""),
		calcusage($asicsynth,  "axipipe", $axipipeconfig,$asicpost));

$dcch = $dcch . sprintf("  AXI-DCACHE   : %5d %5d %6d\n",
		calcusage($ice40synth, "axidcache", $axdcacheconfig,""),
		calcusage($xilinxsynth,"axidcache", $axdcacheconfig,""),
		calcusage($asicsynth,  "axidcache", $axdcacheconfig,$asicpost));

$dcch = $dcch . sprintf("   WB-DMA      : %5d %5d %6d\n",
		calcusage($ice40synth, "wbdmac", $wbdmaconfig,""),
		calcusage($xilinxsynth,"wbdmac", $wbdmaconfig,""),
		calcusage($asicsynth,  "wbdmac", $wbdmaconfig,$asicpost));

$icch = sprintf("   WB-PREFETCH : %5d %5d %6d\n",
		calcusage($ice40synth, "prefetch", $wbprefetchconfig,""),
		calcusage($xilinxsynth,"prefetch", $wbprefetchconfig,""),
		calcusage($asicsynth,  "prefetch", $wbprefetchconfig,$asicpost));

$icch = $icch . sprintf("   WB-DBLFETCH : %5d %5d %6d\n",
		calcusage($ice40synth, "dblfetch", $wbdblfetchconfig,""),
		calcusage($xilinxsynth,"dblfetch", $wbdblfetchconfig,""),
		calcusage($asicsynth,  "dblfetch", $wbdblfetchconfig,$asicpost));

$icch = $icch . sprintf("   WB-ICACHE   : %5d %5d %6d\n",
		calcusage($ice40synth, "pfcache", $wbpfcacheconfig,""),
		calcusage($xilinxsynth,"pfcache", $wbpfcacheconfig,""),
		calcusage($asicsynth,  "pfcache", $wbpfcacheconfig,$asicpost));

$icch = $icch . sprintf("  AXILFETCH-BSC: %5d %5d %6d\n",
		calcusage($ice40synth, "axilfetch", $axpfsimpleconfig,""),
		calcusage($xilinxsynth,"axilfetch", $axpfsimpleconfig,""),
		calcusage($asicsynth,  "axilfetch", $axpfsimpleconfig,$asicpost));

$icch = $icch . sprintf("  AXILFETCH-PIP: %5d %5d %6d\n",
		calcusage($ice40synth, "axilfetch", $axpfdblconfig,""),
		calcusage($xilinxsynth,"axilfetch", $axpfdblconfig,""),
		calcusage($asicsynth,  "axilfetch", $axpfdblconfig,$asicpost));

$icch = $icch . sprintf("  AXI-ICACHE   : %5d %5d %6d\n",
		calcusage($ice40synth, "axiicache", $axpfcacheconfig,""),
		calcusage($xilinxsynth,"axiicache", $axpfcacheconfig,""),
		calcusage($asicsynth,  "axiicache", $axpfcacheconfig,$asicpost));

print USAGE $dcch;
print USAGE $icch;

close(USAGE);
