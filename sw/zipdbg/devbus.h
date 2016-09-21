////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	devbus.h
//
// Project:	UART to WISHBONE FPGA library
//
// Purpose:	The purpose of this file is to document an interface which
//		any device with a bus, whether it be implemented over a UART,
//	an ethernet, or a PCI express bus, must implement.  This describes
//	only an interface, and not how that interface is to be accomplished.
//
//	The neat part of this interface is that, if programs are designed to
//	work with it, than the implementation details may be changed later
//	and any program that once worked with the interface should be able
//	to continue to do so.  (i.e., switch from a UART controlled bus to a
//	PCI express controlled bus, with minimal change to the software of
//	interest.)
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2016, Gisselquist Technology, LLC
//
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of  the GNU General Public License as published
// by the Free Software Foundation, either version 3 of the License, or (at
// your option) any later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
#ifndef	DEVBUS_H
#define	DEVBUS_H

#include <unistd.h>

typedef	unsigned int	uint32;

class	BUSERR {
public:
	uint32 addr;
	BUSERR(const uint32 a) : addr(a) {};
};

class	DEVBUS {
public:
	typedef	uint32	BUSW;

	virtual	void	kill(void) = 0;
	virtual	void	close(void) = 0;

	// Write a single value to a single address
	//	a is the address of the value to be read as it exists on the
	//		wishbone bus within the FPGA.
	//	v is the singular value to write to this address
	virtual	void	writeio(const BUSW a, const BUSW v) = 0;

	// Read a single value to a single address
	//	a is the address of the value to be read as it exists on the
	//		wishbone bus within the FPGA.
	//	This function returns the value read from the device wishbone
	//		at address a.
	virtual	BUSW	readio(const BUSW a) = 0;

	// Read a series of values from values from a block of memory
	//	a is the address of the value to be read as it exists on the
	//		wishbone bus within the FPGA.
	//	len is the number of words to read
	//	buf is a pointer to a place to store the words once read.
	// This is equivalent to:
	//	for(int i=0; i<len; i++)
	//		buf[i] = readio(a+i);
	// only it's faster in our implementation.
	virtual	void	readi(const BUSW a, const int len, BUSW *buf) = 0;

	// Read a series of values from the same address in memory.  This 
	// call is identical to readi, save that the address is not incremented
	// from one read to the next.  It is equivalent to:
	//	for(int i=0; i<len; i++)
	//		buf[i] = readio(a);
	// only it's faster in our implementation.
	//
	virtual	void	readz(const BUSW a, const int len, BUSW *buf) = 0;

	// Write a series of values into a block of memory on the FPGA
	//	a is the address of the value to be written as it exists on the
	//		wishbone bus within the FPGA.
	//	len is the number of words to write
	//	buf is a pointer to a place to from whence to grab the data
	//		to be written.
	// This is equivalent to:
	//	for(int i=0; i<len; i++)
	//		writeio(a+i, buf[i]);
	// only it's faster in our implementation.
	virtual	void	writei(const BUSW a, const int len, const BUSW *buf) = 0;
	// Write a series of values into the same address on the FPGA bus.  This
	// call is identical to writei, save that the address is not incremented
	// from one write to the next.  It is equivalent to:
	//	for(int i=0; i<len; i++)
	//		writeio(a, buf[i]);
	// only it's faster in our implementation.
	//
	virtual	void	writez(const BUSW a, const int len, const BUSW *buf) = 0;

	// Query whether or not an interrupt has taken place
	virtual	bool	poll(void) = 0;

	// Sleep until interrupt, but sleep no longer than msec milliseconds
	virtual	void	usleep(unsigned msec) = 0;

	// Sleep until an interrupt, no matter how long it takes for that
	// interrupt to take place
	virtual	void	wait(void) = 0;

	// Query whether or not a bus error has taken place.  This is somewhat
	// of a misnomer, as my current bus error detection code exits any
	// interface, but ... it is what it is.
	virtual	bool	bus_err(void) const = 0;

	// Clear any bus error condition.
	virtual	void	reset_err(void) = 0;

	// Clear any interrupt condition that has already been noticed by
	// the interface, does not check for further interrupt
	virtual	void	clear(void) = 0;

	virtual	~DEVBUS(void) { };
};

#endif
