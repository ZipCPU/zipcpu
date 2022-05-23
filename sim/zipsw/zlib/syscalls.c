////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sim/zipsw/zlib/syscalls.c
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2022, Gisselquist Technology, LLC
// {{{
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of the GNU General Public License as published
// by the Free Software Foundation, either version 3 of the License, or (at
// your option) any later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
//
// You should have received a copy of the GNU General Public License along
// with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
// target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
// }}}
// License:	GPL, v3, as defined and found on www.gnu.org,
// {{{
//		http://www.gnu.org/licenses/gpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
// }}}
#include <sys/errno.h>
#include <stdint.h>
#include <sys/unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/times.h>
#include <reent.h>
#include <stdio.h>
#include "board.h"
#include "bootloader.h"
#include "zipcpu.h"

#define	UARTRX	_uart->u_rx
#define	UARTTX	_uart->u_tx

// #define	TXBUSY	((_uart->u_fifo & 0x010000)==0)
// #define	TXBUSY	((UARTTX & 0x0100)!=0)
#define	TXBUSY	0

void
_outbyte(char v) {
	if (v == '\n') {
		// Depend upon the WBUART, not the PIC
		while(TXBUSY)
			;
		UARTTX = (unsigned)'\r';
	}

	// Depend upon the WBUART, not the PIC
	while(TXBUSY)
		;
	uint8_t c = v;
	UARTTX = (unsigned)c;
}

void
_outbytes(int nbytes, const char *buf) {
#ifdef	FIFO_ENABLED
	// {{{
	const	uint8_t	*ptr = buf;
	int	fifosz;

	// Get the size of the FIFO
	fifosz = _uart->u_fifo >> 28;
	fifosz = 1<<fifosz;

	for(int i=0; i<nbytes;) {
		int	available, ufifo;
		unsigned v;

		// Check how many positions of the FIFO are available
		while(((ufifo = _uart->u_fifo) & 0x010000)==0)
			;
		available = ufifo >> 18;
		available &= (fifosz-1);

		// Don't check availability again: for each available
		// position, simply output the desired character while
		// doing LF -> CR/LF translation
		for(int k=0; (k<available) && (i < nbytes); k++, i++) {
			v = *ptr++;

			// Output the desired character
			UARTTX = v;
			if (v == '\n') {
				if (--available == 0) {
					// Special case: What if we just
					// used the last item in the FIFO?
					// poll for the next available spot
					while((_uart->u_fifo & 0x010000)==0)
						;
				} UARTTX = '\r';
			}
		}
	}
	// }}}
#else
	const	uint8_t	*ptr = buf;

	for(int i=0; i<nbytes; i++)
		_outbyte(*ptr++);
#endif
}

int
_inbyte(void) {
#ifdef	UARTRX
	// {{{
	const	int	echo = 1, cr_into_nl = 1;
	static	int	last_was_cr = 0;
	int	rv;

	// Character translations:
	// 1. All characters should be echoed
	// 2. \r's should quietly be turned into \n's
	// 3. \r\n's should quietly be turned into \n's
	// 4. \n's should be passed as is
	// Insist on at least one character
	rv = UARTRX;
	if (rv & 0x0100)
		rv = -1;
	else if ((cr_into_nl)&&(rv == '\r')) {
		rv = '\n';
		last_was_cr = 1;
	} else if ((cr_into_nl)&&(rv == '\n')) {
		if (last_was_cr) {
			rv = -1;
			last_was_cr = 0;
		}
	} else
		last_was_cr = 0;

	if ((rv != -1)&&(echo))
		_outbyte(rv);
	return rv;
	// }}}
#else
	return -1;
#endif
}

int
_close_r(struct _reent *reent, int file) {
	reent->_errno = EBADF;

	return -1;	/* Always fails */
}

char	*__env[1] = { 0 };
char	**environ = __env;

int
_execve_r(struct _reent *reent, const char *name, char * const *argv, char * const *env)
{
	reent->_errno = ENOSYS;
	return -1;
}

int
_fork_r(struct _reent *reent)
{
	reent->_errno = ENOSYS;
	return -1;
}

int
_fstat_r(struct _reent *reent, int file, struct stat *st)
{
	if ((STDOUT_FILENO == file)||(STDERR_FILENO == file)
		||(STDIN_FILENO == file)) {
		st->st_mode = S_IFCHR;
		return 0;
#ifdef	_ZIP_HAS_SDCARD_NOTYET
	} else if (SDCARD_FILENO == file) {
		st->st_mode = S_IFBLK;
#endif
	} else {
		reent->_errno = EBADF;
		return -1;
	}
}

int
_getpid_r(struct _reent *reent)
{
	return 1;
}

int
_gettimeofday_r(struct _reent *reent, struct timeval *ptimeval, void *ptimezone)
{
	reent->_errno = ENOSYS;
	return -1;
}

int
_isatty_r(struct _reent *reent, int file)
{
	if ((STDIN_FILENO == file)
			||(STDOUT_FILENO == file)
			||(STDERR_FILENO==file))
		return 1;
	return 0;
}

int
_kill_r(struct _reent *reent, int pid, int sig)
{
	reent->_errno = ENOSYS;
	return -1;
}

int
_link_r(struct _reent *reent, const char *existing, const char *new)
{
	reent->_errno = ENOSYS;
	return -1;
}

_off_t
_lseek_r(struct _reent *reent, int file, _off_t ptr, int dir)
{
#ifdef	_ZIP_HAS_SDCARD_NOTYET
	if (SDCARD_FILENO == file) {
		switch(dir) {
		case SEEK_SET:	rootfs_offset = ptr;
		case SEEK_CUR:	rootfs_offset += ptr;
		case SEEK_END:	rootfs_offset = rootfs->nsectors * rootfs->sectorsize - ptr;
		default:
			reent->_errno = EINVAL; return -1;
		} return rootfs_offset;
	}
#endif
	reent->_errno = ENOSYS;
	return -1;
}

int
_open_r(struct _reent *reent, const char *file, int flags, int mode)
{
#ifdef	_ZIP_HAS_SDCARD_NOTYET
	if (strcmp(file, "/dev/sdcard")==0) {
		return SDCARD_FILENO;
	} else {
		reent->_errno = EACCES;
		return -1;
	}
#endif
	reent->_errno = ENOSYS;
	return -1;
}

int
_read_r(struct _reent *reent, int file, void *ptr, size_t len)
{
#ifdef	UARTRX
	if (STDIN_FILENO == file)
	{
		int	nr = 0, rv;
		char	*chp = ptr;

		while((rv=_inbyte()) &0x0100)
			;
		*chp++ = (char)rv;
		nr++;

		// Now read out anything left in the FIFO
		while((nr < len)&&(((rv=_inbyte()) & 0x0100)==0)) {
			*chp++ = (char)rv;
			nr++;
		}

		// if (rv & 0x01000) _uartrx = 0x01000;
		return nr;
	}
#endif
#ifdef	_ZIP_HAS_SDCARD_NOTYET
	if (SDCARD_FILENO == file)
	{
	}
#endif
	errno = ENOSYS;
	return -1;
}

int
_readlink_r(struct _reent *reent, const char *path, char *buf, size_t bufsize)
{
	reent->_errno = ENOSYS;
	return -1;
}

int
_stat_r(struct _reent *reent, const char *path, struct stat *buf) {
	reent->_errno = EIO;
	return -1;
}

int
_unlink_r(struct _reent *reent, const char *path)
{
	reent->_errno = EIO;
	return -1;
}

int
_times(struct tms *buf) {
	errno = EACCES;
	return -1;
}

int
_write_r(struct _reent * reent, int fd, const void *buf, size_t nbytes) {
	if ((STDOUT_FILENO == fd)||(STDERR_FILENO == fd)) {
		/*
		const	char *cbuf = buf;
		for(int i=0; i<nbytes; i++)
			_outbyte(cbuf[i]);
		*/
		_outbytes(nbytes, buf);
		return nbytes;
	}
#ifdef	_ZIP_HAS_SDCARD_NOTYET
	if (SDCARD_FILENO == file)
	{
	}
#endif

	reent->_errno = EBADF;
	return -1;
}

int
_wait(int *status) {
	errno = ECHILD;
	return -1;
}

int	*heap = _top_of_heap;

void *
_sbrk_r(struct _reent *reent, int sz) {
	int	*prev = heap;

	heap += sz;
	return	prev;
}

__attribute__((__noreturn__))
void	_exit(int rcode) {
	extern void	_hw_shutdown(int rcode) _ATTRIBUTE((__noreturn__));

	// Problem: Once u_tx & 0x100 goes low, there may still be a character
	// or two in the bus console's pipeline.  These may prevent a newline
	// from completing before we issue the exit command.
	//
	// Solution: Just to make sure any newline finishes, send a final
	// non-newline character.  This character will still be transmitting
	// once we are complete, but any last newline will at least have been
	// received
	_outbyte(' ');
	_outbyte(' ');

	// Wait for any serial ports to flush their buffers
	while(TXBUSY)
		;
	_hw_shutdown(rcode);
}
