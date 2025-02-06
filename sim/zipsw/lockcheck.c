////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sim/zipsw/lockcheck.c
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	This is a CPU test program designed to test the ZipCPU's LOCK
//		instruction.  NUM_TASKS (=4) tasks are created, each trying
//	to grab and set a shared resource and increment it.  If all goes
//	well, the resource will be owned by the task and unchanged for the
//	duration that the resource is owned by the task.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2021-2025, Gisselquist Technology, LLC
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
#include <stdio.h>
#include <stdlib.h>
#include "txfns.h"
#include "zipcpu.h"
#include "board.h"

const unsigned	NUM_TASKS = 3;

typedef	struct	TASKT_S {
	unsigned volatile *regs;
	unsigned	*stackp;
} TASKT;

volatile char		atomic;
volatile unsigned	shared_resource;

void	user_task(int task_id, int *loops) {
	// const	unsigned	NLOOPS = 1024;
	const	unsigned	NLOOPS = 12;
	unsigned	task_fail = 0;
	*loops = 0;
	while(!task_fail && *loops < NLOOPS) {
		if (!__atomic_test_and_set(&atomic, __ATOMIC_RELAXED)) {
	//		printf("Task #%d:\n", task_id);
			shared_resource = task_id;
			for(int k=0; k<5; k++) {
				// NSTR("K-Loop");
				// if (shared_resource != task_id) LED = RED;
				if (shared_resource != task_id)
					task_fail = 1;
				if (atomic != 1)
					task_fail = 1;
			}

			// NSTR("Increment");
			*loops = *loops + 1;
			printf("Task #%d: %d loops\n", task_id, *loops);
	//		NSTR("Release");
			atomic = 0;
		}
	}

	// Spin and grab the lock
	while (__atomic_test_and_set(&atomic, __ATOMIC_RELAXED)) {}

	printf("Task #%d: COMPLETE%s\n", task_id, (task_fail) ? " -- FAILED!":"");
	atomic = 0;

	if (task_fail)
		*loops = -1;
	zip_syscall();
	while(1)
		txchr('!');
}

// And a main task that steps each task
int	main(int argc,char **argv) {
	TASKT	TASK[NUM_TASKS];
	unsigned	task_loops[NUM_TASKS];
	unsigned	success = 1;

	atomic = 0;
	shared_resource = 0;

	// Step up tasks
	for(int taskn=0; taskn < NUM_TASKS; taskn++) {
		TASK[taskn].regs  = malloc(sizeof(int)*16);
		TASK[taskn].stackp= malloc(sizeof(int)*512)
					+ sizeof(int)*512;
		for(int r=0; r<13; r++)
			TASK[taskn].regs[r] = 0;
		TASK[taskn].regs[15] = (unsigned)user_task;
		TASK[taskn].regs[14] = CC_STEP;
		TASK[taskn].regs[13] = (unsigned)TASK[taskn].stackp;
		TASK[taskn].regs[ 1] = taskn;	// The task ID
		TASK[taskn].regs[ 2] = (unsigned)&task_loops[taskn];
	}

	// Then run them
	while(1) {
		int	completed;

		completed = 0;
		for(int taskn=0; taskn < NUM_TASKS; taskn++) {
			if (TASK[taskn].regs[14] & (CC_TRAP | CC_EXCEPTION)) {
				completed++;
			} else {
				zip_restore_context((void *)TASK[taskn].regs);
				// zip_ucc() |= STEP;//What's the syntax here?!?
				zip_rtu();
				zip_save_context((void *)TASK[taskn].regs);
				if (zip_ucc() & (CC_EXCEPTION))
					success = 0;

				if (TASK[taskn].regs[14] & (CC_TRAP|CC_EXCEPTION)) {
					printf("TASK[%2d] has completed\n", taskn);
				}
			}
		}

		if (completed >= NUM_TASKS)
			break;
	}

	if (success) {
		for(int taskn=0; taskn < NUM_TASKS; taskn++) {
			printf("  LOOPS[%2d] = 0x%08x\n", taskn, task_loops[taskn]);
			if (task_loops[taskn] == 0xffffffff)
				success = 0;
		}

		if (success)
			printf("SUCCESS!\n");
		else
			printf("TASK FAILURE\n");
	} else
		printf("TEST FAILURE!\n");
}
