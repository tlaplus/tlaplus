/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved.
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tlc2.tool.queue;

import gov.nasa.jpf.jvm.bytecode.GETSTATIC;
import gov.nasa.jpf.jvm.bytecode.INVOKESTATIC;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.VM;

/**
 * Collects execution traces from the fixed single-worker workload launched by
 * {@code collect-queue-traces}. JPF explores different thread schedules and
 * backtracks between them. This listener restores the event history on each
 * backtrack, so events from different executions are never concatenated.
 *
 * <p>
 * The queue's {@code trace(Action.X)} calls identify the events to record. The
 * listener records the thread and action, then skips the marker bytecode so JFR
 * and its counters do not become part of JPF's program state. These markers could
 * potentially be retired by recognizing equivalent events through JPF's
 * instruction, method, and monitor callbacks. {@link QueueMethodTraceListener}
 * provides a coarser, method-based alternative that does not use markers.
 *
 * <p>
 * Histories with the same beginning share nodes in a prefix tree. Each node adds
 * one event to its parent's history; node zero is the empty history. The tree
 * stays outside JPF's program state, so recording does not prevent state matching.
 * Every node represents an execution prefix, including prefixes that end when
 * JPF matches a previously explored state rather than terminating the execution.
 *
 * <p>
 * After depth-first search finishes without errors or search limits, write the
 * tree to {@code nodes.tsv}. A separate TLC run must replay every node's history
 * against the queue specification. The Ant target removes the previous file
 * before collection, so an incomplete search cannot leave a replayable export.
 */
public final class QueueTraceListener extends QueueTraceRecorder {

	private static final String MARKER = "tlc2.tool.queue.DiskStateQueue2TLA";

	@Override
	public void executeInstruction(VM vm, ThreadInfo ti, Instruction instruction) {
		// javac emits GETSTATIC Action.X; INVOKESTATIC trace(Action). Skip
		// both, so even enum initialization/shared reads cannot add choices.
		if (isMarker(instruction)) {
			throw new IllegalArgumentException("Expected a literal Action constant before trace(Action)");
		}
		if (!(instruction instanceof GETSTATIC) || !isMarker(instruction.getNext())) {
			return;
		}
		GETSTATIC actionField = (GETSTATIC) instruction;
		if (!(MARKER + "$Action").equals(actionField.getClassName())) {
			throw new IllegalArgumentException("Unexpected trace argument: " + actionField);
		}
		record(ti, actionField.getFieldName());
		ti.skipInstruction(instruction.getNext().getNext());
	}

	private static boolean isMarker(Instruction instruction) {
		if (!(instruction instanceof INVOKESTATIC)) {
			return false;
		}
		INVOKESTATIC call = (INVOKESTATIC) instruction;
		return MARKER.equals(call.getInvokedMethodClassName())
				&& "trace(Ltlc2/tool/queue/DiskStateQueue2TLA$Action;)V".equals(call.getInvokedMethodName());
	}
}
