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
 ******************************************************************************/
package tlc2.tool.queue;

import java.util.Set;

import gov.nasa.jpf.jvm.bytecode.GETFIELD;
import gov.nasa.jpf.jvm.bytecode.GOTO;
import gov.nasa.jpf.jvm.bytecode.IRETURN;
import gov.nasa.jpf.jvm.bytecode.IfInstruction;
import gov.nasa.jpf.jvm.bytecode.JVMInvokeInstruction;
import gov.nasa.jpf.jvm.bytecode.JVMReturnInstruction;
import gov.nasa.jpf.jvm.bytecode.MONITORENTER;
import gov.nasa.jpf.jvm.bytecode.MONITOREXIT;
import gov.nasa.jpf.jvm.bytecode.PUTFIELD;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.VM;

/**
 * Uses JPF listener callbacks to observe selected queue methods, field accesses,
 * and monitor operations, recording execution prefixes for TLA+ trace validation.
 * Boolean results and null/non-null state results are retained; state values are
 * abstracted away. The observations cover the fixed single-worker
 * DiskStateQueueJPFTest workload, not the entire queue API.
 *
 * <p>
 * JPF invokes methodEntered after acquiring a synchronized method's monitor and
 * methodExited when releasing it, before another thread can acquire it. On normal
 * return, the callee's operand stack still contains the return value. Recording
 * in these callbacks avoids duplicate observations when a return instruction is
 * reexecuted after a scheduling choice.
 *
 * <p>
 * Instruction callbacks record completed field accesses and branch outcomes, not
 * scheduling attempts that JPF will reexecute. Monitor callbacks distinguish
 * notification from actual reacquisition after wait. The listener keeps no
 * per-thread observation state: the current stack identifies the operation even
 * after JPF backtracks.
 *
 * <p>
 * DiskStateQueueMethodTrace.tla checks that each recorded execution prefix can be
 * reproduced by the specification. Every replay step consumes an observation;
 * the replay cannot insert unobserved specification actions.
 */
public final class QueueMethodTraceListener extends QueueTraceRecorder {

	private static final String QUEUE = "tlc2.tool.queue.";
	private static final String POOL = "tlc2.util.";
	private static final Set<String> ENTRIES = Set.of(
			"StateQueue.sEnqueue([Ltlc2/tool/TLCState;)V",
			"StateQueue.sDequeue()Ltlc2/tool/TLCState;",
			"StateQueue.suspendAll()Z",
			"StateQueue.finishAll()V",
			"StatePoolWriter.doWork([Ltlc2/tool/TLCState;Ljava/io/File;)[Ltlc2/tool/TLCState;",
			"StatePoolReader.doWork([Ltlc2/tool/TLCState;Ljava/io/File;)[Ltlc2/tool/TLCState;",
			"StatePoolReader.getCache([Ltlc2/tool/TLCState;Ljava/io/File;)[Ltlc2/tool/TLCState;");
	private static final Set<String> RETURNS = Set.of(
			"StateQueue.enqueue(Ltlc2/tool/TLCState;)V",
			"StateQueue.sEnqueue([Ltlc2/tool/TLCState;)V",
			"StateQueue.sDequeue()Ltlc2/tool/TLCState;",
			"StateQueue.isAvail()Z",
			"StateQueue.suspendAll()Z",
			"StateQueue.resumeAll()V",
			"StateQueue.finishAll()V",
			"DiskStateQueue.enqueueInner(Ltlc2/tool/TLCState;)V",
			"DiskStateQueue.dequeueInner()Ltlc2/tool/TLCState;",
			"DiskStateQueue.fillDeqBuffer()V",
			"DiskStateQueue$StatePoolCleaner.run()V",
			"DiskStateQueue.finishAll()V",
			"StatePoolWriter.doWork([Ltlc2/tool/TLCState;Ljava/io/File;)[Ltlc2/tool/TLCState;",
			"StatePoolReader.doWork([Ltlc2/tool/TLCState;Ljava/io/File;)[Ltlc2/tool/TLCState;",
			"StatePoolReader.getCache([Ltlc2/tool/TLCState;Ljava/io/File;)[Ltlc2/tool/TLCState;",
			"StatePoolReader.wakeup()V");
	private static final Set<String> WAITS = Set.of(
			"StateQueue.isAvail",
			"StateQueue.suspendAll",
			"StatePoolWriter.ensureWritten",
			"StatePoolWriter.run",
			"StatePoolReader.run");
	private static final Set<String> BACKGROUND = Set.of("StatePoolWriter.run", "StatePoolReader.run");
	private static final Set<String> READER_CALLS = Set.of("StatePoolReader.doWork", "StatePoolReader.getCache");
	private static final Set<String> WRITES = Set.of(
			"StateQueue.finishAll.finish",
			"StatePoolWriter.setFinished.finished",
			"StatePoolReader.setFinished.finished",
			"DiskStateQueue.finishAll.finished",
			"StatePoolReader.run.isFull");

	@Override
	public void methodEntered(VM vm, ThreadInfo thread, MethodInfo method) {
		if (selected(method, ENTRIES)) {
			record(thread, name(method) + ".enter");
		}
	}

	@Override
	public void methodExited(VM vm, ThreadInfo thread, MethodInfo method) {
		if (method.getFullName().equals("tlc2.value.ValueOutputStream.close()V")
				&& name(thread.getTopFrame().getPrevious().getMethodInfo()).equals("StatePoolWriter.doWork")) {
			record(thread, "StatePoolWriter.doWork.flush");
		}
		if (!selected(method, RETURNS)) {
			return;
		}
		if (!(thread.getPC() instanceof JVMReturnInstruction)) {
			throw new IllegalStateException("Queue method did not return normally: " + method);
		}
		String event = name(method) + ".return";
		if (method.getSignature().endsWith(")Z")) {
			event += thread.getTopFrame().peek() == 0 ? ".false" : ".true";
		} else if (method.getSignature().endsWith(")[Ltlc2/tool/TLCState;")) {
			event += thread.getTopFrame().peek() == MJIEnv.NULL ? ".null" : ".buffer";
		} else if (method.getSignature().endsWith(")Ltlc2/tool/TLCState;")) {
			event += thread.getTopFrame().peek() == MJIEnv.NULL ? ".null" : ".state";
		}
		record(thread, event);
	}

	@Override
	public void instructionExecuted(VM vm, ThreadInfo thread, Instruction next, Instruction executed) {
		if (next == executed) {
			return;
		}
		if (executed instanceof IfInstruction && executed.getPrev() instanceof GETFIELD
				&& READER_CALLS.contains(name(executed.getMethodInfo()))) {
			// Retain the actual branch outcome, including the opcode, so replay can
			// distinguish cache, pending-file, direct-file, and empty returns.
			GETFIELD field = (GETFIELD) executed.getPrev();
			record(thread, name(executed.getMethodInfo()) + "." + field.getFieldName() + "."
					+ executed.getMnemonic() + "." + ((IfInstruction) executed).getConditionValue());
			return;
		}
		if (executed instanceof GOTO && name(executed.getMethodInfo()).equals("StatePoolWriter.run")
				&& executed.getPrev() instanceof JVMInvokeInstruction
				&& ((JVMInvokeInstruction) executed.getPrev()).getInvokedMethodName().equals("wakeup()V")) {
			record(thread, "StatePoolWriter.run.repeat");
			return;
		}
		// A shared-field instruction can schedule another thread before completing.
		if (!(executed instanceof GETFIELD || executed instanceof PUTFIELD) || next != executed.getNext()) {
			return;
		}
		String method = name(executed.getMethodInfo());
		if (executed instanceof GETFIELD) {
			GETFIELD field = (GETFIELD) executed;
			if (method.equals("DiskStateQueue.enqueueInner") && field.getFieldName().equals("writer")) {
				record(thread, "StatePoolWriter.doWork.call");
			} else if (method.equals("DiskStateQueue.fillDeqBuffer") && field.getFieldName().equals("writer")) {
				record(thread, "StatePoolWriter.ensureWritten.call");
			} else if (method.equals("DiskStateQueue.fillDeqBuffer") && field.getFieldName().equals("reader")) {
				// Loading the receiver precedes the synchronized call, which may block.
				JVMInvokeInstruction call = nextCall(executed);
				String target = call.getInvokedMethodName();
				record(thread, "StatePoolReader." + target.substring(0, target.indexOf('(')) + ".call");
			} else if (method.equals("StateQueue.isAvail") && field.getFieldName().equals("mu")
					&& field.isMonitorEnterPrologue()) {
				// Reaching synchronized(mu) establishes that this is the last
				// worker and the queue is not empty.
				record(thread, method + ".countLast");
			}
		} else if (executed instanceof PUTFIELD) {
			PUTFIELD field = (PUTFIELD) executed;
			String access = method + "." + field.getFieldName();
			if (WRITES.contains(access)) {
				record(thread, access + "." + (field.getLastValue() != 0));
			} else if (access.equals("DiskStateQueue.enqueueInner.enqIndex") && field.getLastValue() == 0) {
				record(thread, "DiskStateQueue.enqueueInner.spilled");
			}
		}
	}

	@Override
	public void objectWait(VM vm, ThreadInfo thread, ElementInfo monitor) {
		String method = caller(thread);
		if (WAITS.contains(method)) {
			record(thread, method + ".wait");
		}
	}

	@Override
	public void objectLocked(VM vm, ThreadInfo thread, ElementInfo monitor) {
		String method = caller(thread);
		MethodInfo instructionMethod = thread.getPC().getMethodInfo();
		if (instructionMethod.getClassName().equals("java.lang.Object")
				&& instructionMethod.getName().equals("wait") && WAITS.contains(method)) {
			record(thread, method + ".wake");
		} else if (thread.getPC() instanceof MONITORENTER) {
			if (BACKGROUND.contains(method)) {
				record(thread, method + ".lock");
			} else if (method.equals("StatePoolWriter.ensureWritten")) {
				record(thread, method + ".lock");
			} else if (method.equals("StateQueue.suspendAll")) {
				record(thread, method + (monitor.getObjectRef() == thread.getThis() ? ".lock.q" : ".lock.mu"));
			}
		}
	}

	@Override
	public void objectUnlocked(VM vm, ThreadInfo thread, ElementInfo monitor) {
		// wait() also releases its monitor; objectWait handles that case.
		if (!(thread.getPC() instanceof MONITOREXIT)) {
			return;
		}
		String method = caller(thread);
		if (BACKGROUND.contains(method) || method.equals("StatePoolWriter.ensureWritten")) {
			record(thread, method + ".unlock");
		} else if (method.equals("StateQueue.suspendAll")) {
			boolean queue = monitor.getObjectRef() == thread.getThis();
			String event = method + (queue ? ".unlock.q" : ".unlock.mu");
			if (thread.getPC().getNext() instanceof IRETURN) {
				// MONITOREXIT has not popped the monitor reference yet; the boolean
				// return value is immediately beneath it on the operand stack.
				event += ".return." + (thread.getTopFrame().peek(1) != 0);
			} else if (queue) {
				// The Ant build retains local-variable debug information.
				event += thread.getTopFrame().getLocalVariable("needWait") != 0 ? ".wait" : ".done";
			}
			record(thread, event);
		}
	}

	@Override
	public void objectNotify(VM vm, ThreadInfo thread, ElementInfo monitor) {
		String method = caller(thread);
		if (method.equals("StateQueue.isAvail") || method.equals("StateQueue.finishAll")) {
			record(thread, method + ".notify.mu");
		}
	}

	@Override
	public void objectNotifyAll(VM vm, ThreadInfo thread, ElementInfo monitor) {
		String method = caller(thread);
		if (method.equals("StateQueue.sEnqueue")) {
			record(thread, method + ".notifyAll");
		} else if (method.equals("DiskStateQueue.finishAll")
				&& monitor.getClassInfo().getName().equals(POOL + "StatePoolReader")) {
			record(thread, method + ".notifyAll.reader");
		}
	}

	private static JVMInvokeInstruction nextCall(Instruction instruction) {
		Instruction next = instruction.getNext();
		while (!(next instanceof JVMInvokeInstruction)) {
			next = next.getNext();
		}
		return (JVMInvokeInstruction) next;
	}

	private static String caller(ThreadInfo thread) {
		StackFrame frame = thread.getTopFrame();
		// Monitor callbacks for wait/notify run in java.lang.Object's native frame.
		while (frame != null && frame.getMethodInfo().getClassName().equals("java.lang.Object")) {
			frame = frame.getPrevious();
		}
		return frame == null ? "" : name(frame.getMethodInfo());
	}

	private static boolean selected(MethodInfo method, Set<String> methods) {
		String fullName = method.getFullName();
		return (fullName.startsWith(QUEUE) && methods.contains(fullName.substring(QUEUE.length())))
				|| (fullName.startsWith(POOL) && methods.contains(fullName.substring(POOL.length())));
	}

	private static String name(MethodInfo method) {
		String className = method.getClassName();
		if (className.startsWith(QUEUE)) {
			return className.substring(QUEUE.length()) + "." + method.getName();
		}
		if (className.startsWith(POOL)) {
			return className.substring(POOL.length()) + "." + method.getName();
		}
		return "";
	}
}
