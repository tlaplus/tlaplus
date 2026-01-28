/*******************************************************************************
 * Copyright (c) 2023 Microsoft Research. All rights reserved. 
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
package tlc2.module;

import java.io.File;
import java.io.IOException;

import tla2sany.semantic.ExprOrOpArgNode;
import tlc2.overrides.Evaluation;
import tlc2.overrides.TLAPlusOperator;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.IValue;
import tlc2.value.ValueInputStream;
import tlc2.value.ValueOutputStream;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.Value;
import util.UniqueString;

public class _TLCTrace {

	@TLAPlusOperator(identifier = "_TLCTraceSerialize", module = "_TLCTrace", warn = false)
	public static final IValue ioSerialize(final IValue value, final StringValue absolutePath)
			throws IOException {
		final ValueOutputStream vos = new ValueOutputStream(new File(absolutePath.val.toString()), true);
		try {
			// Calling IValue#fingerprint guarantees that value can be serialized because
			// fingerprinting also finalizes any internal data structures. For example, it
			// converts the pset of SubsetValue.
			value.fingerPrint(0L);
			value.write(vos);
		} finally {
			vos.close();
		}
		return BoolValue.ValTrue;
	}

	@TLAPlusOperator(identifier = "_TLCTraceDeserialize", module = "_TLCTrace", warn = false)
	public static final IValue ioDeserialize(final StringValue absolutePath) throws IOException {
		final File file = new File(absolutePath.val.toString());
		if (!file.exists()) {
			// ioDeserialize is invoked during constant processing even when the user
			// specifies -dumpTrace but not -loadTrace. In this case, we deliberately return
			// a value that does not represent a valid trace file to signal that the file
			// does not exist. The resulting empty record technically violates the assertion
			// in _TLCTraceConstraint, and the corresponding error message would be
			// misleading in this context. However, _TLCTraceConstraint won't be evaluated
			// when the user passes -dumpTrace without -loadTrace, so this violation should
			// never surface.
			return RecordValue.EmptyRcd;
		}
		final ValueInputStream vis = new ValueInputStream(file, true);
		try {
			return vis.read(UniqueString.internTbl.toMap());
		} finally {
			vis.close();
		}
	}

	@Evaluation(definition = "_TLCState", module = "_TLCTrace", warn = false, silent = true, minLevel = 1)
	public static Value tlcState(final Tool tool, final ExprOrOpArgNode[] args, final Context c,
			final TLCState s0, final TLCState s1, final int control, final CostModel cm) {
		// Overrides the TLA+ definition: _TLCState(level) == Trace[level]
		// The use of TLCExt!Trace is inefficient because it internally reconstructs all
		// states starting from the initial state. As a result, its cost grows linearly
		// with the length of the trace. This override directly returns the state at the
		// current level without reconstruction.
		return new RecordValue(s0);
	}
}
