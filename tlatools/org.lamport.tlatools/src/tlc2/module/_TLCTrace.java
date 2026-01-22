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
import tla2sany.semantic.OpDefNode;
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
import tlc2.value.impl.TupleValue;
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

	// _TLCTraceDeserialize is overridden but won't be called except from
	// _tlcTraceConstraint0 below if _tlcTraceConstraint0 is active.
	@TLAPlusOperator(identifier = "_TLCTraceDeserialize", module = "_TLCTrace", warn = false)
	public static final IValue ioDeserialize(final StringValue absolutePath) throws IOException {
		final ValueInputStream vis = new ValueInputStream(new File(absolutePath.val.toString()), true);
		try {
			return vis.read(UniqueString.internTbl.toMap());
		} finally {
			vis.close();
		}
	}

	// Override the TLA+ operator definition of _TLCTraceConstraint0 for performance
	// reasons:
	// - Avoid repeated deserialization of the trace file by caching the
	// deserialized trace
	// - Avoid repeated reconstruction of the current trace represented by
	// TLCExt!Trace
	// - Is synchronized to be thread-safe when called from multiple workers
	// - Resulting contention is acceptable because we are recreating a single trace
	// where multiple workers are of limited use.
	@Evaluation(definition = "_TLCTraceConstraint0", module = "_TLCTrace", minLevel = 1, warn = false, silent = true)
	public synchronized static Value tlcTraceConstraint0(final Tool tool, final ExprOrOpArgNode[] args, final Context c,
			final TLCState s0, final TLCState s1, final int control, final CostModel cm) throws IOException {

		// Cache the deserialized trace in the operator definition to avoid repeated IO.
		final OpDefNode opDef = tool.getSpecProcessor().getModuleTbl().getModuleNode("_TLCTrace")
				.getOpDef("_TLCTraceDeserialize");
		IValue trace = (IValue) opDef.getToolObject(tool.getId());
		if (trace == null) {
			final Value absoluteFilename = tool.eval(args[0], c, s0, s1, control, cm);
			trace = ioDeserialize((StringValue) absoluteFilename);
			trace.deepNormalize();
			opDef.setToolObject(tool.getId(), trace);
		}

		// The trace is a TupleValue of RecordValues, where the i-th - 1 element
		// corresponds to the current state. -1 because Java is 0-based, while TLA+ is
		// 1-based.
		if (s0.getLevel() < 1 || s0.getLevel() > ((TupleValue) trace).size()) {
			return BoolValue.ValTrue;
		}
		final RecordValue tr = (RecordValue) ((TupleValue) trace).getElem(s0.getLevel() - 1);
		return new RecordValue(s0).equals(tr) ? BoolValue.ValTrue : BoolValue.ValFalse;
	}
}
