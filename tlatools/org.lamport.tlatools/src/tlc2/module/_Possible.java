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
package tlc2.module;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import tlc2.TLCGlobals;
import tlc2.overrides.TLAPlusOperator;
import tlc2.tool.AbstractChecker;
import tlc2.value.IValue;
import tlc2.value.ValueConstants;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.Value;
import util.UniqueString;

public class _Possible implements ValueConstants {

	public static final long serialVersionUID = 20260408L;

	private static final UniqueString KEY = UniqueString.uniqueStringOf("s:_possible");

	@TLAPlusOperator(identifier = "_Counts", module = "_Possible", warn = false)
	public static Value counts() {
		final List<IValue> perWorker;
		if (TLCGlobals.mainChecker != null) {
			perWorker = ((AbstractChecker) TLCGlobals.mainChecker).getAllNamedValues(KEY);
		} else if (TLCGlobals.simulator != null) {
			perWorker = TLCGlobals.simulator.getAllNamedValues(KEY);
		} else {
			return new FcnRcdValue(new Value[0], new Value[0], false);
		}

		final Map<Value, Integer> totals = new HashMap<>();
		for (IValue wv : perWorker) {
			if (wv instanceof FcnRcdValue) {
				FcnRcdValue rec = (FcnRcdValue) ((Value) wv).normalize();
				for (int i = 0; i < rec.domain.length; i++) {
					totals.merge(rec.domain[i],
						((IntValue) rec.values[i]).val, Integer::sum);
				}
			}
		}

		final Value[] domain = new Value[totals.size()];
		final Value[] values = new Value[totals.size()];
		int i = 0;
		for (Map.Entry<Value, Integer> e : totals.entrySet()) {
			domain[i] = e.getKey();
			values[i] = IntValue.gen(e.getValue());
			i++;
		}
		return new FcnRcdValue(domain, values, false);
	}
}
