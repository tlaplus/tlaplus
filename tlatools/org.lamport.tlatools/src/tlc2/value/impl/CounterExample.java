/*******************************************************************************
 * Copyright (c) 2022 Microsoft Research. All rights reserved. 
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
package tlc2.value.impl;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import tlc2.tool.Action;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateInfo;
import util.UniqueString;

public class CounterExample extends RecordValue {

	private static final UniqueString STATES = UniqueString.of("state");
	private static final UniqueString ACTIONS = UniqueString.of("action");

	public CounterExample() {
		this(new ArrayList<>(0), Action.UNKNOWN, 0);
	}

	public CounterExample(final List<TLCStateInfo> trace) {
		this(trace, Action.UNKNOWN, 0);
	}

	// CounterExample has been modeled as a graph to represent counterexamples
	// of safety *and* liveness violations. Also, this representation is
	// suitable once the code is extended to handle TLC's "-continue" parameter,
	// when there can be many counterexamples.
	// TODO Include name of definition of the violated property.
	public CounterExample(final List<TLCStateInfo> trace, final Action action, final int loopOrdinal) {
		super(new UniqueString[] { ACTIONS, STATES }, new Value[2], false);

		final int loopIdx = loopOrdinal - 1;
		assert loopIdx < trace.size();

		final LinkedList<Value> states = new LinkedList<>();
		final List<Value> actions = new ArrayList<>();

		// A sequence of distinct states...
		for (int i = 0; i < trace.size(); i++) {
			final TLCStateInfo info = trace.get(i);
			final Value r = new TupleValue(new Value[] { IntValue.gen(info.state.getLevel()), new RecordValue(info) });
			if (i > 0) {
				final TupleValue edge = new TupleValue(
						new Value[] { states.getLast(), new RecordValue(info.getAction()), r });
				actions.add(edge);
			}
			states.add(r);
		}

		// The actions that completes the sequence to close the lasso.
		if (loopOrdinal > 0) {
			final Value last = states.getLast();
			final Value back = states.get(loopIdx);
			final TupleValue edge = new TupleValue(new Value[] { last, new RecordValue(action), back });
			actions.add(edge);
		}

		this.values[0] = new SetEnumValue(actions.toArray(Value[]::new), false);
		this.values[1] = new SetEnumValue(states.toArray(Value[]::new), false);
	}
	public CounterExample(TLCState initialState) {
		this(Arrays.asList(new TLCStateInfo[] { new TLCStateInfo(initialState) }), Action.UNKNOWN, 0);
	}

    public Value toTrace() {
		final SetEnumValue set = (SetEnumValue) this.select(new StringValue(STATES));
		final Value[] v = new Value[set.elems.size()];
		for (int i = 0; i < v.length; i++) {
			final TupleValue tv = (TupleValue) set.elems.elementAt(i);
			v[((IntValue) tv.getElem(0)).val - 1] = (Value) tv.getElem(1);
		}
		return new TupleValue(v);
	}
}
