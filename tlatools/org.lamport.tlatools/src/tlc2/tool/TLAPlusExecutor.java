/*******************************************************************************
 * Copyright (c) 2020 Microsoft Research. All rights reserved. 
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
package tlc2.tool;

import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.locks.ReentrantLock;

import tla2sany.semantic.SymbolNode;
import tlc2.tool.impl.FastTool;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.IValue;
import tlc2.value.impl.Value;
import util.SimpleFilenameToStream;

public class TLAPlusExecutor {

	public class Mapping {
		private final Action action;
		private final Map<SymbolNode, IValue> params;
		private final Map<String, SymbolNode> symbol2node;

		public Mapping(final Action a, final String... params) {
			this.action = a;
			this.params = new HashMap<>();
			this.symbol2node = new HashMap<>();
			for (String param : params) {
				final SymbolNode node = action.con.lookupName(s -> s.getName().equals(param));
				this.symbol2node.put(param, node);
			}
		}

		public Mapping set(final String param, final IValue value) {
			final SymbolNode node = this.symbol2node.get(param);
			this.params.put(node, value);
			return this;
		}

		public Context getContext() {
			// Replace TLC's values in ctx with the given ones by extending the pointer list
			// of ctxs.
			Context ctx = action.con;
			for (Map.Entry<SymbolNode, IValue> entry : params.entrySet()) {
				ctx = ctx.cons(entry.getKey(), entry.getValue());
			}
			return ctx;
		}
	}

	private final ReentrantLock lock = new ReentrantLock();
	private final FastTool tool;

	private TLCState state;

	public TLAPlusExecutor(String spec, String config) {
		this.tool = new FastTool(spec, config, new SimpleFilenameToStream(), Tool.Mode.Executor);

		// Initialize the TLA+ executor by generating the initial state.
		this.state = this.tool.getInitStates().first();
	}

	public Mapping map(final String actionName, final String processNode, final IValue v, final String... params) {
		final Action[] actions = tool.getActions();
		for (Action action : actions) {
			if (action.getName().equals(actionName)) {
				final Object lookup = action.con.lookup(s -> s.getName().equals(processNode));
				if (lookup != null) {
					if (lookup.equals(v)) {
						return new Mapping(action, params);
					}
				}
			}
		}
		throw new RuntimeException("failed to create mapping");
	}

	public Object step(final Mapping m) throws Exception {
		final Context ctx = m.getContext();
		lock.lock();
		try {
			while (true) {
				final StateVec nextStates = this.tool.getNextStates(m.action, ctx, state);
				assert !nextStates.isEmpty();
				this.state = nextStates.first();

				// Check invariants.
				for (int k = 0; k < this.tool.getInvariants().length; k++) {
					if (!tool.isValid(this.tool.getInvariants()[k], this.state)) {
						throw new INextStateFunctor.InvariantViolatedException();
					}
				}

				final Object result = this.state.execCallable();
				if (result != null) {
					return result;
				}
			}
		} finally {
			lock.unlock();
		}
	}

	public ReentrantLock getLock() {
		return lock;
	}
	
	public Value getConstant(final String string) {
		return (Value) this.tool.getSpecProcessor().getDefns().get(string);
	}
}
