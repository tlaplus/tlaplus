/*******************************************************************************
 * Copyright (c) 2025 NVIDIA. All rights reserved. 
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
package tlc2.debug;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.CompletableFuture;

import org.eclipse.lsp4j.debug.Scope;
import org.eclipse.lsp4j.debug.Variable;

import tla2sany.semantic.SemanticNode;
import tlc2.debug.IDebugTarget.Granularity;
import tlc2.tool.IStateFunctor;
import tlc2.tool.TLCState;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.impl.RecordValue;

public class TLCInitStatesStackFrame extends TLCStackFrame {

	public static final String SCOPE = "Initials";

	private transient final IStateFunctor functor;

	// Maps variable reference IDs to TLC states for successor states.
	// The mapping would be more robust, if we used the fingerprint instead of the
	// variable reference ID. In the general case, however, FPs cannot be computed
	// if the state is only partial, i.e., not all variables have been determined.
	// Moreover, the DAP's representation of variable references is an integer, not
	// a long. This is why the front-end uses the DAP's variable references.
	private transient final Map<Integer, TLCState> idToStateMap = new HashMap<>();

	protected transient final int stateId;

	public TLCInitStatesStackFrame(TLCStackFrame parent, SemanticNode pred, Context con, Tool tool,
			IStateFunctor functor) {
		super(parent, pred, con, tool);
		this.stateId = rnd.nextInt(Integer.MAX_VALUE - 1) + 1;
		this.functor = functor;
	}

	protected Set<TLCState> getStates() {
		return functor.getStates().toSet();
	}

	@Override
	public Scope[] getScopes() {
		final List<Scope> scopes = new ArrayList<>(Arrays.asList(super.getScopes()));
		final Scope scope = new Scope();
		scope.setName(SCOPE);
		scope.setVariablesReference(stateId);
		scopes.add(scope);
		return scopes.toArray(new Scope[scopes.size()]);
	}

	// Change the debugger's buttons and granularity when entering/exiting
	
	@Override
	public boolean handle(final TLCDebugger debugger) {
		return debugger.stack.size() == 1;
	}

	@Override
	public void preHalt(final TLCDebugger debugger) {
		debugger.sendCapabilities(TLCCapabilities.NO_STEP_BACK);
		debugger.setGranularity(Granularity.State);
	}

	@Override
	public void postHalt(final TLCDebugger debugger) {
		debugger.sendCapabilities(TLCCapabilities.STEP_BACK);
		debugger.setGranularity(Granularity.Formula);
	}
	
	// Render the frame in the debugger's variables view.

	@Override
	public Variable[] getVariables(final int vr) {
		if (vr == stateId) {
			return tool.eval(() -> {
				// Sort lexicographically by state representation for stable order.
				final Set<TLCState> initials = new TreeSet<>((s1, s2) -> {
					return s1.toString().compareTo(s2.toString());
				});
				initials.addAll(functor.getStates().toSet());

				// Convert states into the DAP representation.
				final Variable[] vars = new Variable[initials.size()];
				final int width = String.valueOf(initials.size()).length();
				final Iterator<TLCState> itr = initials.iterator();
				for (int i = 0; i < vars.length; i++) {
					TLCState t = itr.next();
					RecordValue r = new RecordValue(t);
					vars[i] = getStateAsVariable(r, t.getLevel() + "." + String.format("%0" + width + "d", i + 1) + ": "
							+ (t.hasAction() ? t.getAction().getLocation() : "<???>"));
					// See note about getVariablesReference in the declaration of idToStateMap.
					idToStateMap.put(vars[i].getVariablesReference(), t);
				}
				return vars;
			});
		}
		return super.getVariables(vr);
	}
	
	// Handle user selecting a different initial state.

	@Override
	public synchronized CompletableFuture<Void> gotoState(final TLCDebugger debugger, int id) {
		// idToStateMap is populated with the trace from the initial state to the
		// current state s, and all of s' successor states.
		TLCState tlcState = idToStateMap.get(id);
		if (tlcState != null) {
			functor.setElement(tlcState);
			return super.gotoState(debugger, id);
		}

		return super.gotoState(debugger, id);
	}

	Variable[] getStatesVariables() {
		return getVariables(stateId);
	}
}
