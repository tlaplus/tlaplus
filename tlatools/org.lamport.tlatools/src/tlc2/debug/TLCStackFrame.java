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
package tlc2.debug;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import org.eclipse.lsp4j.debug.Scope;
import org.eclipse.lsp4j.debug.Source;
import org.eclipse.lsp4j.debug.StackFrame;
import org.eclipse.lsp4j.debug.Variable;

import tla2sany.semantic.NumeralNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.st.Location;
import tlc2.output.EC;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.impl.LazyValue;
import tlc2.value.impl.Value;
import util.Assert;

class TLCStackFrame extends StackFrame {
	
	// Not thread-safe because TLCDebugger is assumed to take care of synchronization!
	private static final Map<SemanticNode, String> PATH_CACHE = new HashMap<>();
	
	public static final String SCOPE = "Context";
	
	// It would be easier to use hashCode instead of passing a random generator
	// around. However, calculating the hashCode for a TLC value calculates the
	// value's fingerprint, which normalizes and, thus, enumerates the value.
	protected static final Random rnd = new Random();

	protected transient final Map<Integer, DebugTLCVariable> nestedVariables = new HashMap<>();

	private transient final SemanticNode node;
	private transient final Context ctxt;
	protected transient final Tool tool;

	private final int stackId;

	public TLCStackFrame(SemanticNode node, Context ctxt, final Tool tool) {
		this.node = node;
		Assert.check(node != null, EC.GENERAL);
		// Do not create a deep copy of ctxt (like it is done for state and predecessor
		// in TLCInit|NextStackFrame. A TLCStackFrame will point to its corresponding
		// node in the Context tree even if Context mutates.
		this.ctxt = ctxt;
		Assert.check(ctxt != null, EC.GENERAL);
		this.tool = tool;
		Assert.check(tool != null, EC.GENERAL);

		if (node instanceof NumeralNode) {
			setName(Integer.toString(((NumeralNode)node).val()));
		} else {
			setName(node.getHumanReadableImage());
		}
		setId(node.myUID);

		final Location location = node.getLocation();
		setLine(location.beginLine());
		setEndLine(location.endLine());
		setColumn(location.beginColumn());
		setEndColumn(location.endColumn()+1);

		final Source source = new Source();
		source.setName(node.getLocation().source());
		// resolve(..) triggers a file-system round-trip (IO), which is obviously too
		// expensive!!! Thus, cache the result.
		source.setPath(PATH_CACHE.computeIfAbsent(node,
				n -> tool.getResolver().resolve(n.getTreeNode().getFilename(), true).getAbsolutePath().toString()));
		setSource(source);
		
		this.stackId = rnd.nextInt(Integer.MAX_VALUE - 1) + 1;
	}

	Variable[] getVariables() {
		return getVariables(stackId);
	}
	
	public Variable[] getVariables(final int vr) {
		return tool.eval(() -> {
			if (nestedVariables.containsKey(vr)) {
				DebugTLCVariable[] nested = nestedVariables.get(vr).getNested(rnd);
				for (DebugTLCVariable debugTLCVariable : nested) {
					nestedVariables.put(debugTLCVariable.getVariablesReference(), debugTLCVariable);
				}
				return nested;
			}

			final List<Variable> vars = new ArrayList<>();
			if (stackId == vr) {
				Context c = this.ctxt;
				while (c.hasNext()) {
					Object val = c.getValue();
					if (val instanceof LazyValue) {
						// unlazy/eval LazyValues
						val = unlazy((LazyValue) c.getValue());
					}
					if (val instanceof Value) {
						final Value value = (Value) val;
						final DebugTLCVariable variable = (DebugTLCVariable) value
								.toTLCVariable(new DebugTLCVariable(c.getName().getName().toString()), rnd);
						nestedVariables.put(variable.getVariablesReference(), variable);
						vars.add(variable);
					} else if (val instanceof SemanticNode) {
						final Variable variable = new Variable();
						variable.setName(c.getName().getSignature());
						variable.setValue(((SemanticNode) val).getHumanReadableImage());
						vars.add(variable);
					} else {
						System.err.println("This is interesting!!! What's this??? " + val.toString());
					}
					c = c.next();
				}
			}
			
			return vars.toArray(new Variable[vars.size()]);
		});
	}

	protected Object unlazy(final LazyValue lv) {
		return tool.eval(() -> {
			return lv.eval(tool);
		});
	}

	public Scope[] getScopes() {
		final List<Scope> scopes = new ArrayList<>();
		
		if (!ctxt.isEmpty()) {
			final Scope scope = new Scope();
			scope.setName(SCOPE);
			scope.setVariablesReference(stackId);
			scopes.add(scope);
		}
		return scopes.toArray(new Scope[scopes.size()]);
	}
	
	public SemanticNode getNode() {
		return node;
	}

	public Context getContext() {
		return ctxt;
	}

	public Tool getTool() {
		return tool;
	}

	@Override
	public String toString() {
		return "TLCStackFrame [node=" + node + "]";
	}
}