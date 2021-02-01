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
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Random;
import java.util.stream.Collectors;

import org.eclipse.lsp4j.debug.Scope;
import org.eclipse.lsp4j.debug.ScopePresentationHint;
import org.eclipse.lsp4j.debug.Source;
import org.eclipse.lsp4j.debug.StackFrame;
import org.eclipse.lsp4j.debug.Variable;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NumeralNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.st.Location;
import tlc2.output.EC;
import tlc2.tool.EvalException;
import tlc2.tool.impl.SpecProcessor;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.impl.LazyValue;
import tlc2.value.impl.TLCVariable;
import tlc2.value.impl.Value;
import util.Assert;
import util.Assert.TLCRuntimeException;
import util.UniqueString;

class TLCStackFrame extends StackFrame {
	
	// Not thread-safe because TLCDebugger is assumed to take care of synchronization!
	private static final Map<SemanticNode, String> PATH_CACHE = new HashMap<>();

	public static final String CONSTANTS = "Constants";
	public static final String SCOPE = "Context";
	
	// It would be easier to use hashCode instead of passing a random generator
	// around. However, calculating the hashCode for a TLC value calculates the
	// value's fingerprint, which normalizes and, thus, enumerates the value.
	protected static final Random rnd = new Random();

	protected transient final Map<Integer, DebugTLCVariable> nestedVariables = new HashMap<>();
	protected transient final Map<Integer, List<DebugTLCVariable>> nestedConstants = new HashMap<>();

	protected transient final SemanticNode node;
	protected transient final Context ctxt;
	protected transient final Tool tool;

	protected final int constantsId;
	protected final int stackId;
	
	// Testing only!
	TLCStackFrame(int id) {
		super();
		this.node = null;
		this.ctxt = null;
		this.tool = null;
		this.constantsId = -1;
		this.stackId = -1;
		this.setId(id);
	}

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
		// There is a 1:n mapping between SemanticNode and TLCStackFrames. For example,
		// the same SN appears multiple times on the stack in case of recursion.
		setId(node.myUID ^ rnd.nextInt(Integer.MAX_VALUE - 1) + 1);

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
		this.constantsId = rnd.nextInt(Integer.MAX_VALUE - 1) + 1;
	}

	Variable[] getVariables() {
		return getVariables(stackId);
	}

	Variable[] getConstants() {
		return getVariables(constantsId);
	}
	
	public Variable[] getVariables(final int vr) {
		return tool.eval(() -> {
			final List<Variable> vars = new ArrayList<>();

			if (nestedVariables.containsKey(vr)) {
				List<TLCVariable> nested = nestedVariables.get(vr).getNested(rnd);
				for (TLCVariable n : nested) {
					DebugTLCVariable d = (DebugTLCVariable) n;
					nestedVariables.put(d.getVariablesReference(), d);
					vars.add(d);
				}
			}

			if (nestedConstants.containsKey(vr)) {
				List<DebugTLCVariable> cntsts = nestedConstants.get(vr);
				for (DebugTLCVariable c : cntsts) {
					nestedVariables.put(c.getVariablesReference(), c);
					List<TLCVariable> nested = c.getNested(rnd);
					for (TLCVariable n : nested) {
						DebugTLCVariable d = (DebugTLCVariable) n;
						nestedVariables.put(d.getVariablesReference(), d);
					}
				}
				vars.addAll(cntsts);
			}

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
					} else if (val instanceof RuntimeException) {
						final Variable variable = new Variable();
						variable.setName(c.getName().getName().toString());
						variable.setValue(c.getValue().toString());
						final RuntimeException re = (RuntimeException) val;
						variable.setType(re.getMessage());
						vars.add(variable);
					} else {
						System.err.println("This is interesting!!! What's this??? " + val.toString());
					}
					c = c.next();
				}
			} else if (constantsId == vr) {
				//TODO: This is evaluated for each TLCStackFrame instance even though the constantDefns
				// never change.  Perhaps, this can be moved to a place where it's only evaluated once.
				// On the other hand, the debug adapter protocol (DAP) might not like sharing
				// DebugTLCVariables.
				final SpecProcessor sp = this.tool.getSpecProcessor();
				final Map<ModuleNode, Map<OpDefNode, Object>> constantDefns = sp.getConstantDefns();
				for (final Entry<ModuleNode, Map<OpDefNode, Object>> e : constantDefns.entrySet()) {
					final ModuleNode module = e.getKey();
					
					final Variable v = new Variable();
					// Pick one of the OpDefNode and derive the name with which the definition
					// appears in the spec, i.e. A!B!C!Op -> A!B!C.  Users then see the module
					// name and instance path that appears in the instantiating module. getPathName
					// equals the empty (unique) string if the module has no path.
					v.setValue(e.getValue().keySet().stream().findAny().map(odn -> odn.getPathName())
							.orElse(UniqueString.of(module.getSignature())).toString());
					v.setName(module.getSignature());
					v.setVariablesReference(rnd.nextInt(Integer.MAX_VALUE - 1) + 1);

					nestedConstants.put(v.getVariablesReference(),
							e.getValue().entrySet().stream().filter(f -> f.getValue() instanceof Value)
									.map(f -> (DebugTLCVariable) ((Value) f.getValue())
											.toTLCVariable(new DebugTLCVariable(f.getKey().getLocalName()), rnd))
									.collect(Collectors.toList()));
					vars.add(v);
				}
			}
			
			// Its nicer if the variables/constants are sorted lexicographically.
			vars.sort(new Comparator<Variable>() {
				@Override
				public int compare(Variable o1, Variable o2) {
					return o1.getName().compareTo(o2.getName());
				}
			});
			return vars.toArray(new Variable[vars.size()]);
		});
	}

	protected Object unlazy(final LazyValue lv) {
		try {
			return tool.eval(() -> {
				return lv.eval(tool);
			});
		} catch (TLCRuntimeException | EvalException e) {
			return e;
		}
	}

	public Scope[] getScopes() {
		final List<Scope> scopes = new ArrayList<>();
		
		if (!ctxt.isEmpty()) {
			final Scope scope = new Scope();
			scope.setName(SCOPE);
			scope.setVariablesReference(stackId);
			scopes.add(scope);
		}
		
		if (!this.tool.getSpecProcessor().getConstantDefns().isEmpty()) {
			final Scope scope = new Scope();
			scope.setName(CONSTANTS);
			scope.setVariablesReference(constantsId);
			scope.setPresentationHint(ScopePresentationHint.REGISTERS);
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