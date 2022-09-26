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

import java.net.URI;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.CompletableFuture;

import org.eclipse.lsp4j.debug.ContinueResponse;
import org.eclipse.lsp4j.debug.EvaluateArguments;
import org.eclipse.lsp4j.debug.EvaluateResponse;
import org.eclipse.lsp4j.debug.Scope;
import org.eclipse.lsp4j.debug.ScopePresentationHint;
import org.eclipse.lsp4j.debug.Source;
import org.eclipse.lsp4j.debug.StackFrame;
import org.eclipse.lsp4j.debug.StackFramePresentationHint;
import org.eclipse.lsp4j.debug.StoppedEventArguments;
import org.eclipse.lsp4j.debug.StoppedEventArgumentsReason;
import org.eclipse.lsp4j.debug.Variable;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NumeralNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.OpDefOrDeclNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.st.Location;
import tlc2.debug.IDebugTarget.Granularity;
import tlc2.output.EC;
import tlc2.tool.EvalControl;
import tlc2.tool.EvalException;
import tlc2.tool.FingerprintException;
import tlc2.tool.INextStateFunctor.InvariantViolatedException;
import tlc2.tool.TLCState;
import tlc2.tool.impl.SpecProcessor;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.IValue;
import tlc2.value.impl.LazyValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.TLCVariable;
import tlc2.value.impl.Value;
import util.Assert;
import util.Assert.TLCDetailedRuntimeException;
import util.Assert.TLCRuntimeException;
import util.UniqueString;

public class TLCStackFrame extends StackFrame {
	
	// Not thread-safe because TLCDebugger is assumed to take care of synchronization!
	private static final Map<SemanticNode, String> PATH_CACHE = new HashMap<>();

	public static final String EXCEPTION = "Exception";
	public static final String CONSTANTS = "Constants";
	public static final String SCOPE = "Context";
	public static final String STACK = "Stack";
	
	// It would be easier to use hashCode instead of passing a random generator
	// around. However, calculating the hashCode for a TLC value calculates the
	// value's fingerprint, which normalizes and, thus, enumerates the value.
	protected static final Random rnd = new Random();

	protected transient final Map<Integer, DebugTLCVariable> nestedVariables = new HashMap<>();
	protected transient final Map<Integer, List<DebugTLCVariable>> nestedConstants = new HashMap<>();

	protected transient final SemanticNode node;
	protected transient final Context ctxt;
	protected transient final Tool tool;
	protected transient final RuntimeException exception;
	// The Value this SemanticNode evaluated to eventually. null if this node has
	// not been evaluated yet or it doesn't evaluate to a value.
	protected transient Value v;
	// null if this is the root frame, i.e. the start of an evaluation.
	protected transient TLCStackFrame parent;

	protected final int ctxtId;
	
	// Testing only!
	TLCStackFrame(int id) {
		super();
		this.node = null;
		this.ctxt = null;
		this.tool = null;
		this.exception = null;
		this.ctxtId = -1;
		this.setId(id);
	}

	public TLCStackFrame(TLCStackFrame parent, SemanticNode node, Context ctxt, Tool tool, RuntimeException e) {
		this.parent = parent;
		this.tool = tool;
		Assert.check(this.tool != null, EC.GENERAL);
		
		if (e instanceof TLCDetailedRuntimeException) {
			TLCDetailedRuntimeException dre = (TLCDetailedRuntimeException) e;
			this.node = dre.expr;
			this.ctxt = dre.ctxt;
		} else {
			this.node = node;
			// Do not create a deep copy of ctxt (like it is done for state and predecessor
			// in TLCInit|NextStackFrame. A TLCStackFrame will point to its corresponding
			// node in the Context tree even if Context mutates.
			this.ctxt = ctxt; //ctxt.deepCopy();
		}
		Assert.check(this.node != null, EC.GENERAL);
		Assert.check(this.ctxt != null, EC.GENERAL);

		this.exception = e; // e is nullable!

		if (node instanceof NumeralNode) {
			setName(Integer.toString(((NumeralNode)node).val()));
		} else if (e instanceof InvariantViolatedException) {
			setName(String.format("(Invariant) %s", node.getHumanReadableImage()));
			setPresentationHint(StackFramePresentationHint.SUBTLE);
		} else if (e != null) {
			setName(String.format("(Exception) %s", node.getHumanReadableImage()));
			setPresentationHint(StackFramePresentationHint.SUBTLE);
		} else {
			setName(node.getHumanReadableImage());
		}
		// There is a 1:n mapping between SemanticNode and TLCStackFrames. For example,
		// the same SN appears multiple times on the stack in case of recursion. Thus,
		// node.myUID doesn't suffice as a frame's id, which - by definition - has to
		// be unique across all frames.
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
		
		this.ctxtId = rnd.nextInt(Integer.MAX_VALUE - 1) + 1;
	}

	public TLCStackFrame(TLCStackFrame parent, SemanticNode node, Context ctxt, final Tool tool) {
		this(parent, node, ctxt, tool, null);
	}

	protected Variable getStateAsVariable(final IValue value, String varName) {
		final Variable variable = getVariable(value, UniqueString.of(varName));
		// Because we convert the TLCState (getT) to a RecordValue to re-use the
		// getVariable(..) implementation, the type (shown when hovering over the
		// variable in the debugger's variable view) would be RecordValue. This would be
		// bogus and is, thus, corrected to TLCState here.
		//TODO: Is it useful to report the level, action, ... here?
		variable.setType("State");
		return variable;
	}

	private Variable getVariable(final IValue val, final SymbolNode expr) {
		if (!val.hasSource()) {
			// Previously, only CallStack would attach a SymbolNode to the
			// value, which the legacy exception handling in the Value classes
			// relies on (values throw a FingerprintException if a SymbolNode
			// has been attached.
			val.setSource(expr);
		}
		return getVariable(val, expr.getName());
	}

	protected Variable getVariable(final IValue value, String varName) {
		return getVariable(value, UniqueString.of(varName));
	}
	
	protected Variable getVariable(final IValue value, UniqueString varName) {
		DebugTLCVariable variable = (DebugTLCVariable) value.toTLCVariable(new DebugTLCVariable(varName), rnd);
		nestedVariables.put(variable.getVariablesReference(), variable);
		return variable;
	}
	
	protected List<Variable> getStackVariables(final List<Variable> vars) {
		if (this.v != null) {
			Variable variable = getVariable(v, ((SyntaxTreeNode) node.getTreeNode()).getHumanReadableImage());
			// TODO Somehow attach the variable's location too? getHumanReadableImage
			// doesn't correctly create whitespaces, which might be confusing. However, the
			// Toolbox's hover help also shows getHumanReadableImage, which is why fixing it
			// would be desirable.
			if (!vars.contains(variable)) {
				vars.add(variable);
			}
		}
		if (parent != null) {
			return parent.getStackVariables(vars);
		}
		return vars;
	}
	
	protected boolean hasStackVariables() {
		if (this.v != null) {
			return true;
		}
		if (parent != null) {
			return parent.hasStackVariables();
		}
		return false;
	}

	Variable[] getVariables() {
		return getVariables(ctxtId);
	}

	Variable[] getConstants() {
		return getVariables(getConstantsId());
	}
	
	// Keep this for the (legacy) unit-tests that expected the exception to appear
	// in an artificial variable in the variable view.
	Variable[] getExceptionAsVariable() {
		final Variable variable = new Variable();
		variable.setName(getNode().getHumanReadableImage());
		final RuntimeException re = (RuntimeException) exception;
		variable.setValue(re.getMessage());
		variable.setType(re.getClass().getSimpleName()); //TODO Is this useful?
		return new Variable[]{variable};
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

			if (ctxtId == vr) {
				Context c = this.ctxt;
				while (c.hasNext()) {
					Object val = c.getValue();
					if (val instanceof LazyValue) {
						// unlazy/eval LazyValues
						val = unlazy((LazyValue) c.getValue());
					}
					if (val instanceof Value) {
						vars.add(getVariable((Value) val, c.getName()));
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
					} else if (val == null && c.getName() == null) {
						// When evaluating e.g. ENABLED, the context contains
						// tlc2.util.Context.BaseBranch elements for which val and name are null. For
						// now, we simply ignore them.
					} else {
						System.err.println("This is interesting!!! What's this??? " + val);
					}
					c = c.next();
				}
			} else if (getConstantsId() == vr) {
				//TODO: This is evaluated for each TLCStackFrame instance even though the constantDefns
				// never change.  Perhaps, this can be moved to a place where it's only evaluated once.
				// On the other hand, the debug adapter protocol (DAP) might not like sharing
				// DebugTLCVariables.
				getConstants(vars);
			} else if (getStackId() == vr) {
				// Intentionally not sorting lexicographically because the order given by the
				// stack is probably more useful.
				final List<Variable> pVars = getStackVariables(new ArrayList<>());
				return pVars.toArray(Variable[]::new); 
			}
			return toSortedDistinctArray(vars);
		});
	}

	private void getConstants(final List<Variable> vars) {
		final SpecProcessor sp = this.tool.getSpecProcessor();
		final Map<ModuleNode, Map<OpDefOrDeclNode, Object>> constantDefns = sp.getConstantDefns();
			for (final Entry<ModuleNode, Map<OpDefOrDeclNode, Object>> e : constantDefns.entrySet()) {
				if (constantDefns.size() == 1) {
					// If there is only one module, do *not* organize the constants in the variable
					// view by modules. In other words, constants get moved up by one level in the
					// variable view iff there is only one module.
					e.getValue().entrySet().stream().map(c -> getVariable((Value) c.getValue(), c.getKey().getName()))
							.forEach(var -> vars.add(var));
				} else {
					final ModuleNode module = e.getKey();
					
					final Variable v = new Variable();
					// Pick one of the OpDefNode and derive the name with which the definition
					// appears in the spec, i.e. A!B!C!Op -> A!B!C.  Users then see the module
					// name and instance path that appears in the instantiating module. getPathName
					// equals the empty (unique) string if the module has no path.
					v.setValue(e.getValue().keySet().stream().filter(OpDefNode.class::isInstance)
							.map(OpDefNode.class::cast).map(OpDefNode::getPathName).findAny()
							.orElse(UniqueString.of(module.getSignature())).toString());
					v.setName(module.getSignature());
					v.setVariablesReference(rnd.nextInt(Integer.MAX_VALUE - 1) + 1);
					vars.add(v);
					
					final List<DebugTLCVariable> l = new ArrayList<>();
					final Set<Entry<OpDefOrDeclNode,Object>> entrySet = e.getValue().entrySet();
					for (Entry<OpDefOrDeclNode, Object> entry : entrySet) {
						final OpDefOrDeclNode oddn = entry.getKey();
						final Object value = entry.getValue();
						if (oddn instanceof OpDefNode) {
							final OpDefNode odn = (OpDefNode) oddn;
							l.add((DebugTLCVariable) ((Value) value)
									.toTLCVariable(new DebugTLCVariable(odn.getLocalName()), rnd));
						} else {
							final OpDeclNode odn = (OpDeclNode) oddn;
							l.add((DebugTLCVariable) ((Value) value)
									.toTLCVariable(new DebugTLCVariable(odn.getSignature()), rnd));
						}
					}
					nestedConstants.put(v.getVariablesReference(), l);
				}
			}
	}
	
	protected Variable[] toSortedDistinctArray(final List<Variable> vars) {
		// Its nicer if variables/constants are sorted lexicographically, and
		// duplicates removed.
		final Set<Variable> s = new TreeSet<>(new Comparator<Variable>() {
			@SuppressWarnings("unchecked")
			@Override
			public int compare(Variable o1, Variable o2) {
				if (o1 instanceof Comparable && o2 instanceof Comparable) {
					return ((Comparable<Variable>) o1).compareTo(o2);
				}
				return o1.getName().compareTo(o2.getName());
			}
		});
		s.addAll(vars);
		return s.toArray(Variable[]::new);
	}
	
	protected Variable getVariable(final LinkedList<SemanticNode> path) {
		assert !path.isEmpty();
		
		SemanticNode sn = path.getFirst();
		Object o;
		if (sn instanceof SymbolNode) {
			o = tool.lookup((SymbolNode) sn, this.ctxt, false);
		} else if (sn instanceof ExprOrOpArgNode) {
			o = tool.getVal((ExprOrOpArgNode) sn, ctxt, false);
		} else {
			o = sn;
		}
		
		if (o instanceof LazyValue) {
			// Unlazying might fail if the lazy value is not within the scope of this frame.
			// In this case, fall-back to sn.
			o = unlazy((LazyValue) o, o);
		}
		
		final Variable variable;
		if (o instanceof Value) {
			variable = getVariable((IValue) o, sn.getHumanReadableImage());
			variable.setType(((Value) o).getTypeString());
		} else {
			variable = new Variable();
			variable.setValue(
					// Print the location for built-in symbols instead of "-- TLA Builtin ---"
					o instanceof SymbolNode && ((SymbolNode) o).isBuiltIn() ? ((SymbolNode) o).getLocation().toString()
							: o.toString());
			variable.setType(o.getClass().getSimpleName());
		}
		return variable;
	}

	public EvaluateResponse get(final EvaluateArguments ea) {
		// Lets assume a module R that extends B, which in turn instantiates module A,
		// i.e., R e> B i> A where "e>" denotes extends and "i>" denotes
		// instantiation.
		// For two constants c defined in A and B, and foo defined in R, the DAP variable
		// view shows a high-level "Constants" and a sub-node for A, B, and R, respectively:
		//
		// Constant
		// - A
		// -- c
		// - B
		// -- c
		// - R
		// -- foo
		// -- ...
		//
		// A user might hover of the occurrence of constant c in R, which should be evaluated
		// to the value of B!c.  She might also hover over the occurrence of I!c in R, assuming
		// an named instantiation, i.e. I == INSTANCE A occurring in B.  If she opens module A,
		// hovering over c should also show the value of A!c.  Hovering of c in B, on the other
		// hand, has to show the value of B!c.
		//
		// Unless TLCDebugger declares the capability "EvaluateForHovers" [0], DAP uses a
		// basic lookup mechanism that looks for symbols in the set of variables from which DAP
		// populated its variables view.  This mechanism fails to resolve a symbol if it appears
		// multiple times such as c above.  It also fails to handle the case of variables appearing
		// in sub-nodes such as R.  That is, it doesn't not resolve foo because foo is one level
		// too deep in the tree.  In other words, the lookup mechanism is coupled to how the view
		// presents the data.  To address these issues, TLCDebugger declares the capability
		// "EvaluateForHovers" and resolves variables manually.
		// DAP does not provide the current (hovering) location (file, start/end line & column) as
		// structured data [1].  Instead, we encode the location into the expression of
		// EvaluateArguments as suggested privately by Andre Weinand of the VSCode team and
		// partially demonstrated by vscode-mock-debug [2].
		// 
		//
		// [0] https://microsoft.github.io/debug-adapter-protocol/specification#Requests_Evaluate
		// [1] https://github.com/microsoft/vscode/issues/89084
		// [2] https://github.com/microsoft/vscode-mock-debug/commit/27539c78c25aa316be6aa1ee03bfd1e87bf7faad#diff-04bba6a35cad1c794cbbe677678a51de13441b7a6ee8592b7b50be1f05c6f626

		// Encode this file, token, and range into a URI with which parsing becomes a
		// no-brainer but some might consider over-engineered, oh well...
		// tlaplus:///home/markus/foo/bar.tla?A!c#4 3 1 2
		final EvaluateResponse er = new EvaluateResponse();
		try {
			final URI u = URI.create(ea.getExpression());
			// Unfortunately, we have to manually strip the extension because the lookup
			// later is going to be on the module, not the file name.
			final String moduleName = Paths.get(u.getPath()).getFileName().toString().replaceAll(".tla$", "");

			final Location location = Location.parseCoordinates(moduleName, u.getFragment());
			final LinkedList<SemanticNode> path = tool.getModule(location.source()).pathTo(location);
			if (path.isEmpty()) {
				// Can be resolved to something. If not, the user hovered over something like a comment.
				er.setResult(location.toString());
				return er;
			}
			final Variable v = getVariable(path);
			if (v != null) {
				// Can be resolved to something. If not, the user hovered over something like a comment.
				er.setResult(v.getValue());
				er.setType(v.getType());
				er.setVariablesReference(v.getVariablesReference());
			}
			
			return er;
		} catch (IllegalArgumentException e) {
			return er;
		}
	}
	
	protected TLCState getS() {
		return TLCState.Empty;
	}
	
	protected TLCState getT() {
		return TLCState.Empty;
	}

	public EvaluateResponse getWatch(final String name) {
		if (name == null) {
			return new EvaluateResponse();
		} 
		final ModuleNode module = tool.getSpecProcessor().getRootModule();
		return getWatch(module.getOpDef(name));
	}

	public EvaluateResponse getWatch(final OpDefNode odn) {
		if (odn == null) {
			return new EvaluateResponse();
		} 

		Variable variable;
		try {
			variable = tool.eval(() -> {
				return getVariable(tool.eval(odn.getBody(), getContext(), getS(), getT(), EvalControl.Clear),
						odn.getName());
			});
		} catch (TLCRuntimeException | EvalException | FingerprintException e) {
			variable = getVariable(new StringValue(e.getMessage() == null ? "" : e.getMessage()), odn.getName());
		}

		final EvaluateResponse er = new EvaluateResponse();
		er.setResult(variable.getValue());
		er.setVariablesReference(variable.getVariablesReference());
		return er;
	}
	
	protected Object unlazy(final LazyValue lv) {
		return unlazy(lv, null);
	}

	protected Object unlazy(final LazyValue lv, final Object fallback) {
		try {
			return tool.eval(() -> {
				return lv.eval(tool);
			});
		} catch (TLCRuntimeException | EvalException | FingerprintException e) {
			return fallback == null ? e : fallback;
		}
	}

	public Scope[] getScopes() {
		final List<Scope> scopes = new ArrayList<>();
		
		if (!ctxt.isEmpty()) {
			final Scope scope = new Scope();
			scope.setName(SCOPE);
			scope.setVariablesReference(ctxtId);
			scopes.add(scope);
		}
		
		if (!this.tool.getSpecProcessor().getConstantDefns().isEmpty()) {
			final Scope scope = new Scope();
			scope.setName(CONSTANTS);
			scope.setVariablesReference(getConstantsId());
			scope.setPresentationHint(ScopePresentationHint.REGISTERS);
			scopes.add(scope);
		}
		
		if (hasStackVariables()) {
			final Scope scope = new Scope();
			scope.setName(STACK);
			scope.setVariablesReference(getStackId());
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

	public boolean hasException() {
		return exception != null;
	}
	
	public Exception getException() {
		return exception;
	}

	@Override
	public String toString() {
		return "TLCStackFrame [node=" + node + "]";
	}

	public Value setValue(Value v) {
		assert this.v == null;
		this.v = v;
		return v;
	}
	
	public int getConstantsId() {
		return this.ctxtId + 1;
	}
	
	public int getStackId() {
		return this.ctxtId + 3;
	}

	public StoppedEventArguments getStoppedEventArgument() {
		final StoppedEventArguments eventArguments = new StoppedEventArguments();
		if (this.exception != null) {
			// The DAP does not have anything besides "exception" that would be useful, ie.
			// show something meaningful in the front-end, when an invariant is violated.
			// Thus, we have to use the visualization that comes with exception, even though
			// the term "exception" appears in the front-end.
			eventArguments.setReason(StoppedEventArgumentsReason.EXCEPTION);
			eventArguments.setText(this.exception.getMessage().replaceAll("(?m)^@!@!@.*", ""));
		}
		return eventArguments;
	}

	public boolean matches(final TLCSourceBreakpoint bp) {
		// TODO: For const-level expression (TLCStackFrame),
		// TLCSourceBreakpoint#getHits() should have the traditional meaning. Question
		// is, where do we keep the hit count. A user would select the meaning by
		// passing e.g. TLCGet("level") > 3 as the hit condition for state-level and a
		// simple integer for const-level.
		return bp.getLine() == node.getLocation().beginLine()
				//TODO why *smaller* than BEGINcolumn?
				&& bp.getColumnAsInt() <= node.getLocation().beginColumn();
	}

    boolean matches(SemanticNode expr, RuntimeException e) {
		return node == expr || (e instanceof TLCDetailedRuntimeException && ((TLCDetailedRuntimeException)e).expr == node);
	}

	public boolean matches(SemanticNode expr) {
		return node == expr;
	}

	public boolean isTarget(SemanticNode expr) {
		return node == expr;
	}

	public void postHalt(final TLCDebugger tlcDebugger) {
		// no-op; sub-classes may override.
	}

	public void preHalt(final TLCDebugger tlcDebugger) {
		// no-op; sub-classes may override.
	}

	public CompletableFuture<Void> stepOut(final TLCDebugger debugger) {
		debugger.setGranularity(Granularity.Formula);
		debugger.notify();
		return CompletableFuture.completedFuture(null);
	}

	public CompletableFuture<Void> stepIn(final TLCDebugger debugger) {
		debugger.setGranularity(Granularity.Formula);
		debugger.notify();
		return CompletableFuture.completedFuture(null);
	}

	public CompletableFuture<Void> stepOver(final TLCDebugger debugger) {
		debugger.setGranularity(Granularity.Formula);
		debugger.notify();
		return CompletableFuture.completedFuture(null);
	}

	public CompletableFuture<ContinueResponse> continue_(final TLCDebugger debugger) {
		debugger.setGranularity(Granularity.Formula);
		debugger.notify();
		return CompletableFuture.completedFuture(new ContinueResponse());
	}

	public CompletableFuture<Void> reverseContinue(final TLCDebugger debugger) {
		debugger.setGranularity(Granularity.Formula);
		debugger.notify();
		return CompletableFuture.completedFuture(null);
	}

	public CompletableFuture<Void> stepBack(final TLCDebugger debugger) {
		debugger.setGranularity(Granularity.Formula);
		debugger.notify();
		return CompletableFuture.completedFuture(null);
	}

	public boolean handle(final TLCDebugger debugger) {
		return false;
	}
}