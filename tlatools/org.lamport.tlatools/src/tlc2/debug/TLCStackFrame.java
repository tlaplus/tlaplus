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

import java.io.File;
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
	
	// It would be easier to use hashCode instead of passing a random generator
	// around. However, calculating the hashCode for a TLC value calculates the
	// value's fingerprint, which normalizes and, thus, enumerates the value.
	private static final Random rnd = new Random();

	private transient final Map<Integer, DebugTLCVariable> nestedVariables = new HashMap<>();

	private transient final SemanticNode node;
	private transient final Context ctxt;
	private transient final Tool tool;

	public TLCStackFrame(SemanticNode node, Context ctxt, final Tool tool) {
		this.node = node;
		Assert.check(node != null, EC.GENERAL);
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
		final File moduleFile = tool.getResolver().resolve(node.getTreeNode().getFilename(), true);
		source.setPath(moduleFile.getAbsolutePath().toString());
		setSource(source);
	}

	public Variable[] getVariables(final int vr) {
		if (nestedVariables.containsKey(vr)) {
			DebugTLCVariable[] nested = nestedVariables.get(vr).getNested(rnd);
			for (DebugTLCVariable debugTLCVariable : nested) {
				nestedVariables.put(debugTLCVariable.getVariablesReference(), debugTLCVariable);
			}
			return nested;
		}

		final List<Variable> vars = new ArrayList<>();
		if (ctxt.hashCode() == vr) {
			Context c = this.ctxt;
			while (c.hasNext()) {
				Object val = c.getValue();
				if (val instanceof LazyValue) {
					// unlazy/eval LazyValues
					val = ((LazyValue) c.getValue()).eval(tool); // Do not pass EvalControl.Debug here because we don't
																	// want to debug the un-lazying the value.
				}
				if (val instanceof Value) {
					final Value value = (Value) val;
					final DebugTLCVariable variable = (DebugTLCVariable) value
							.toTLCVariable(new DebugTLCVariable(c.getName().getName().toString()), rnd);
					nestedVariables.put(variable.getVariablesReference(), variable);
					vars.add(variable);
				} else {
					System.err.println("This is interesting!!! What's this??? " + val.toString());
				}
				c = c.next();
			}
		}
		return vars.toArray(new Variable[vars.size()]);
	}

	public Scope[] getScopes() {
		final List<Scope> scopes = new ArrayList<>();
		
		if (!ctxt.isEmpty()) {
			final Scope scope = new Scope();
			scope.setName("Context");
			scope.setVariablesReference(ctxt.hashCode());
			scopes.add(scope);
		}
		return scopes.toArray(new Scope[scopes.size()]);
	}
	
	public SemanticNode getNode() {
		return node;
	}
}