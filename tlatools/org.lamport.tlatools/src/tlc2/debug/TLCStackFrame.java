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

import org.eclipse.lsp4j.debug.Scope;
import org.eclipse.lsp4j.debug.Source;
import org.eclipse.lsp4j.debug.StackFrame;
import org.eclipse.lsp4j.debug.Variable;

import tla2sany.semantic.NumeralNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.st.Location;
import tlc2.tool.EvalControl;
import tlc2.tool.TLCState;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.LazyValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueEnumeration;

class TLCStackFrame extends StackFrame {

	transient final SemanticNode node;
	private transient final Context ctxt;

	transient final Map<Integer, Variable[]> variableValues = new HashMap<>();

	public TLCStackFrame(SemanticNode node, Context ctxt, final Tool tool) {
		this.node = node;
		this.ctxt = ctxt;

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

		final List<Variable> vars = new ArrayList<>();
		Context c = this.ctxt;
		while (c.hasNext()) {
			final Variable variable = new Variable();

			final String name = c.getName().getName().toString();
			variable.setName(name);

			Object val = c.getValue();
			if (val instanceof LazyValue) {
				// unlazy/eval LazyValues
				final LazyValue lv = (LazyValue) c.getValue();
				val = tool.eval(lv.expr, lv.con, TLCState.Empty, null, EvalControl.Debug, lv.getCostModel());
			}
			variable.setValue(val.toString());

			variable.setType(val.getClass().getSimpleName());

			if (val instanceof Value) {
				final Value value = (Value) val;
				if (value.toSetEnum() != null) {
					SetEnumValue setEnum = (SetEnumValue) value.toSetEnum();
					final List<Variable> nestedVars = new ArrayList<>(setEnum.size());
					ValueEnumeration elements = setEnum.elements();
					Value elem;
					while ((elem = elements.nextElement()) != null) {
						final Variable nested = new Variable();
						nested.setName(elem.toString());
						nested.setValue(elem.toString());
						nestedVars.add(nested);
					}
					variableValues.put(Math.abs(setEnum.hashCode()), nestedVars.toArray(new Variable[nestedVars.size()]));
					variable.setVariablesReference(Math.abs(setEnum.hashCode()));
				} else if (value.toFcnRcd() != null) {
					FcnRcdValue fcnRcd = (FcnRcdValue) value.toFcnRcd();
					Value[] values = fcnRcd.getDomainAsValues();
					final List<Variable> nestedVars = new ArrayList<>(values.length);
					for (int i = 0; i < values.length; i++) {
						for (Value v : values) {
							final Variable nested = new Variable();
							nested.setName(values[i].toString());
							nested.setValue(fcnRcd.values[i].toString());
							nested.setType(fcnRcd.values[i].getClass().getSimpleName());
							nestedVars.add(nested);
						}
					}
					variableValues.put(Math.abs(fcnRcd.hashCode()), nestedVars.toArray(new Variable[nestedVars.size()]));
					variable.setVariablesReference(Math.abs(fcnRcd.hashCode()));
				} else if (value.toRcd() != null) {
					RecordValue rcd = (RecordValue) value.toRcd();
					//TODO
				}
			}
			vars.add(variable);

			c = c.next();
		}
		variableValues.put(TLCDebugger.CONTEXT_SCOPE, vars.toArray(new Variable[vars.size()]));
		variableValues.put(TLCDebugger.STACK_SCOPE, new Variable[0]);
	}

	public Variable[] getVariables(final int vr) {
		return variableValues.get(vr);
	}

	public Scope[] getScopes() {

		final List<Scope> scopes = new ArrayList<>();

		if (variableValues.containsKey(TLCDebugger.STACK_SCOPE)) {
			final Scope scope = new Scope();
			scope.setName("Stack");
			scope.setVariablesReference(TLCDebugger.STACK_SCOPE);
			scopes.add(scope);
		}
		if (variableValues.containsKey(TLCDebugger.CONTEXT_SCOPE)) {
			final Scope scope = new Scope();
			scope.setName("Context");
			scope.setVariablesReference(TLCDebugger.CONTEXT_SCOPE);
			scopes.add(scope);
		}

		return scopes.toArray(new Scope[scopes.size()]);
	}
}