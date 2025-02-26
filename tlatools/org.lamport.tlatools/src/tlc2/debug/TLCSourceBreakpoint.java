/*******************************************************************************
 * Copyright (c) 2021 Microsoft Research. All rights reserved. 
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

import org.eclipse.lsp4j.debug.SourceBreakpoint;

import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.st.Location;
import tlc2.tool.EvalControl;
import tlc2.tool.EvalException;
import tlc2.tool.FingerprintException;
import tlc2.tool.TLCState;
import tlc2.tool.impl.SpecProcessor;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.IValue;
import tlc2.value.impl.BoolValue;
import util.Assert.TLCRuntimeException;

public class TLCSourceBreakpoint extends SourceBreakpoint {

	private final int hits;
	private final Location location;
	private final OpDefNode condition;
	
	public TLCSourceBreakpoint(final SpecProcessor processor, final String module, final SourceBreakpoint s,
			final ModuleNode semanticRoot) {
		setColumn(s.getColumn());
		setLine(s.getLine());
		// Create a location that's not a point.
		final int column = getColumn() != null ? getColumn() : 1;
		//TODO: If the location spans lines, getLine() + 1 should be the endline (second line parameter of Location).
		location = new Location(module, getLine() + 1, column, getLine(), column + 1);
		
		setCondition(s.getCondition());
		setLogMessage(s.getLogMessage());
		
		setHitCondition(s.getHitCondition());
		// Try to convert the input string that can be anything into a integer.
		int h = 0;
		if (getHitCondition() != null) {
			try {
				h = Integer.parseInt(getHitCondition());
			} catch (NumberFormatException nfe) {
			}
		}
		hits = h;

		if (s.getCondition() != null && !s.getCondition().isBlank()) {
			// TODO Check if level of odn matches level of expression at location.
			final OpDefNode odn = semanticRoot.getOpDef(s.getCondition());
			if (odn != null) {
				// Use existing definition.
				condition = odn;
			} else {
				condition = TLCDebuggerExpression.process(processor, semanticRoot, location, s.getCondition());
			}
		} else {
			condition = null;
		}
	}

	public int getHits() {
		return hits;
	}
	
	public boolean isInline() {
		return getColumnAsInt() == -1;
	}
	
	public int getColumnAsInt() {
		if (this.getColumn() != null) {
			return this.getColumn();
		}
		return -1;
	}

	public Location getLocation() {
		return location;
	}
	
	protected boolean matchesExpression(final Tool tool, final TLCState s, final TLCState t, final Context c,
			boolean fire) {
		if (condition != null) {
			// Wrap in tool.eval(() -> to evaluate the debug expression *outside* of the
			// debugger. In that case, we would have to handle the exceptions below.
//			fire = tool.eval(() -> {
				try {					
					// Create the debug expression's context from the stack frame's context.
					// Best effort as lookup is purely syntactic on UniqueString!
					Context ctxt = Context.Empty;
					for (FormalParamNode p : condition.getParams()) {
						ctxt = ctxt.cons(p, c.lookup(sn -> sn.getName().equals(p.getName())));
					}
					
					final IValue eval = tool.noDebug().eval(condition.getBody(), ctxt, s, t, EvalControl.Clear);
					if (eval instanceof BoolValue) {
//						return 
								fire &= ((BoolValue) eval).val;
					}
				} catch (TLCRuntimeException | EvalException | FingerprintException e) {
					// TODO DAP spec not clear on how to handle an evaluation failure of a debug
					// expression. Given our limitation that debug expressions have to be defined in
					// the spec, the same error will be raised like for any other broken expression
					// in the spec. In other words, a user may use the debugger to debug a debug
					// expression.
					
					// Swallow the exception to make TLC continue instead of crash.
				}
//				return false;
//			});
		}
		return fire;
	}

	public boolean matchesLocation(final Location loc) {
		return getLine() == loc.beginLine()
				//TODO why *smaller* than BEGINcolumn?
				&& getColumnAsInt() <= loc.beginColumn();
	}
}
