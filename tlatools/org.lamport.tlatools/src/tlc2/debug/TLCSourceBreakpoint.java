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

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.st.Location;
import tlc2.tool.impl.SpecProcessor;

public class TLCSourceBreakpoint extends SourceBreakpoint {

	private final int hits;
	private final Location location;
	// Use Getter
	public final OpDefNode condition;
	
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

		// TODO Move condition handling into new subclass of TLCSourceBreakpoint or make
		// ODN = TRUE to not check for null everywhere.
		if (s.getCondition() != null && !s.getCondition().isBlank()) {
			// Use existing definition.
			// TODO Check if level of odn matches level of expression at location.
			final OpDefNode odn = semanticRoot.getOpDef(s.getCondition());
			if (odn != null) {
				condition = odn;
			} else {
				condition = TLCBreakpointExpression.process(processor, semanticRoot, s.getCondition());
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
}
