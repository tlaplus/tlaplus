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

import tla2sany.st.Location;

public class TLCSourceBreakpoint extends SourceBreakpoint {

	private final int hits;
	private final Location location;
	
	public TLCSourceBreakpoint(final String module, final SourceBreakpoint s) {
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
