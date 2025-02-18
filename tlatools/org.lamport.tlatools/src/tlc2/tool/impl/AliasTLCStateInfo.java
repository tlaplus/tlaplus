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
package tlc2.tool.impl;

import tlc2.tool.Action;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateInfo;

public class AliasTLCStateInfo extends TLCStateInfo {

	private final TLCState originalState;

	public AliasTLCStateInfo(TLCState alias, TLCStateInfo current) {
		super(alias, current);
		originalState = current.state;
	}
	  
	@Override
	public int getStateNumber() {
		return originalState.getLevel();
	}

	@Override
	public Action getAction() {
		if (originalState.hasAction()) {
			// originalState could be a TLCStateMut, which has no action.
			return originalState.getAction();
		}
		return super.getAction();
	}

	@Override
	public TLCState getOriginalState() {
		return originalState;
	}
}
