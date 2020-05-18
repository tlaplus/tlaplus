/*******************************************************************************
 * Copyright (c) 2016 Microsoft Research. All rights reserved. 
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
package tlc2.util;

import java.io.IOException;

import tlc2.tool.Action;
import tlc2.tool.TLCState;

public final class NoopStateWriter implements IStateWriter {

	/* (non-Javadoc)
	 * @see tlc2.util.StateWriter#writeState(tlc2.tool.TLCState)
	 */
	public final void writeState(final TLCState state) {
		// noop
	}

	/* (non-Javadoc)
	 * @see tlc2.util.StateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.TLCState, boolean)
	 */
	public final void writeState(final TLCState state, final TLCState successor, final boolean successorStateIsNew) {
		// noop
	}

	/* (non-Javadoc)
	 * @see tlc2.util.IStateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.TLCState, boolean, tlc2.util.IStateWriter.Visualization)
	 */
	public void writeState(TLCState state, TLCState successor, boolean successorStateIsNew, Visualization visualization) {
		// noop
	}

	/* (non-Javadoc)
	 * @see tlc2.util.IStateWriter#close()
	 */
	public final void close() {
		// noop
	}

	/* (non-Javadoc)
	 * @see tlc2.util.IStateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.TLCState, tlc2.util.BitVector, int, int, boolean)
	 */
	public void writeState(TLCState state, TLCState successor, BitVector actionChecks, int from, int to, boolean successorStateIsNew) {
		// noop
	}

	/* (non-Javadoc)
	 * @see tlc2.util.IStateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.TLCState, tlc2.util.BitVector, int, int, boolean, tlc2.util.IStateWriter.Visualization)
	 */
	public void writeState(TLCState state, TLCState successor, BitVector actionChecks, int from, int to, boolean successorStateIsNew,
			Visualization visualization) {
		// noop
	}

	/* (non-Javadoc)
	 * @see tlc2.util.IStateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.TLCState, boolean, tlc2.tool.Action)
	 */
	public void writeState(TLCState state, TLCState successor, boolean successorStateIsNew, Action action) {
		// noop
	}

	/* (non-Javadoc)
	 * @see tlc2.util.IStateWriter#isNoop()
	 */
	public boolean isNoop() {
		return true;
	}

	/* (non-Javadoc)
	 * @see tlc2.util.IStateWriter#isDot()
	 */
	@Override
	public boolean isDot() {
		return false;
	}
		
	/* (non-Javadoc)
	 * @see tlc2.util.IStateWriter#getDumpFileName()
	 */
	public String getDumpFileName() {
		return "";
	}

	/* (non-Javadoc)
	 * @see tlc2.util.IStateWriter#snapshot()
	 */
	@Override
	public void snapshot() throws IOException {
	}
}
