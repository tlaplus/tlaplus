/*******************************************************************************
 * Copyright (c) 2025 NVIDIA Corp. All rights reserved. 
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

import tlc2.tool.TLCStateInfo;
import tlc2.tool.impl.Tool;

/**
 * This class represents a stack frame that is not managed by DebugTool in the
 * usual push/pop manner. Instead, instances are manually added to and removed
 * from the debugger’s stack. The class effectively serves as a marker that
 * identifies which stack frames should be removed. It derives from
 * TLCStateStackFrame, although an alternative design would have been to add a
 * marker directly to TLCStateStackFrame itself.
 */
public class TLCSyntheticStateStackFrame extends TLCStateStackFrame {

	public TLCSyntheticStateStackFrame(Tool tool, TLCStateInfo ti, int width) {
		super(null, ti.getAction().pred, ti.getAction().con, tool, ti.state);
		setName(String.format("%0" + width + "d", ti.state.getLevel()) + ": " + ti.info.toString());
	}
}
