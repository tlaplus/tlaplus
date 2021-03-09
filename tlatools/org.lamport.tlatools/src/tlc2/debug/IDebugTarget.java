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

import tla2sany.semantic.SemanticNode;
import tlc2.tool.Action;
import tlc2.tool.TLCState;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.impl.Value;

public interface IDebugTarget {

	public enum Step {
		In, Out, Over, Continue
	};

	IDebugTarget pushFrame(Tool tool, SemanticNode expr, Context c);
	
	IDebugTarget popFrame(Tool tool, SemanticNode expr, Context c);
	
	IDebugTarget popFrame(Tool tool, SemanticNode expr, Context c, Value v);

	IDebugTarget popFrame(Tool tool, SemanticNode expr, Context c, TLCState state);

	IDebugTarget popFrame(Tool tool, SemanticNode expr, Context c, Value v, TLCState state);

	IDebugTarget pushFrame(Tool tool, SemanticNode expr, Context c, TLCState state);

	IDebugTarget pushFrame(Tool tool, SemanticNode expr, Context c, TLCState predecessor, Action a, TLCState state);

	IDebugTarget popFrame(Tool tool, SemanticNode expr, Context c, TLCState predecessor, TLCState state);

	IDebugTarget popFrame(Tool tool, SemanticNode expr, Context c, Value v, TLCState predecessor, TLCState state);

	// No popExceptionFrame because TLC cannot recover from an exception!
	IDebugTarget pushExceptionFrame(Tool tool, SemanticNode expr, Context c, RuntimeException e);

	IDebugTarget pushExceptionFrame(Tool tool, SemanticNode expr, Context c, TLCState state, RuntimeException e);

	IDebugTarget pushExceptionFrame(Tool tool, SemanticNode expr, Context c, TLCState predecessor, Action a, TLCState state,
			RuntimeException e);

	//------------------------ Wrapper --------------------------//
	
	IDebugTarget pushFrame(TLCState state);
	
	IDebugTarget popFrame(TLCState state);

	IDebugTarget pushFrame(TLCState predecessor, Action a, TLCState state);
	
	IDebugTarget popFrame(TLCState predecessor, TLCState state);

	IDebugTarget setTool(Tool tool);
}
