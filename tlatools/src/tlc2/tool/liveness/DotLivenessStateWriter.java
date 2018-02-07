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
package tlc2.tool.liveness;

import java.io.IOException;

import tlc2.tool.TLCState;
import tlc2.util.BitVector;
import tlc2.util.DotStateWriter;
import tlc2.util.IStateWriter;

public class DotLivenessStateWriter extends DotStateWriter implements ILivenessStateWriter {
	
	public DotLivenessStateWriter(IStateWriter aStateWriter) throws IOException {
		super(aStateWriter.getDumpFileName().replace(".dot", "_liveness.dot"), "");
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILivenessStateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.liveness.TBGraphNode)
	 */
	public void writeState(TLCState state, TBGraphNode tableauNode) {
		
		// Marker the state as an initial state by using a filled style.
		this.writer.append("\"");
		this.writer.append(Long.toString(state.fingerPrint()));
		this.writer.append(".");
		this.writer.append(Integer.toString(tableauNode.getIndex()));
		this.writer.append("\"");
		this.writer.append(" [style = filled]");
		this.writer.append(" [label=\"");
		this.writer.append(states2dot(state));
		this.writer.append("\n#" + Long.toString(state.fingerPrint()) + "."
				+ tableauNode.getIndex() + "#");
		this.writer.append("\"]");
		this.writer.append("\n");
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILivenessStateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.liveness.TBGraphNode, tlc2.tool.TLCState, tlc2.tool.liveness.TBGraphNode, boolean)
	 */
	public void writeState(TLCState state, TBGraphNode tableauNode, TLCState successor,
			TBGraphNode tableauNodeSuccessor, BitVector actionChecks, int from, int length, boolean successorStateIsNew) {
		writeState(state, tableauNode, successor, tableauNodeSuccessor, actionChecks, from, length, successorStateIsNew, Visualization.DEFAULT);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILivenessStateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.liveness.TBGraphNode, tlc2.tool.TLCState, tlc2.tool.liveness.TBGraphNode, boolean, tlc2.util.IStateWriter.Visualization)
	 */
	public void writeState(TLCState state, TBGraphNode tableauNode, TLCState successor,
			TBGraphNode tableauNodeSuccessor, BitVector actionChecks, int from, int length, boolean successorStateIsNew, Visualization visualization) {

		final String successorsFP = Long.toString(successor.fingerPrint());

		// Write the transition
		this.writer.append("\"");
		this.writer.append(Long.toString(state.fingerPrint()));
		this.writer.append(".");
		this.writer.append(Integer.toString(tableauNode.getIndex()));
		this.writer.append("\"");
		this.writer.append(" -> ");
		this.writer.append("\"");
		this.writer.append(successorsFP);
		this.writer.append(".");
		this.writer.append(Integer.toString(tableauNodeSuccessor.getIndex()));
		this.writer.append("\"");
		if (visualization == Visualization.STUTTERING) {
			this.writer.append(" [style=\"dashed\"]");
		}
		if (visualization == Visualization.DOTTED) {
			this.writer.append(" [style=\"dotted\"]");
		}
		if (length > 0) {
			this.writer.append(" [label=\"" + actionChecks.toString(from, length, 't', 'f') + "\"]");
		}
		this.writer.append(";\n");

		// If the successor is new, print the state's label. Labels are printed
		// when writeState sees the successor. It does not print the label for
		// the current state. If it would print the label for the current state,
		// the init state labels would be printed twice.
		if (successorStateIsNew) {
			// Write the successor's label
			this.writer.append("\"");
			this.writer.append(successorsFP);
			this.writer.append(".");
			this.writer.append(Integer.toString(tableauNodeSuccessor.getIndex()));
			this.writer.append("\"");
			this.writer.append(" [label=\"");
			this.writer.append(states2dot(successor));
			this.writer.append(
					"\n#" + Long.toString(successor.fingerPrint()) + "."
							+ tableauNodeSuccessor.getIndex() + "#");
			this.writer.append("\"]");
			this.writer.append(";\n");
		}
	}

	protected static String tableauNode2dot(final TBGraphNode tableauNode) {
		// Replace "\" with "\\" and """ with "\"".	
		return tableauNode.toString().replace("\\", "\\\\").replace("\"", "\\\"").trim();
	}
}
