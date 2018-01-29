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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import tlc2.tool.Action;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateMut;
import tlc2.tool.TLCStateMutSource;
import tlc2.value.Value;
import util.UniqueString;

/**
 * Writes the given state in dot notation.
 * 
 * @see https://en.wikipedia.org/wiki/DOT_(graph_description_language)
 */
public class DotStateWriter extends StateWriter {

	// Used for assigning unique color identifiers to each action type.
	Integer colorGen = 1;
	HashMap<String, Integer> actionToColors = new HashMap<>();
	static String dotColorScheme = "paired12";
	
	public DotStateWriter(final String fname) throws IOException {
		this(fname, "strict ");
	}
	
	public DotStateWriter(final String fname, final String strict) throws IOException {
		super(fname);
		this.writer.append(strict + "digraph DiskGraph {\n"); // strict removes redundant edges
		// Turned off LR because top to bottom provides better results with GraphViz viewer.
//		this.writer.append("rankdir=LR;\n"); // Left to right rather than top to bottom
        this.writer.append(String.format("edge [colorscheme=\"%s\"]\n", dotColorScheme));
        // Spread out state nodes more.
        this.writer.append("nodesep=0.35;\n");
//        this.writer.append("ranksep=0.85;\n");
		this.writer.append("subgraph cluster_graph {\n"); 
        this.writer.append("color=\"white\";\n"); //no border.
		this.writer.flush();
	}

	/* (non-Javadoc)
	 * @see tlc2.util.StateWriter#writeState(tlc2.tool.TLCState)
	 */
	public synchronized void writeState(final TLCState state) {
		// Marker the state as an initial state by using a filled style.
		this.writer.append(Long.toString(state.fingerPrint()));
		this.writer.append(" [style = filled]");
		this.writer.append(" [label=<");
		this.writer.append(stateToDotStr(state, state));
		this.writer.append(">]");
		this.writer.append("\n");
//		this.writer.append(dotLegend("Legend", new ArrayList<String>()));
	}
	
	/* (non-Javadoc)
	 * @see tlc2.util.StateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.TLCState, boolean)
	 */
	public synchronized void writeState(TLCState state, TLCState successor, boolean successorStateIsNew) {
		writeState(state, successor, successorStateIsNew, Visualization.DEFAULT);
	}
	
    public synchronized void writeState(final TLCState state, final TLCState successor, final boolean successorStateIsNew, Action action)
    {
		writeState(state, successor, null, 0, 0, successorStateIsNew, Visualization.DEFAULT, action);
    }
	
	/* (non-Javadoc)
	 * @see tlc2.util.StateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.TLCState, boolean, tlc2.util.IStateWriter.Visualization)
	 */
	public synchronized void writeState(TLCState state, TLCState successor, boolean successorStateIsNew, Visualization visualization) {
		writeState(state, successor, null, 0, 0, successorStateIsNew, visualization, null);
	}

	/* (non-Javadoc)
	 * @see tlc2.util.StateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.TLCState, tlc2.util.BitVector, int, int, boolean)
	 */
	public synchronized void writeState(TLCState state, TLCState successor, BitVector actionChecks, int from, int length, boolean successorStateIsNew) {
		writeState(state, successor, actionChecks, from, length, successorStateIsNew, Visualization.DEFAULT, null);
	}

	/* (non-Javadoc)
	 * @see tlc2.util.StateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.TLCState, java.lang.String, boolean, tlc2.util.IStateWriter.Visualization)
	 */
	public synchronized void writeState(TLCState state, TLCState successor, BitVector actionChecks, int from, int length, boolean successorStateIsNew,
			Visualization visualization, Action action) {
		final String successorsFP = Long.toString(successor.fingerPrint());
		
		// Write the transition edge.
		this.writer.append(Long.toString(state.fingerPrint()));
		this.writer.append(" -> ");
		this.writer.append(successorsFP);
		if (visualization == Visualization.STUTTERING) {
			this.writer.append(" [style=\"dashed\"]");
		}
		
		// Add the transition edge label. Omit if there are no actions.	
		if (length > 0) { 
//			this.writer.append(" [label=\"" + actionChecks.toString(from, length, 't', 'f') + "\"]");
		}
		
		String transitionLabel = this.dotTransitionLabel(state, successor, action);
		this.writer.append(transitionLabel);
		
		// If the successor is new, print the state's label. Labels are printed
		// when writeState sees the successor. It does not print the label for
		// the current state. If it would print the label for the current state,
		// the init state labels would be printed twice.
		if (successorStateIsNew) {
			// Write the successor's label.
			this.writer.append(successorsFP);
			this.writer.append(" [label=<");
			String stateStr = stateToDotStr(state, successor);
			this.writer.append(stateStr);
			this.writer.append(">]");
			this.writer.append(";\n");
		}
		

	}
	
	protected String dotTransitionLabel(TLCState state, TLCState successor, Action action) {
		StringBuilder sb = new StringBuilder();
		sb.append(" [label=<");
		sb.append("<table border='0' cellborder='0' cellspacing='0'>");
	    sb.append("<tr>");
	    Integer color = 0;
	    if(action!=null) {
	    		String actionName = action.getActionName();
	    		if(actionToColors.containsKey(actionName)) {
	    			color = actionToColors.get(actionName);
	    		} else {
	    			// Get the next color and use it for this action.
	    			this.colorGen++;
	    			color = this.colorGen;
	    			actionToColors.put(actionName, color);
	    		}
	    		sb.append("<td bgcolor='white' color='red'>");
			sb.append("<font point-size='12'" + " color=\"" + color + "\">" + actionName + "</font>");
			sb.append("</td>");
	    }
	    sb.append("</tr>");

		// Print names of variables that changed in this transition.
//	    sb.append("<tr>");
//		sb.append("<td bgcolor='white'><font color='#222222' point-size='9'>");
//		sb.append("(");
//		HashMap<UniqueString, Value> diffMap = state.diff(successor);
//		ArrayList<String> changedVars = new ArrayList<>();
//		for(UniqueString key : diffMap.keySet()) {
//			changedVars.add(key.toString());
//			sb.append(key.toString());
//			sb.append("<br/>");
//		}
//		sb.append(String.join("\n", changedVars));
//		sb.append(")");
//		sb.append("</font>");
//		sb.append("</td>");
//		sb.append("</tr>");
	    
	    
		sb.append("</table>");
		sb.append(">");
		sb.append(" labeldistance=\"4\" color=\"" + color +"\"]");
		
		return sb.toString();
	}
	
	
	/** 
	 * Return a DOT string that contains a legend describing the map of actions to their corresponding color.
	 */
	protected String dotLegend(String name, Set<String> actions) {
		StringBuilder sb = new StringBuilder();
		sb.append(String.format("subgraph %s {", "cluster_legend"));
		sb.append("graph[style=bold];");
		sb.append(String.format("node [ labeljust=\"l\" colorscheme=\"%s\" style=filled shape=record ]\n", dotColorScheme));
        sb.append("label = \"Transition Action Legend\" style=\"solid\"\n");
        sb.append(String.format("colorscheme=\"%s\"\n", dotColorScheme));
        int i=1;
        for(String action: actions) {
        		String str = String.format("%s [label=\"%s\" fillcolor=%d]", action, action, this.actionToColors.get(action));
    			sb.append(str);
    			sb.append("\n");
        }
		sb.append("}");
		return sb.toString();
	}
	
	protected static String stateToDotStr(TLCState state, TLCState successor) {		
		StringBuilder sb = new StringBuilder();
		HashMap<UniqueString, Value> valMap = successor.getVals();
		
		// Generate a string representation of state.
		for(UniqueString key : state.getVals().keySet()) {
			String valString = (key.toString() + " = " + valMap.get(key).toString());
			sb.append(valString);
			// New line between variables.
			sb.append("<br/>");
		}
		return sb.toString();
	}

	protected static String states2dot(final TLCState state) {
		// Replace "\" with "\\" and """ with "\"".	
		return state.toString().replace("\\", "\\\\").replace("\"", "\\\"").trim();
	}

	/* (non-Javadoc)
	 * @see tlc2.util.IStateWriter#close()
	 */
	public void close() {
		this.writer.append("}\n"); // closes the main subgraph.

		this.writer.append(dotLegend("DotLegend", this.actionToColors.keySet()));
		this.writer.append("}");
		super.close();
	}
}
