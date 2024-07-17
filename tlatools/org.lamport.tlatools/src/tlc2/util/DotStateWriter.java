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
import java.nio.file.Files;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import tla2sany.semantic.SemanticNode;
import tlc2.TLCGlobals;
import tlc2.tool.Action;
import tlc2.tool.TLCState;
import util.FileUtil;

/**
 * Writes the given state in dot notation.
 * 
 * @see https://en.wikipedia.org/wiki/DOT_(graph_description_language)
 * 
 * 
 * To ASCII-render a graph (on Debian|Ubuntu) install cpanminus, sudo cpanm Graph::Easy and run:
 * cat your.dot | graph-easy --from=dot --as_ascii
 * (https://stackoverflow.com/questions/3211801/graphviz-and-ascii-output)
 */
public class DotStateWriter extends StateWriter {

	// The Graphviz color scheme that is used for state transition edge colors. See
	// https://www.graphviz.org/doc/info/colors.html for more details on color schemes.
	private static final String dotColorScheme = "paired12";

	// A mapping of action names to their assigned color ids. Since states are fed
	// into a StateWriter incrementally, one at a time, this table is built up over
	// time, adding new actions as we find out about them.
	private final Map<String, Integer> actionToColors = new HashMap<>();
	
	// A mapping from ranks to nodes.
	private final Map<Integer, Set<Long>> rankToNodes = new HashMap<>();
	
	// Forbids the creation of multi-edges.
	private final Set<Long> strict;

	// Determines whether or not transition edges should be colorized in the state
	// graph.
	private final boolean colorize;

	// Determines whether or not transition edges should be labeled with their
	// action names.
	private final boolean actionLabels;

	// Used for assigning unique color identifiers to each action type. Incremented
	// by 1 every time a new color is assigned to an action.
	private Integer colorGen = 1;
	
	// Create a valid fname_snapshot.dot file after a state is written.
	private final boolean snapshot;
	
	// Include states in the dot file that are excluded from the model via a state or action constraint.
	private final boolean constrained;
	
	// Determines whether or not stuttering edges should be rendered.
	private final boolean stuttering;
	
	public DotStateWriter() throws IOException {
		this("DotStateWriter.dot", "", false, false, false, false, false, false);
	}
	
	public DotStateWriter(final String fname, final String strict) throws IOException {
		this(fname, strict, false, false, false, false, false, false);
	}
	
	/**
	 * @param fname
	 * @param colorize
	 *            Colorize state transition edges in the DOT state graph.
	 * @param actionLabels
	 *            Label transition edges in the state graph with the name of the
	 *            associated action. Can potentially add a large amount of visual
	 *            clutter for large graphs with many actions.
	 * @throws IOException
	 */
	public DotStateWriter(final String fname, final boolean colorize, final boolean actionLabels,
			final boolean snapshot, final boolean constrained, final boolean stuttering, final boolean strict) throws IOException {
		this(fname, "strict ", colorize, actionLabels, snapshot, constrained, stuttering, strict);
	}
	
	public DotStateWriter(final String fname, final String prefix, final boolean colorize, final boolean actionLabels,
			final boolean snapshot, final boolean constrained, final boolean stuttering, final boolean strict) throws IOException {
		super(fname);
		this.colorize = colorize;
		this.actionLabels = actionLabels;
		this.snapshot = snapshot;
		this.constrained = constrained;
		this.stuttering = stuttering;
		if (strict) {
			this.strict = new HashSet<>();
		} else {
			this.strict = null;
		}
		this.writer.append(prefix + "digraph DiskGraph {\n"); // strict removes redundant edges
		// Turned off LR because top to bottom provides better results with GraphViz viewer.
//		this.writer.append("rankdir=LR;\n"); // Left to right rather than top to bottom
		
		// Using boxed nodes instead of ovals can significantly reduce screen estate
		// waste. Rounding the corners of nodes is merely cosmetic and does not offer
		// any substantial benefits.
		this.writer.append("node [shape=box,style=rounded]\n");
        
		// Set the color scheme for transition edges if necessary.
		if(colorize) {
			this.writer.append(String.format("edge [colorscheme=\"%s\"]\n", dotColorScheme));	
		}
        
		// Spread out state nodes a bit more.
        this.writer.append("nodesep=0.35;\n");

		this.writer.append("subgraph cluster_graph {\n"); 
        this.writer.append("color=\"white\";\n"); // no border.
		this.writer.flush();
	}

	/* (non-Javadoc)
	 * @see tlc2.util.IStateWriter#isDot()
	 */
	@Override
	public boolean isDot() {
		return true;
	}
	
	public boolean isConstrained() {
		return this.constrained;
	}

	/* (non-Javadoc)
	 * @see tlc2.util.StateWriter#writeState(tlc2.tool.TLCState)
	 */
	public synchronized void writeState(final TLCState state) {
		// Marker the state as an initial state by using a filled style.
		this.writer.append(Long.toString(state.fingerPrint()));
		this.writer.append(" [label=\"");
		this.writer.append(states2dot(state.evalStateLevelAlias()));
		this.writer.append("\",style = filled]");
		this.writer.append("\n");
		
		maintainRanks(state);
		
		if (snapshot) {
			try {
				this.snapshot();
			} catch (IOException e) {
				// Let's assume this never happens!
				e.printStackTrace();
				throw new RuntimeException(e);
			}
		}
	}
	
	protected void maintainRanks(final TLCState state) {
		rankToNodes.computeIfAbsent(state.getLevel(), k -> new HashSet<Long>()).add(state.fingerPrint());
	}

	/* (non-Javadoc)
	 * @see tlc2.util.StateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.TLCState, boolean)
	 */
	public void writeState(TLCState state, TLCState successor, short stateFlags) {
		writeState(state, successor, stateFlags, Visualization.DEFAULT);
	}
	
    public void writeState(final TLCState state, final TLCState successor, final short stateFlags, Action action)
    {
		writeState(state, successor, null, 0, 0, stateFlags, Visualization.DEFAULT, action, null);
    }
	
    public void writeState(final TLCState state, final TLCState successor, final short stateFlags, Action action, SemanticNode pred)
    {
		writeState(state, successor, null, 0, 0, stateFlags, Visualization.DEFAULT, action, pred);
    }
	
	/* (non-Javadoc)
	 * @see tlc2.util.StateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.TLCState, boolean, tlc2.util.IStateWriter.Visualization)
	 */
	public void writeState(TLCState state, TLCState successor, short stateFlags, Visualization visualization) {
		writeState(state, successor, null, 0, 0, stateFlags, visualization, null, null);
	}

	/* (non-Javadoc)
	 * @see tlc2.util.StateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.TLCState, tlc2.util.BitVector, int, int, boolean)
	 */
	public void writeState(TLCState state, TLCState successor, BitVector actionChecks, int from, int length, short stateFlags) {
		writeState(state, successor, actionChecks, from, length, stateFlags, Visualization.DEFAULT, null, null);
	}

	/* (non-Javadoc)
	 * @see tlc2.util.StateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.TLCState, java.lang.String, boolean, tlc2.util.IStateWriter.Visualization)
	 */
	private synchronized void writeState(TLCState state, TLCState successor, BitVector actionChecks, int from, int length, short stateFlags,
			Visualization visualization, Action action, SemanticNode pred) {
		if (!stuttering && visualization == Visualization.STUTTERING) {
			// Do not render stuttering transitions unless requested.
			return;
		}
		
		final long sfp = successor.fingerPrint();
		final long cfp = state.fingerPrint();

		if (strict != null) {
			// XORing the fingerprints of the two nodes may result in the omission of this
			// edge. However, this is expected to be a minor issue, as the DotStateWriter
			// primarily handles small graphs for visualization with GraphViz.
			if (!strict.add(cfp ^ sfp)) {
				return;
			}
		}
		
		final String successorsFP = Long.toString(sfp);
		
		// Write the transition edge.
		this.writer.append(Long.toString(cfp));
		this.writer.append(" -> ");
		this.writer.append(successorsFP);
		if (visualization == Visualization.STUTTERING) {
			this.writer.append(" [style=\"dashed\",color=\"lightgray\"];\n");
			maintainRanks(state);
		} else {
			// Add the transition edge label.
			final String labelFmtStr = " [label=\"%s%s%s\",color=\"%s\",fontcolor=\"%s\"]";
			
			// Only colorize edges if specified. Default to black otherwise.
			final String color = colorize ? this.getActionColor(action).toString() : "black" ;

			// Only add action label if specified.
			final String actionName = actionLabels && action != null ? action.getName().toString() : "" ;
			
			// Show the changes variables as part of the transition if the successor has
			// previously been added.
			String diff = "";
			if (TLCGlobals.printDiffsOnly && isSet(stateFlags, IStateWriter.IsSeen)
					&& rankToNodes.values().stream().filter(s -> s.contains(sfp)).findAny().isEmpty()) {
				diff = states2dot(state.evalStateLevelAlias(), successor.evalStateLevelAlias());
			}

			this.writer.append(
					String.format(labelFmtStr, actionName, diff, pred == null ? "" : "\n" + pred.toString(), color, color));
			
			this.writer.append(";\n");
			
			// If the successor is new, print the state's label. Labels are printed
			// when writeState sees the successor. It does not print the label for
			// the current state. If it would print the label for the current state,
			// the init state labels would be printed twice.
	    	if (!isSet(stateFlags, IStateWriter.IsSeen)) {
				// Write the successor's label.
				this.writer.append(successorsFP);
				this.writer.append(" [label=\"");
				if (TLCGlobals.printDiffsOnly) {
					this.writer.append(states2dot(state.evalStateLevelAlias(), successor.evalStateLevelAlias()));
				} else {
					this.writer.append(states2dot(successor.evalStateLevelAlias()));
				}
				this.writer.append("\",tooltip=\"");
				this.writer.append(states2dot(successor));
		    	if (isSet(stateFlags, IStateWriter.IsNotInModel)) {
		    		this.writer.append("\",style = filled, fillcolor=lightyellow]");
				} else {
					this.writer.append("\"]");
				}
				this.writer.append(";\n");
				
				maintainRanks(state);
			}
		}
		
		if (snapshot) {
			try {
				this.snapshot();
			} catch (IOException e) {
				// Let's assume this never happens!
				e.printStackTrace();
				throw new RuntimeException(e);
			}
		}
	}
	
	/**
	 * Given an action, returns the associated color identifier for it. The color
	 * identifier is just an integer suitable for use in a GraphViz color scheme. This
	 * method updates the (action -> color) mapping if this action has not been seen
	 * before for this DotStateWriter instance.
	 * 
	 * @param action
	 * @return the color identifier for the given action
	 */
	protected Integer getActionColor(final Action action) {
		// Return a default color if the given action is null.
		if (action == null) {
			return 1;
		} else {
			String actionName = action.getName().toString();
			// If this action has been seen before, retrieve its color.
			if (actionToColors.containsKey(actionName)) {
				return actionToColors.get(actionName);
			}
			// If this action has not been seen yet, get the next available color
			// and assign it to this action.
			else {
				this.colorGen++;
				actionToColors.put(actionName, this.colorGen);
				return this.colorGen;
			}
		}
	}
	
	/**
	 * Creates a DOT label for an edge representing a state transition. 
	 * 
	 * @param state the current state of the transition
	 * @param successor the next state of the transition
	 * @param action the action that induced the transition
	 * @return the DOT label for the edge
	 */
	protected String dotTransitionLabel(final TLCState state, final TLCState successor, final Action action, final SemanticNode pred) {
	    // Only colorize edges if specified. Default to black otherwise.
		final String color = colorize ? this.getActionColor(action).toString() : "black" ;
		
	    // Only add action label if specified.
		final String actionName = actionLabels ? action.getName().toString() : "" ;
		
		final String labelFmtStr = " [label=\"%s%s\",color=\"%s\",fontcolor=\"%s\"]";
		return String.format(labelFmtStr, actionName, pred == null ? "" : "\n" + pred.toString(), color, color);
	}
	
	
	/**
	 * Creates a DOT legend that maps actions to their corresponding edge color in the state graph.
	 * 
	 * @param name the title of the legend
	 * @param actions the set of action names that will be included in the legend
	 * @return
	 */
	protected String dotLegend(final String name, final Set<String> actions) {
		final StringBuilder sb = new StringBuilder();
		sb.append(String.format("subgraph %s {", "cluster_legend"));
		sb.append("graph[style=bold];");
		sb.append("label = \"Next State Actions\" style=\"solid\"\n");
		sb.append(String.format("node [ labeljust=\"l\",colorscheme=\"%s\",style=filled,shape=record ]\n",
				dotColorScheme));
		for (String action : actions) {
			String str = String.format("%s [label=\"%s\",fillcolor=%d]", action.replaceAll("!", ":"), action,
					this.actionToColors.get(action));
			sb.append(str);
			sb.append("\n");
		}
		sb.append("}");
		return sb.toString();
	}
	
	/**
	 * Given a TLC state, generate a string representation suitable for a HTML DOT graph label.
	 */
	//TODO This cannot handle states with variables such as "active = (0 :> TRUE @@ 1 :> FALSE)". 
//	protected static String state2html(final TLCState state) {		
//		final StringBuilder sb = new StringBuilder();
//		final Map<UniqueString, Value> valMap = state.getVals();
//
//		// Generate a string representation of state.
//		for (UniqueString key : valMap.keySet()) {
//			final String valString = (key.toString() + " = " + valMap.get(key).toString());
//			sb.append(valString);
//			// New line between variables.
//			sb.append("<br/>");
//		}
//		return sb.toString();
//	}

	protected static String states2dot(final TLCState predecessor, final TLCState state) {
		// Replace "\" with "\\" and """ with "\"".	
		return state.toString(predecessor).replace("\\", "\\\\").replace("\"", "\\\"").trim()
				.replace("\n", "\\n"); // Do not remove remaining (i.e. no danling/leading) "\n". 
	}

	protected static String states2dot(final TLCState state) {
		// Replace "\" with "\\" and """ with "\"".	
		return state.toString().replace("\\", "\\\\").replace("\"", "\\\"").trim()
				.replace("\n", "\\n"); // Do not remove remaining (i.e. no danling/leading) "\n". 
	}

	/* (non-Javadoc)
	 * @see tlc2.util.IStateWriter#close()
	 */
	public void close() {
		for (final Set<Long> entry : rankToNodes.values()) {
			this.writer.append("{rank = same; ");
			for (final Long l : entry) {
				this.writer.append(l + ";");
			}
			this.writer.append("}\n");
		}
		this.writer.append("}\n"); // closes the main subgraph.
		// We only need the legend if the edges are colored by action and there is more
		// than a single action.
		if (colorize && this.actionToColors.size() > 1) {
			this.writer.append(dotLegend("DotLegend", this.actionToColors.keySet()));
		}
		this.writer.append("}");
		super.close();
	}
	
	/* (non-Javadoc)
	 * @see tlc2.util.IStateWriter#snapshot()
	 */
	@Override
	public void snapshot() throws IOException {
		this.writer.flush();
		
		final String snapshot = fname.replace(".dot", "_snapshot" + ".dot");
		FileUtil.copyFile(this.fname, snapshot);

		StringBuffer buf = new StringBuffer();
		for (final Set<Long> entry : rankToNodes.values()) {
			buf.append("{rank = same; ");
			for (final Long l : entry) {
				buf.append(l + ";");
			}
			buf.append("}\n");
		}
		buf.append("}\n");
		// We only need the legend if the edges are colored by action and there is more
		// than a single action.
		if (colorize && this.actionToColors.size() > 1) {
			buf.append(dotLegend("DotLegend", this.actionToColors.keySet()));
		}
		buf.append("}");

	    Files.write(Paths.get(snapshot), buf.toString().getBytes(), StandardOpenOption.APPEND);
	}
}
