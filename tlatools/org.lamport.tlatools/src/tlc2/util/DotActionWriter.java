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

package tlc2.util;

import java.io.IOException;
import java.io.PrintWriter;

import tlc2.tool.Action;
import util.FileUtil;

/**
 * Writes the given action in dot notation.
 * 
 * @see https://en.wikipedia.org/wiki/DOT_(graph_description_language)
 * 
 * 
 * To ASCII-render a graph (on Debian|Ubuntu) install cpanminus, sudo cpanm Graph::Easy and run:
 * cat your.dot | graph-easy --from=dot --as_ascii
 * (https://stackoverflow.com/questions/3211801/graphviz-and-ascii-output)
 */
public class DotActionWriter {

    protected final PrintWriter writer;
    protected final String fname;
	
	public DotActionWriter(final String fname, final String strict) throws IOException {
        this.fname = fname;
        this.writer = new PrintWriter(FileUtil.newBFOS(fname));
		this.writer.append(strict + "digraph ActionGraph {\n"); // strict removes redundant edges
		// Turned off LR because top to bottom provides better results with GraphViz viewer.
//		this.writer.append("rankdir=LR;\n"); // Left to right rather than top to bottom
        
		// Spread out state nodes a bit more.
        this.writer.append("nodesep=0.35;\n");

        // Add a legend explaining the semantics of the arcs.
        //TODO penwidth should be explained too!
//        subgraph cluster_legend {
//            label = "Legend";
//            node [shape=point] {
//                d0 [style = invis];
//                d1 [style = invis];
//                p0 [style = invis];
//                p1 [style = invis];
//            }
//            d0 -> d1 [label=unseen color=green style=dotted]
//            p0 -> p1 [label=seen]
//        }
		this.writer.append("subgraph cluster_legend {\n");
		this.writer.append("label = \"Coverage\";\n");
		this.writer.append("node [shape=point] {\n");
		this.writer.append("d0 [style = invis];\n");
		this.writer.append("d1 [style = invis];\n");
		this.writer.append("p0 [style = invis];\n");
		this.writer.append("p0 [style = invis];\n");
		this.writer.append("}\n");
		this.writer.append("d0 -> d1 [label=unseen, color=\"green\", style=dotted]\n");
		this.writer.append("p0 -> p1 [label=seen]\n");
		this.writer.append("}\n");

		this.writer.flush();
	}

	public synchronized void write(final Action action, final int id) {
		this.writer.append(Integer.toString(id));
		this.writer.append(" [shape=box,label=\"");
		this.writer.append(action.getNameOfDefault());
		if (action.isInitPredicate()) {
			// Marker the action as an initial predicate by using a filled style.
			this.writer.append("\",style = filled]");
		} else {
			this.writer.append("\"]");
		}
		this.writer.append("\n");
	}

	public synchronized void write(final int fromId, final int toId) {
		write(fromId, toId, 0d);
	}

	public synchronized void write(final int fromId, final int toId, final double weight) {
		// Write the transition edge.
		this.writer.append(Integer.toString(fromId));
		this.writer.append(" -> ");
		this.writer.append(Integer.toString(toId));
		// Add the transition edge label.
		if (weight == 0d) {
			this.writer.append("[color=\"green\",style=dotted]");
		} else {
			// TODO don't increase penwidth (contributes to a spaghetti ball of lines) but
			// use heatmap approach like in ModuleCoverageInformation.
			this.writer.append(String.format("[penwidth=%s]", Double.toString(weight)));
		}
		this.writer.append(";\n");
	}

	public void close() {
		this.writer.append("}");
		this.writer.close();
	}

	public void writeSubGraphStart(final String key, final String label) {
		this.writer.append(String.format("subgraph cluster_%s {\ncolor=\"white\"\nlabel=\"%s\"\n", key, label));
	}

	public void writeSubGraphEnd() {
		this.writer.append("}\n");
	}
}
