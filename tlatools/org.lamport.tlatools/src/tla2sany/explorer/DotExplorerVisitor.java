/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
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
package tla2sany.explorer;

import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.Map;

import tla2sany.semantic.Context;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.Subst;
import util.FileUtil;

public class DotExplorerVisitor extends ExplorerVisitor {

	private static final Map<Class<? extends SemanticNode>, String> type2format = new HashMap<>();
	
	static {
		type2format.put(OpDefNode.class, " [style=filled,shape=diamond,fillcolor=\"red\",");
		type2format.put(OpApplNode.class, " [color=\"green\",");
		type2format.put(OpDeclNode.class, " [shape=square,color=\"yellow\",");
		type2format.put(LetInNode.class, " [color=\"orange\",");
	}
	
	private final ModuleNode rootModule;
	private final Hashtable<Integer, ExploreNode> table;
	private final PrintWriter writer;
	private final Deque<ExploreNode> stack = new ArrayDeque<>();
	private final boolean includeLineNumbers = Boolean.getBoolean(DotExplorerVisitor.class.getName() + ".includeLineNumbers");

	public DotExplorerVisitor(final ModuleNode rootModule) {
		this.rootModule = rootModule;
		this.table = new NoopTable<>();
		try {
			this.writer = new PrintWriter(FileUtil.newBFOS(rootModule.getName() + ".dot"));
		} catch (FileNotFoundException e) {
			throw new RuntimeException(e);
		}
		this.writer.append("strict digraph DiskGraph {\n"); // strict removes redundant edges
	}
	
	@Override
	public void preVisit(ExploreNode exploreNode) {
		if (skipNode(exploreNode)) {
			return;
		}
		
		final ExploreNode parent = stack.peek();
		if (exploreNode == this.rootModule) {
			assert parent == null;
			
			final ModuleNode mn = (ModuleNode) exploreNode;
			this.writer.append(Integer.toString(mn.hashCode()));
			this.writer.append(" [label=\"");
			this.writer.append(mn.getName().toString());
			this.writer.append("\",style = filled]");
			this.writer.append(";\n");
			
			stack.push(exploreNode);
		} else {
			final SemanticNode sn = (SemanticNode) exploreNode;
			this.writer.append(Integer.toString(sn.hashCode()));
			this.writer.append(type2format.getOrDefault(exploreNode.getClass(), " [") + "label=\"");
			if (exploreNode instanceof OpDefNode) {
				this.writer.append(toDot(((OpDefNode) sn).getName().toString()));
			} else {
				this.writer.append(toDot(sn.getTreeNode().getHumanReadableImage()));
			}
			if (includeLineNumbers) {
				// Wrap location for more compact nodes in dot output.
				final String loc = sn.getLocation().toString();
				this.writer.append("\n");
				this.writer.append(loc.replace("of module", "\n"));
				this.writer.append("\n" + sn.getClass().getSimpleName());
			}
			this.writer.append("\"]");
			this.writer.append(";\n");

			this.writer.append(Integer.toString(parent.hashCode()));
			this.writer.append(" -> ");
			this.writer.append(Integer.toString(sn.hashCode()));
			this.writer.append("\n");

			stack.push(sn);
		}
	}

	@Override
	public void postVisit(final ExploreNode exploreNode) {
		if (skipNode(exploreNode)) {
			return;
		}
		final ExploreNode pop = stack.pop();
		assert pop == exploreNode;
	}

	public void done() {
		this.writer.append("}");
		this.writer.close();
	}

	public Hashtable<Integer, ExploreNode> getTable() {
		return table;
	}
	
	private static String toDot(final String sn) {
		return sn.replace("\\", "\\\\").replace("\"", "\\\"").trim().replace("\n", "\\n");
	}
	
	private static boolean skipNode(final ExploreNode exploreNode) {
		if (exploreNode instanceof Context || exploreNode instanceof FormalParamNode) {
			return true;
		}
		if (exploreNode instanceof Subst) {
			return true;
		}
		if (Context.isBuiltIn(exploreNode)) {
			return true;
		}
		if (exploreNode instanceof SemanticNode) {
			return ((SemanticNode) exploreNode).isStandardModule();
		}
		return false;
	}
	
	@SuppressWarnings("serial")
	private class NoopTable<K, V> extends Hashtable<K, V> {
		@Override
		public V get(Object key) {
			// Return null here to visit an OpDefNode D multiple times if D is "called" from
			// multiple OpApplNodes. However, stop endless recursion if D is a RECURSIVE
			// operator.
			final V v = super.get(key);
			if (v instanceof OpDefNode) {
				final OpDefNode odn = (OpDefNode) v;
				if (odn.getInRecursive()) {
					if (stack.contains(odn)) {
						// RECURSIVE operators
						return v;
					}
				}
			}
			return null;
		}
	}
}
