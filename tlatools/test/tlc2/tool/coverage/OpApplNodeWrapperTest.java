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
package tlc2.tool.coverage;

import org.junit.Before;
import org.junit.Test;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.xml.SymbolContext;
import tlc2.TLCGlobals;
import util.TestPrintStream;
import util.ToolIO;
import util.UniqueString;

public class OpApplNodeWrapperTest {

	@Before
	public void setup() {
		TLCGlobals.coverageInterval = 1;
		ToolIO.out = new TestPrintStream();
	}
	
	@Test
	public void testReportCoverage01() {
		final OpApplNodeWrapper root = new OpApplNodeWrapper();
		root.report();
		((TestPrintStream) ToolIO.out).assertEmpty();
		
		root.addChild(new OpApplNodeWrapper());
	}
	
	@Test
	public void testReportCoverage02() {
		final OpApplNodeWrapper root = new OpApplNodeWrapper();
		root.incInvocations(42);
		
		root.addChild(getNode(23));
		root.addChild(getNode(24));
		root.addChild(getNode(0)); // Not reported

		root.report();
		((TestPrintStream) ToolIO.out)
				.assertContains("  Unknown location: 42\n" + 
						"  |In module --TLA+ BUILTINS--: 23\n" + 
						"  |In module --TLA+ BUILTINS--: 24");
	}
	
	@Test
	public void testReportCoverage03() {
		final OpApplNodeWrapper root = new OpApplNodeWrapper();
		root.incInvocations(42);
		
		OpApplNodeWrapper childA = getNode(23);
		childA.addChild(getNode(546));
		root.addChild(childA);
		
		OpApplNodeWrapper childB = getNode(24);
		root.addChild(childB);
		childB.addChild(getNode(0)); // Not reported because 0
		
		OpApplNodeWrapper childC = getNode(0);
		root.addChild(childC); // Not reported

		childC.addChild(getNode(17)); // Must be reported despite C being 0
		
		root.report();
		((TestPrintStream) ToolIO.out)
				.assertContains("  Unknown location: 42\n" + 
						"  |In module --TLA+ BUILTINS--: 23\n" + 
						"  ||In module --TLA+ BUILTINS--: 546\n" + 
						"  |In module --TLA+ BUILTINS--: 24\n" + 
						"  |In module --TLA+ BUILTINS--: 17");
	}
	
	/*
  line 8, col 12 to line 8, col 21 of module A: 1
  |line 5, col 11 to line 5, col 49 of module A: 1
  ||line 5, col 31 to line 5, col 49 of module A: 131072
  ||line 5, col 20 to line 5, col 27 of module A: 131072
  |||line 5, col 27 to line 5, col 27 of module A: 1
  |line 8, col 16 to line 8, col 20 of module A: 1
	 */
	@Test
	public void testReportCoverage04() {
		final OpApplNodeWrapper root = new OpApplNodeWrapper();
		root.incInvocations(1);
		
		OpApplNodeWrapper childA = getNode(1);
		root.addChild(childA);
		
		childA.addChild(getNode(131072));
		
		OpApplNodeWrapper cChildA = getNode(131072);
		childA.addChild(cChildA);
		
		cChildA.addChild(getNode(1));
		
		OpApplNodeWrapper childB = getNode(1);
		root.addChild(childB);
		
		root.report();
		((TestPrintStream) ToolIO.out)
				.assertContains("  Unknown location: 1\n" + 
						"  |In module --TLA+ BUILTINS--: 1\n" + 
						"  ||In module --TLA+ BUILTINS--: 131072\n" + 
						"  ||In module --TLA+ BUILTINS--: 131072\n" + 
						"  |||In module --TLA+ BUILTINS--: 1\n" + 
						"  |In module --TLA+ BUILTINS--: 1");
	}
	
	// It is dummies all the way down...
	
	private OpApplNodeWrapper getNode(long count) {
		final SymbolNode sn = new DummySymbolNode(Long.toString(count));
		final OpApplNode node = new DummyOpApplNode(sn);
		return new OpApplNodeWrapper(node, count);
	}
	
	private static class DummySymbolNode extends SymbolNode {

		protected DummySymbolNode(String name) {
			super(1, SyntaxTreeNode.nullSTN, UniqueString.uniqueStringOf(name));
		}

		@Override
		public int getArity() {
			throw new UnsupportedOperationException("not implemented");
		}

		@Override
		public boolean isLocal() {
			throw new UnsupportedOperationException("not implemented");
		}

		@Override
		public boolean match(OpApplNode test, ModuleNode mn) throws AbortException {
			throw new UnsupportedOperationException("not implemented");
		}

		@Override
		protected Element getSymbolElement(Document doc, SymbolContext context) {
			throw new UnsupportedOperationException("not implemented");
		}

		@Override
		protected String getNodeRef() {
			throw new UnsupportedOperationException("not implemented");
		}
		
	}
	
	private static class DummyOpApplNode extends OpApplNode {

		public DummyOpApplNode(SymbolNode sn) {
			super(sn);
		}
	}
}
