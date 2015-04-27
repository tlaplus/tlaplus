/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
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

import junit.framework.TestCase;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.xml.SymbolContext;
import util.UniqueString;

public class ContextTest extends TestCase {

	public void testLookupEmpty() {
		assertNull(Context.Empty.lookup(new DummySymbolNode()));
		assertNull(Context.Empty.lookup(new DummySymbolNode(), true));
		assertNull(Context.Empty.lookup(new DummySymbolNode(), false));
		assertNull(Context.Empty.lookup(null));
		assertNull(Context.Empty.lookup(null, true));
		assertNull(Context.Empty.lookup(null, false));
	}

	public void testLookupBranch() {
		// BranchCtx -> Empty
		final Context ctx = Context.branch(Context.Empty);
		assertNull(ctx.lookup(new DummySymbolNode()));
		assertNull(ctx.lookup(new DummySymbolNode(), true));
		assertNull(ctx.lookup(new DummySymbolNode(), false));
		assertNull(ctx.lookup(null));
		assertNull(ctx.lookup(null, false));
		assertNull(ctx.lookup(null, true));
	}
	
	public void testLookupSymbolNodeNull() {
		final Context ctx = Context.branch(Context.Empty);
		assertNull(ctx.lookup(null));
	}
	
	public void testLookup() {
		final DummySymbolNode name = new DummySymbolNode("ctx1");
		final Object value = "value1";
		
		// Ctx 3 -> Ctx 2 -> Ctx Branch -> Ctx 1 -> Ctx Empty
		final Context ctx1 = Context.Empty.cons(name, value);
		final Context branch = Context.branch(ctx1);
		final Context ctx2 = branch.cons(new DummySymbolNode("ctx2"), "value2");
		final Context ctx3 = ctx2.cons(new DummySymbolNode("ctx3"), "value3");
		
		assertEquals(value, ctx3.lookup(name));
	}
	
	public void testLookupCutOffFalse() {
		final DummySymbolNode name = new DummySymbolNode("ctx1");
		final Object value = "value1";
		
		// Ctx 3 -> Ctx 2 -> Ctx Branch -> Ctx 1 -> Ctx Empty
		final Context ctx1 = Context.Empty.cons(name, value);
		final Context branch = Context.branch(ctx1);
		final Context ctx2 = branch.cons(new DummySymbolNode("ctx2"), "value2");
		final Context ctx3 = ctx2.cons(new DummySymbolNode("ctx3"), "value3");
		
		assertEquals(value, ctx3.lookup(name, false));
	}
	
	// Cutoff causes lookup to stop at branching context
	public void testLookupCutOffTrue() {
		final DummySymbolNode name = new DummySymbolNode("ctx1");
		final Object value = "value1";
		
		// Ctx 3 -> Ctx 2 -> Ctx Branch -> Ctx 1 -> Ctx Empty
		final Context ctx1 = Context.Empty.cons(name, value);
		final Context branch = Context.branch(ctx1);
		final Context ctx2 = branch.cons(new DummySymbolNode("ctx2"), "value2");
		final Context ctx3 = ctx2.cons(new DummySymbolNode("ctx3"), "value3");
		
		assertNull(ctx3.lookup(name, true));
	}
	
	public void testLookupWithAtBranching() {
		final DummySymbolNode name = new DummySymbolNode("ctx1");
		final Object value = "value1";
		
		// Ctx Branch -> Ctx 1 -> Ctx Empty
		final Context ctx1 = Context.Empty.cons(name, value);
		final Context branch = Context.branch(ctx1);
		
		assertEquals(value, branch.lookup(name));
	}
	
	public void testLookupWithCutOffFalseAtBranching() {
		final DummySymbolNode name = new DummySymbolNode("ctx1");
		final Object value = "value1";
		
		// Ctx Branch -> Ctx 1 -> Ctx Empty
		final Context ctx1 = Context.Empty.cons(name, value);
		final Context branch = Context.branch(ctx1);
		
		assertEquals(value, branch.lookup(name, false));
	}

	public void testLookupWithCutOffTrueAtBranching() {
		final DummySymbolNode name = new DummySymbolNode("ctx1");
		final Object value = "value1";
		
		// Ctx Branch -> Ctx 1 -> Ctx Empty
		final Context ctx1 = Context.Empty.cons(name, value);
		final Context branch = Context.branch(ctx1);
		
		assertNull(branch.lookup(name, true));
	}
	
	/**
	 * Test method for {@link tlc2.util.Context#lookup(tla2sany.semantic.SymbolNode)}.
	 */
	public void testLookupSymbolNode() {
		final DummySymbolNode name = new DummySymbolNode();
		final Object value = new Object();

		final Context ctx = Context.branch(Context.Empty);
		Context cons = ctx.cons(name, value);
		
		Object lookup = cons.lookup(name);
		assertEquals(value, lookup);
	}
	
	// Need a dummy for the instance identity checks in Context 
	private static class DummySymbolNode extends SymbolNode {

		DummySymbolNode() {
			this("Dummy");
		}
		
		DummySymbolNode(String name) {
			super(-1, new SyntaxTreeNode(), UniqueString.uniqueStringOf(name));
		}

		public int getArity() {
			return 0;
		}

		public boolean isLocal() {
			return false;
		}
		
		public boolean match(OpApplNode test, ModuleNode mn) throws AbortException {
			return false;
		}

		protected Element getSymbolElement(Document doc, SymbolContext context) {
			return null;
		}

		protected String getNodeRef() {
			return null;
		}
	}
}
