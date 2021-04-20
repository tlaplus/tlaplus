/*******************************************************************************
 * Copyright (c) 2021 Microsoft Research. All rights reserved. 
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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.xml.SymbolContext;
import tlc2.util.Context;
import util.UniqueString;

public class TBParTest {

	@Test
	public void testParticleClosureInconsistentConstantLevel() {
		final TBPar tbPar = new TBPar();
		// Positive form (negation pushed down), and, thus, locally inconsistent.
		tbPar.addElement(new LNBool(false));
		tbPar.addElement(new LNNeg(new LNBool(false)));
		assertEquals(0, tbPar.particleClosure().size());
	}

	@Test
	public void testParticleClosureInconsistentStateLevel() {
		final TBPar tbPar = new TBPar();
		// Positive form (negation pushed down), and, thus, locally inconsistent.
		final LiveExprNode p = new LNStateAST(new DummyOpApplNode("p"), Context.Empty);
		tbPar.addElement(p);
		tbPar.addElement(new LNNeg(p));
		assertEquals(0, tbPar.particleClosure().size());
	}

	@Test
	public void testParticleClosureConsistentConstantLevel() {
		final TBPar tbPar = new TBPar();
		tbPar.addElement(new LNBool(false));
		tbPar.addElement(new LNNeg(new LNBool(true)));
		assertEquals(1, tbPar.particleClosure().size());
	}

	@Test
	public void testParticleClosureConsistentStateLevel() {
		final TBPar tbPar = new TBPar();
		final LiveExprNode p = new LNStateAST(new DummyOpApplNode("p"), Context.Empty);
		tbPar.addElement(p);
		tbPar.addElement(new LNNeg(new LNNeg(p)));
		assertEquals(1, tbPar.particleClosure().size());
	}

	@Test
	public void testParticleClosureExampleConstLevel() {
		// <>p \/ []~p from page 454 of Manna & Pnueli book with p constant-level
		// expression.
		final LiveExprNode p = new LNBool(true);
		
		final TBPar tbPar = new TBPar();
		final LNEven evenP = new LNEven(p);
		// Because the same LNStateAST instance appears in both disjuncts, there is no
		// need to tag it--LNState#equals behaves the same.
		final LNDisj phi = new LNDisj(evenP, new LNAll(new LNNeg(p)));
		tbPar.addElement(phi);

		// p 454 gives the expected particles.
		final TBParVec particleClosure = tbPar.particleClosure();
		assertEquals(3, particleClosure.size());

		// <>p \/ []~p, <>p, p
		assertEquals(phi, particleClosure.elementAt(0).elementAt(0));
		assertEquals(evenP, particleClosure.elementAt(0).elementAt(1));
		assertEquals(p, particleClosure.elementAt(0).elementAt(2));

		// <>p \/ []~p, <>p, ()<>p
		assertEquals(phi, particleClosure.elementAt(1).elementAt(0));
		assertEquals(evenP, particleClosure.elementAt(1).elementAt(1));
		// LN*#equals(Object) just object identify, thus, manually checked here. 
		final LiveExprNode nextEvenP = particleClosure.elementAt(1).elementAt(2);
		assertTrue(nextEvenP instanceof LNNext);
		assertEquals(evenP, ((LNNext) nextEvenP).getBody());

		// <>p \/ []~p, []~p, ()[]~p, ~p
		assertEquals(phi, particleClosure.elementAt(2).elementAt(0));
		// ...[]~p
		assertTrue(particleClosure.elementAt(2).elementAt(1) instanceof LNAll);
		assertTrue(((LNAll) particleClosure.elementAt(2).elementAt(1)).getBody() instanceof LNNeg);
		assertEquals(p, ((LNNeg) ((LNAll) particleClosure.elementAt(2).elementAt(1)).getBody()).getBody());
		assertEquals("[]-TRUE", particleClosure.elementAt(2).elementAt(1).toString());
		// ...~p
		assertTrue((particleClosure.elementAt(2).elementAt(2)) instanceof LNNeg);
		assertEquals(p, ((LNNeg) particleClosure.elementAt(2).elementAt(2)).getBody());
		assertEquals("-TRUE", particleClosure.elementAt(2).elementAt(2).toString());
		// ...()[]~p
		assertTrue(particleClosure.elementAt(2).elementAt(3) instanceof LNNext);
		assertTrue(((LNNext) particleClosure.elementAt(2).elementAt(3)).getBody() instanceof LNAll);
		assertTrue(((LNAll) ((LNNext) particleClosure.elementAt(2).elementAt(3)).getBody()).getBody() instanceof LNNeg);
		assertEquals("()[]-TRUE", particleClosure.elementAt(2).elementAt(3).toString());
	}

	@Test
	public void testParticleClosureExampleStateLevel() {
		// <>p \/ []~p from page 454 of Manna & Pnueli book with p state-level
		// expression.
		final LiveExprNode p = new LNStateAST(new DummyOpApplNode("p"), Context.Empty);

		final TBPar tbPar = new TBPar();
		final LNEven evenP = new LNEven(p);
		// Because the same LNStateAST instance appears in both disjuncts, there is no
		// need to tag it--LNState#equals behaves the same.
		final LNDisj phi = new LNDisj(evenP, new LNAll(new LNNeg(p)));
		tbPar.addElement(phi);

		// p 454 gives the expected particles.
		final TBParVec particleClosure = tbPar.particleClosure();
		assertEquals(3, particleClosure.size());

		// <>p \/ []~p, <>p, p
		assertEquals(phi, particleClosure.elementAt(0).elementAt(0));
		assertEquals(evenP, particleClosure.elementAt(0).elementAt(1));
		assertEquals(p, particleClosure.elementAt(0).elementAt(2));

		// <>p \/ []~p, <>p, ()<>p
		assertEquals(phi, particleClosure.elementAt(1).elementAt(0));
		assertEquals(evenP, particleClosure.elementAt(1).elementAt(1));
		// LN*#equals(Object) just object identify, thus, manually checked here. 
		final LiveExprNode nextEvenP = particleClosure.elementAt(1).elementAt(2);
		assertTrue(nextEvenP instanceof LNNext);
		assertEquals(evenP, ((LNNext) nextEvenP).getBody());

		// <>p \/ []~p, []~p, ()[]~p, ~p
		assertEquals(phi, particleClosure.elementAt(2).elementAt(0));
		// ...[]~p
		assertTrue(particleClosure.elementAt(2).elementAt(1) instanceof LNAll);
		assertTrue(((LNAll) particleClosure.elementAt(2).elementAt(1)).getBody() instanceof LNNeg);
		assertEquals(p, ((LNNeg) ((LNAll) particleClosure.elementAt(2).elementAt(1)).getBody()).getBody());
		assertEquals("[]-p", particleClosure.elementAt(2).elementAt(1).toString());
		// ...~p
		assertTrue((particleClosure.elementAt(2).elementAt(2)) instanceof LNNeg);
		assertEquals(p, ((LNNeg) particleClosure.elementAt(2).elementAt(2)).getBody());
		assertEquals("-p", particleClosure.elementAt(2).elementAt(2).toString());
		// ...()[]~p
		assertTrue(particleClosure.elementAt(2).elementAt(3) instanceof LNNext);
		assertTrue(((LNNext) particleClosure.elementAt(2).elementAt(3)).getBody() instanceof LNAll);
		assertTrue(((LNAll) ((LNNext) particleClosure.elementAt(2).elementAt(3)).getBody()).getBody() instanceof LNNeg);
		assertEquals("()[]-p", particleClosure.elementAt(2).elementAt(3).toString());
	}

	
	public static class DummyOpApplNode extends OpApplNode {

		public DummyOpApplNode(String name) {
			super(new DummySymbolNode(name));
		}

		@Override
		public String toString() {
			return this.operator.toString();
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
			
			@Override
			public String toString() {
				return name.toString();
			}
		}
	}
}
