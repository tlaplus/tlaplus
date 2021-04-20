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

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.util.Context;

public class LiveExprNodeTest {

	@Test
	public void testLNBool() {
		// Rewriting rules page 452.
		final LiveExprNode p = new LNBool(true);
		final LiveExprNode q = new LNBool(true);
		
		// ~~T -> T
		LiveExprNode tf = new LNNeg(new LNNeg(p));
		assertFalse(tf.isPositiveForm());
		assertTrue(tf.pushNeg().isPositiveForm());
		assertTrue(p.equals(tf.toDNF()));

		// ~<>T -> []F
		tf = new LNNeg(new LNEven(p));
		assertFalse(tf.isPositiveForm());
		assertTrue(tf.pushNeg().isPositiveForm());
		assertTrue(new LNAll(new LNBool(false)).equals(tf.toDNF()));

		// ~[]T -> <>F
		tf = new LNNeg(new LNAll(p));
		assertFalse(tf.isPositiveForm());
		assertTrue(tf.pushNeg().isPositiveForm());
		assertTrue(new LNEven(new LNBool(false)).equals(tf.toDNF()));

		// ~()T -> ()F
		//TODO: pushNeg causes a StackOverflow, see LiveExprNode#pushNeg
		tf = new LNNeg(new LNNext(p));
		assertFalse(tf.isPositiveForm());
//		assertTrue(tf.pushNeg().isPositiveForm());
//		assertTrue(new LNNext(new LNBool(false)).equals(tf.toDNF()));

		// ~(T /\ T) -> F \/ F
		//TODO: Rewrite F\/F to F in toDNF? Probably not worth it.
		tf = new LNNeg(new LNConj(p, q));
		assertFalse(tf.isPositiveForm());
		assertTrue(tf.pushNeg().isPositiveForm());
		assertTrue(new LNDisj(new LNBool(false), new LNBool(false)).equals(tf.toDNF()));

		// ~(T \/ T) -> F /\ F
		//TODO: Rewrite F/\F to F in toDNF? Probably not worth it.
		tf = new LNNeg(new LNDisj(p, q));
		assertFalse(tf.isPositiveForm());
		assertTrue(tf.pushNeg().isPositiveForm());
		assertTrue(new LNConj(new LNBool(false), new LNBool(false)).equals(tf.toDNF()));
	}

	@Test
	public void testLNState() {
		final LiveExprNode p = new LNStateAST(new TBParTest.DummyOpApplNode("p"), Context.Empty);
		final LiveExprNode q = new LNStateAST(new TBParTest.DummyOpApplNode("q"), Context.Empty);

		// ~~p -> p
		LiveExprNode tf = new LNNeg(new LNNeg(p));
		assertFalse(tf.isPositiveForm());
		assertTrue(tf.pushNeg().isPositiveForm());
		assertTrue(p.equals(tf.toDNF()));

		// ~<>p -> []~p
		tf = new LNNeg(new LNEven(p));
		assertFalse(tf.isPositiveForm());
		assertTrue(tf.pushNeg().isPositiveForm());
		assertTrue(new LNAll(new LNNeg(p)).equals(tf.toDNF()));

		// ~[]p -> <>~p
		tf = new LNNeg(new LNAll(p));
		assertFalse(tf.isPositiveForm());
		assertTrue(tf.pushNeg().isPositiveForm());
		assertTrue(new LNEven(new LNNeg(p)).equals(tf.toDNF()));

		// ~()p -> ()~p
		//TODO: pushNeg causes a StackOverflow, see LiveExprNode#pushNeg
		tf = new LNNeg(new LNNext(p));
		assertFalse(tf.isPositiveForm());
//		assertTrue(tf.pushNeg().isPositiveForm());
//		assertTrue(new LNNext(new LNNeg(p)).equals(tf.toDNF()));

		// ~(p /\ q) -> ~p \/ ~q
		tf = new LNNeg(new LNConj(p, q));
		assertFalse(tf.isPositiveForm());
		assertTrue(tf.pushNeg().isPositiveForm());
		assertTrue(new LNDisj(new LNNeg(p), new LNNeg(q)).equals(tf.toDNF()));

		// ~(p \/ q) -> ~p /\ ~q
		tf = new LNNeg(new LNDisj(p, q));
		assertFalse(tf.isPositiveForm());
		assertTrue(tf.pushNeg().isPositiveForm());
		assertTrue(new LNConj(new LNNeg(p), new LNNeg(q)).equals(tf.toDNF()));
	}
}
