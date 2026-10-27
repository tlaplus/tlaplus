/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved.
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
package tlc2.value.impl;

import static tlc2.value.impl.ValueFixtures.ints;

import org.jetbrains.lincheck.datastructures.Operation;
import org.junit.Test;

import tlc2.module.Bags;
import tlc2.util.FP64;
import tlc2.util.Vect;

/**
 * The bag B == (3 :> 30 @@ 1 :> 10 @@ 2 :> 20), whose domain is not
 * normalized. A worker that applies an operator of the Bags module to B while
 * another worker sorts B must still get the result for B. Each operator reads
 * the domain and the values of B, and FcnRcdValue#normalize sorts them in place.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class BagsTest extends ValueLincheckTestCase {

	/** The operator F with F(1) = F(2) = 0 and F(3) = 1. */
	private static final OpRcdValue F;

	static {
		final Vect<Value[]> domain = new Vect<>();
		final Vect<Value> values = new Vect<>();
		for (int i = 1; i <= 3; i++) {
			domain.addElement(new Value[] { IntValue.gen(i) });
			values.addElement(IntValue.gen(i == 3 ? 1 : 0));
		}
		F = new OpRcdValue(domain, values);
	}

	private final FcnRcdValue bag = unsortedFcn();

	@Override
	protected Value value() {
		return bag;
	}

	/**
	 * BagCardinality(B) must be 60. If Bags#BagCardinality reads the values of B
	 * without a lock, it may count a value twice and another not at all.
	 */
	@Operation
	public int bagCardinality() {
		return Bags.BagCardinality(bag).val;
	}

	/**
	 * B (+) (4 :> 40) must be (1 :> 10 @@ 2 :> 20 @@ 3 :> 30 @@ 4 :> 40). If
	 * Bags#BagCup reads the domain and the values of B one after the other,
	 * without a lock, it may pair a sorted domain with unsorted values, or copy 3
	 * twice.
	 */
	@Operation
	public long bagCup() {
		return Bags.BagCup(bag, new FcnRcdValue(ints(4), ints(40), true)).fingerPrint(FP64.New());
	}

	/**
	 * B (-) (1 :> 10) must be (2 :> 20 @@ 3 :> 30). If Bags#BagDiff reads the
	 * domain, the values, and whether B is normalized one after the other,
	 * without a lock, it may pair a sorted domain with unsorted values, or mark
	 * an unsorted copy as normalized.
	 */
	@Operation
	public long bagDiff() {
		return Bags.BagDiff(bag, new FcnRcdValue(ints(1), ints(10), true)).fingerPrint(FP64.New());
	}

	/**
	 * BagIn(2, B) must be TRUE. If Bags#BagIn searches the domain of B without a
	 * lock, it may miss 2.
	 */
	@Operation
	public boolean bagIn() {
		return Bags.BagIn(IntValue.gen(2), bag).getVal();
	}

	/**
	 * BagOfAll(F, B) must be (0 :> 30 @@ 1 :> 30). If Bags#BagOfAll reads the
	 * domain and the counts of B without a lock, it may pair an element with the
	 * count of another.
	 */
	@Operation
	public long bagOfAll() {
		return Bags.BagOfAll(F, bag).fingerPrint(FP64.New());
	}

	/**
	 * BagToSet(B) must be {1, 2, 3}. If Bags#BagToSet wraps the domain of B, not
	 * a copy, in a set while another worker still sorts the domain in place, the
	 * set may contain 3 twice.
	 */
	@Operation
	public long bagToSet() {
		return Bags.BagToSet(bag).fingerPrint(FP64.New());
	}

	/**
	 * BagUnion({B, 4 :> 40}) must be (1 :> 10 @@ 2 :> 20 @@ 3 :> 30 @@ 4 :> 40).
	 * If Bags#BagUnion reads the domain and the values of B one after the other,
	 * without a lock, it may pair a sorted domain with unsorted values, or copy 3
	 * twice.
	 */
	@Operation
	public long bagUnion() {
		return Bags.BagUnion(new SetEnumValue(new Value[] { bag, new FcnRcdValue(ints(4), ints(40), true) }, false))
				.fingerPrint(FP64.New());
	}

	/**
	 * CopiesIn(1, B) must be 10. If Bags#CopiesIn reads the domain and the values
	 * of B one after the other, without a lock, it may pair a sorted domain with
	 * unsorted values.
	 */
	@Operation
	public int copiesIn() {
		return Bags.CopiesIn(IntValue.gen(1), bag).val;
	}

	/**
	 * B \sqsubseteq (1 :> 10 @@ 2 :> 20 @@ 3 :> 30) must be TRUE. If
	 * Bags#SqSubseteq reads the domain and the values of B one after the other,
	 * without a lock, it may pair a sorted domain with unsorted values, such as 1
	 * with 30.
	 */
	@Operation
	public boolean sqSubseteq() {
		return Bags.SqSubseteq(bag, new FcnRcdValue(ints(1, 2, 3), ints(10, 20, 30), true)).getVal();
	}

	@Test
	public void fingerPrintAndBagCardinality() {
		modelCheckingParallel("fingerPrint", "bagCardinality");
	}

	@Test
	public void fingerPrintAndBagCup() {
		modelCheckingParallel("fingerPrint", "bagCup");
	}

	@Test
	public void fingerPrintAndBagDiff() {
		modelCheckingParallel("fingerPrint", "bagDiff");
	}

	@Test
	public void fingerPrintAndBagIn() {
		modelCheckingParallel("fingerPrint", "bagIn");
	}

	@Test
	public void fingerPrintAndBagOfAll() {
		modelCheckingParallel("fingerPrint", "bagOfAll");
	}

	@Test
	public void fingerPrintAndBagToSet() {
		modelCheckingParallel("fingerPrint", "bagToSet");
	}

	@Test
	public void fingerPrintAndBagUnion() {
		modelCheckingParallel("fingerPrint", "bagUnion");
	}

	@Test
	public void fingerPrintAndCopiesIn() {
		modelCheckingParallel("fingerPrint", "copiesIn");
	}

	@Test
	public void fingerPrintAndSqSubseteq() {
		modelCheckingParallel("fingerPrint", "sqSubseteq");
	}
}
