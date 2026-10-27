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

import org.jetbrains.lincheck.datastructures.Operation;
import org.junit.Test;

import tlc2.value.IMVPerm;

/**
 * The permutation p == (c :> a @@ a :> b @@ b :> c) of the model values a, b,
 * and c, whose domain is not normalized. A worker that computes the group that
 * p and (a :> b @@ b :> a) generate for SYMMETRY while another worker sorts p
 * must still get all permutations of a, b, and c. If
 * MVPerms#permutationSubgroup reads the domain and the values of p while
 * FcnRcdValue#normalize sorts them in place, it may map a model value to the
 * image of another.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class MVPermsPermutationSubgroupTest extends ValueLincheckTestCase {

	// Model values compare by the order in which their names were interned, and
	// nothing interns these names before.
	private static final ModelValue A = (ModelValue) ModelValue.make("mvpermsA");
	private static final ModelValue B = (ModelValue) ModelValue.make("mvpermsB");
	private static final ModelValue C = (ModelValue) ModelValue.make("mvpermsC");

	static {
		ModelValue.setValues();
	}

	// MVPerms#permutationSubgroup fails for fewer than two generators. A set that
	// isn't normalized would normalize p when it compares p with SWAP_AB.
	private static final FcnRcdValue SWAP_AB = new FcnRcdValue(new Value[] { A, B }, new Value[] { B, A }, true);

	private final FcnRcdValue perm = new FcnRcdValue(new Value[] { C, A, B }, new Value[] { A, B, C }, false);

	@Override
	protected Value value() {
		return perm;
	}

	@Operation
	public String permutationSubgroup() {
		final StringBuilder sb = new StringBuilder();
		for (final IMVPerm p : MVPerms.permutationSubgroup(new SetEnumValue(new Value[] { perm, SWAP_AB }, true))) {
			sb.append(p.get(A)).append(p.get(B)).append(p.get(C)).append(' ');
		}
		return sb.toString();
	}

	@Test
	public void fingerPrintAndPermutationSubgroup() {
		modelCheckingParallel("fingerPrint", "permutationSubgroup");
	}
}
