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

import static tlc2.value.impl.ValueFixtures.evaluatingTo;
import static tlc2.value.impl.ValueFixtures.ints;
import static tlc2.value.impl.ValueFixtures.setPred;

import org.jetbrains.lincheck.datastructures.Operation;
import org.junit.Test;

/**
 * The set S == {x \in {2, 1} : FALSE}, which TLC has not yet enumerated. A
 * worker that evaluates 1 \in S while another worker fingerprints S must still
 * get FALSE. Fingerprinting replaces the set {2, 1} in S with the enumeration
 * of S, which is empty. If SetPredValue#member decides whether S is enumerated
 * apart from reading the set that S holds, it may take {2, 1} for the
 * enumeration and skip the predicate, and so get TRUE.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class SetPredValueMemberTest extends ValueLincheckTestCase {

	private final SetPredValue set = setPred(new SetEnumValue(ints(2, 1), false), evaluatingTo(BoolValue.ValFalse));

	@Override
	protected Value value() {
		return set;
	}

	@Operation
	public boolean member() {
		return set.member(IntValue.gen(1));
	}

	@Test
	public void fingerPrintAndMember() {
		modelCheckingParallel("fingerPrint", "member");
	}
}
