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

/**
 * The set S == {3, 1, 2}, whose elements are not normalized. A worker that
 * evaluates 1 \in S while another worker sorts S must still get TRUE. If
 * SetEnumValue#member searches the elements of S without a lock while another
 * worker sorts them in place, it may miss 1.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class SetEnumValueMemberTest extends ValueLincheckTestCase {

	private final SetEnumValue set = unsortedSet();

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
