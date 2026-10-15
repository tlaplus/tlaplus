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

import static tlc2.value.impl.ValueFixtures.sortedSet;

import org.jetbrains.lincheck.datastructures.Operation;
import org.junit.Test;

/**
 * The function f == (3 :> 30 @@ 1 :> 10 @@ 2 :> 20), whose domain is not
 * normalized. A worker that evaluates f \in [{1, 2, 3} -> {10, 20, 30}] while
 * another worker sorts f must still get TRUE. If SetOfFcnsValue#member reads
 * the domain or the values of f while FcnRcdValue#normalize sorts them in
 * place, it may read an element twice and miss another.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class SetOfFcnsValueMemberTest extends ValueLincheckTestCase {

	private static final SetOfFcnsValue SET = new SetOfFcnsValue(sortedSet(1, 2, 3), sortedSet(10, 20, 30));

	private final FcnRcdValue fcn = unsortedFcn();

	@Override
	protected Value value() {
		return fcn;
	}

	@Operation
	public boolean member() {
		return SET.member(fcn);
	}

	@Test
	public void fingerPrintAndMember() {
		modelCheckingParallel("fingerPrint", "member");
	}
}
