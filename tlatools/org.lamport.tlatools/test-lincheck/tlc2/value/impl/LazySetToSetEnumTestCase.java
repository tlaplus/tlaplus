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

import tlc2.util.FP64;

/**
 * The lazy set that the subclass creates from the component C == {3} \cup {1}.
 * A worker that enumerates the set while another worker fingerprints the set or
 * C must still get the fingerprint of the set. C enumerates 3 before 1 and is
 * not normalized, so the enumeration of the set is not normalized either.
 * Fingerprinting caches the normalized enumeration of what it fingerprints. If
 * toSetEnum reads whether the set is normalized after the enumeration, it may
 * read either cache and mark the unsorted enumeration as normalized.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public abstract class LazySetToSetEnumTestCase extends ValueLincheckTestCase {

	private final Value component = new SetCupValue(sortedSet(3), sortedSet(1));

	private final EnumerableValue set = set(component);

	/**
	 * The lazy set of the component C, which this calls once for every
	 * interleaving.
	 */
	protected abstract EnumerableValue set(Value c);

	@Override
	protected final Value value() {
		return set;
	}

	@Operation
	public long toSetEnum() {
		return set.toSetEnum().fingerPrint(FP64.New());
	}

	@Operation
	public long fingerPrintComponent() {
		return component.fingerPrint(FP64.New());
	}

	@Test
	public void fingerPrintAndToSetEnum() {
		modelCheckingParallel("fingerPrint", "toSetEnum");
	}

	@Test
	public void fingerPrintComponentAndToSetEnum() {
		modelCheckingParallel("fingerPrintComponent", "toSetEnum");
	}
}
