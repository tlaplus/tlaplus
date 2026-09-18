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
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tlc2.value.impl;

/**
 * Verifies singleton intervals for every possible endpoint. {@code value} and
 * {@code fp} are unconstrained JBMC inputs, not known boundary test cases.
 */
public final class IntervalValueHarness {
	public static void verify(final int test, final int value, final long fp) {
		final boolean valid;
		switch (test) {
		case 0:
			valid = verifyEnumeration(value);
			break;
		case 1:
			valid = verifyDiff(value);
			break;
		case 2:
			valid = verifyCap(value);
			break;
		case 3:
			valid = verifyCup(value);
			break;
		case 4:
			valid = verifyFingerprint(value, fp);
			break;
		default:
			return;
		}
		assert valid;
	}

	private static boolean verifyEnumeration(final int value) {
		final IntervalValue interval = new IntervalValue(value, value);
		final IntervalValue.Enumerator elements = interval.new Enumerator();
		final Value first = elements.nextElement();
		return first instanceof IntValue
				&& ((IntValue) first).val == value
				&& elements.nextElement() == null;
	}

	private static boolean verifyDiff(final int value) {
		return isSingleton(new IntervalValue(value, value).diff(emptySet()), value);
	}

	private static boolean verifyCap(final int value) {
		final IntervalValue interval = new IntervalValue(value, value);
		return isSingleton(interval.cap(interval), value);
	}

	private static boolean verifyCup(final int value) {
		return isSingleton(new IntervalValue(value, value).cup(emptySet()), value);
	}

	private static boolean verifyFingerprint(final int value, final long fp) {
		return new IntervalValue(value, value).fingerPrint(fp)
				== singletonSet(value).fingerPrint(fp);
	}

	private static SetEnumValue emptySet() {
		return new SetEnumValue(new Value[0], true);
	}

	private static SetEnumValue singletonSet(final int value) {
		return new SetEnumValue(new Value[] { IntValue.gen(value) }, true);
	}

	private static boolean isSingleton(final Value result, final int value) {
		if (!(result instanceof SetEnumValue)) {
			return false;
		}
		final ValueVec elements = ((SetEnumValue) result).elems;
		return elements.size() == 1
				&& elements.elementAt(0) instanceof IntValue
				&& ((IntValue) elements.elementAt(0)).val == value;
	}
}
