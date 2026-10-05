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
package tlc2.util;

import static org.junit.Assert.assertNotEquals;

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;
import util.UniqueString;

/**
 * {@link FP64#Extend(long, String)} and {@link FP64#Extend(long, char)} only
 * use the low byte of each char. Thus, strings that differ only in the high
 * bytes of their chars get the same fingerprint by construction, e.g. U+00E9
 * ("é") and U+01E9 ("ǩ").
 */
@Ignore("FP64 only uses the low byte of each char")
public class FP64UnicodeTest {

	private static final String E_ACUTE = "\u00e9";
	private static final String K_CARON = "\u01e9";

	@Before
	public void setup() {
		FP64.Init();
	}

	@Test
	public void testExtendStringUsesWholeChar() {
		assertNotEquals(FP64.New("a"), FP64.New("b"));
		assertNotEquals(FP64.New(E_ACUTE), FP64.New(K_CARON));
	}

	@Test
	public void testExtendCharUsesWholeChar() {
		assertNotEquals(FP64.Extend(FP64.New(), E_ACUTE.charAt(0)), FP64.Extend(FP64.New(), K_CARON.charAt(0)));
	}

	@Test
	public void testThreeByteChars() {
		// U+2200 ("∀") and U+3200 share their low byte.
		assertNotEquals(FP64.New("\u2200"), FP64.New("\u3200"));
	}

	@Test
	public void testStringValueFingerprintsDiffer() {
		assertNotEquals(new StringValue(E_ACUTE).fingerPrint(FP64.New()),
				new StringValue(K_CARON).fingerPrint(FP64.New()));
	}

	/**
	 * {@link RecordValue#fingerPrint(long)} fingerprints its field names with
	 * {@link FP64#Extend(long, String)}.
	 */
	@Test
	public void testRecordValueFingerprintsDiffer() {
		assertNotEquals(
				new RecordValue(UniqueString.uniqueStringOf(E_ACUTE), IntValue.gen(1)).fingerPrint(FP64.New()),
				new RecordValue(UniqueString.uniqueStringOf(K_CARON), IntValue.gen(1)).fingerPrint(FP64.New()));
	}
}
