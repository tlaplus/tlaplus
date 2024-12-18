/*
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
 *   Finn Hackett - initial test, related to TLC string deserialization support
 ******************************************************************************/
package tlc2.value;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class StringDeserializeTLCTest extends ModelCheckerTestCase {
	public StringDeserializeTLCTest() {
		super("StringDeserialize");
	}
	
	@Before
	public void setUp() {
		// Resolve the .vos file against BASE_PATH in Java. TLC's working directory
		// varies depending on testing setup, so we can't reliably write a relative
		// path in the TLA+ (normally we're resolving other specs, which works by default,
		// but resolving data files like this is much less common).
		final String vosFileName = BASE_PATH + "StringDeserialize.vos";
		System.setProperty("StringDeserializeTLCTest.vosFileName", vosFileName);
		super.setUp();
	}
	
	@Test
	public void test() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
	}
}
