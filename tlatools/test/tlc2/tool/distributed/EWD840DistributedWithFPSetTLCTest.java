/*******************************************************************************
 * Copyright (c) 2016 Microsoft Research. All rights reserved. 
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
package tlc2.tool.distributed;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import tlc2.output.EC;

public class EWD840DistributedWithFPSetTLCTest extends DistributedTLCTestCase {

	public EWD840DistributedWithFPSetTLCTest() {
		super("MC06", BASE_PATH + "EWD840" + File.separator, new String[] {"-deadlock"}, 1);
	}

	@Test
	public void test() {
		// Can we do any assertions here?
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		// Number of generated states differs because of distributed TLC
		assertTrue(recorder.recordedWithStringValueAt(EC.TLC_STATS, "114942", 1));
		assertTrue(recorder.recordedWithStringValueAt(EC.TLC_STATS, "0", 2));
		assertFalse(recorder.recorded(EC.GENERAL));
	}
}
