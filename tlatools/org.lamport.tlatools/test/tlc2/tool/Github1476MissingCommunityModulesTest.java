/*******************************************************************************
 * Copyright (c) 2026 Younes. All rights reserved.
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
 *   Younes - initial API and implementation
 ******************************************************************************/
package tlc2.tool;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;
import util.FilenameToStream;
import util.SimpleFilenameToStream;

public class Github1476MissingCommunityModulesTest extends ModelCheckerTestCase {

	public Github1476MissingCommunityModulesTest() {
		super("Github1476", new String[] { "-config", "Github1476.tla", "-dumpTrace", "cbor",
				"states" + File.separator + "Github1476MissingCommunityModules.cbor" }, EC.ExitStatus.ERROR_SPEC_PARSE);
	}

	// The test classpath always has the CommunityModules, so hide the module that
	// -dumpTrace cbor needs from the resolver instead.
	@Override
	protected FilenameToStream getResolver() {
		return new SimpleFilenameToStream() {
			@Override
			public TLAFile resolve(final String name, final boolean isModule) {
				return "CBOR.tla".equals(name) ? null : super.resolve(name, isModule);
			}
		};
	}

	@Override
	protected boolean noGenerateSpec() {
		return true;
	}

	@Override
	protected boolean doDumpTrace() {
		return false;
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithSubStringValue(EC.TLC_PARSING_FAILED2,
				"-dumpTrace cbor requires the CommunityModules (https://github.com/tlaplus/CommunityModules)"
						+ " on the classpath, but TLC cannot find its module CBOR."));
		assertFalse(recorder.recorded(EC.TLC_STARTING));
	}
}
