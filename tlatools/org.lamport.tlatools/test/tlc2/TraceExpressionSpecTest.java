/*******************************************************************************
 * Copyright (c) 2020 Microsoft Research. All rights reserved. 
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
package tlc2;

import java.util.Date;

import org.junit.Test;

import tlc2.tool.impl.FastTool;
import tlc2.tool.impl.Tool;
import tlc2.tool.liveness.ModelCheckerTestCase;
import util.FilenameToStream;
import util.SimpleFilenameToStream;

public abstract class TraceExpressionSpecTest extends ModelCheckerTestCase {

	private static final String OUTPUT_PATH = "states"; // Rest of tests dump stuff here.

	public TraceExpressionSpecTest(final String specName, final String configName, String mode, int exitStatus) {
		this(specName, "TESpecTest", configName, mode, exitStatus);
	}

	public TraceExpressionSpecTest(final String specName, final String path, final String configName, String mode, int exitStatus) {
		super(specName, path,
				new String[] { "-generateSpecTE", "-config", configName, "-teSpecOutDir", OUTPUT_PATH, mode },
				exitStatus);
	}

	protected FilenameToStream getResolver() {
		return new SimpleFilenameToStream(OUTPUT_PATH);
	}

	@Override
	protected boolean doCoverage() {
		return false;
	}

	@Override
	protected boolean doDump() {
		return false;
	}

	@Override
	protected boolean noGenerateSpec() {
		return false;
	}
	
	@Override
	protected boolean doDumpTrace() {
		return false;
	}

	@Test
	public void testSpec() throws Exception {
		final Date timestamp = new Date(tlc.getStartTime());
		final String traceSpecName = TraceExplorationSpec.deriveTESpecModuleName(spec, timestamp);
		doTest(new FastTool(traceSpecName, traceSpecName + ".tla", tlc.getResolver()), TraceExplorationSpec.teModuleId(timestamp));
	}

	protected abstract void doTest(Tool tool, final String id) throws Exception;
}
