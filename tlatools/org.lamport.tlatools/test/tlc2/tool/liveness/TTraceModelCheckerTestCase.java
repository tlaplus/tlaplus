/*******************************************************************************
 * Copyright (c) 2021 Microsoft Research. All rights reserved. 
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
package tlc2.tool.liveness;

import java.io.File;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.stream.Stream;

import org.junit.Assume;
import org.junit.Before;

import util.FilenameToStream;
import util.SimpleFilenameToStream;
import util.TLAConstants;

public abstract class TTraceModelCheckerTestCase extends ModelCheckerTestCase {

	// Make the generated stuff go into the target/ folder of the org.lamport.tlatools folder.
	private static final String GEN_SPEC_PATH = ".." + File.separator + "target" + File.separator + "GeneratedTESpecs";

	public static String getPath(Class<? extends ModelCheckerTestCase> clazz) {
		return BASE_PATH + GEN_SPEC_PATH + File.separator + getSpecFileName(clazz);
	}

	private static String getSpecFileName(Class<?> clazz) {
		return clazz.getSimpleName() + TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME
				+ TLAConstants.Files.TLA_EXTENSION;
	}
	
	private final Class<?> clazz;
	// Path to the original spec (not the trace spec)
	private final String specPath;

	public String getModuleName() {
		return clazz.getSimpleName() + TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME;
	}
	
	public TTraceModelCheckerTestCase(final Class<?> clazz, final String path, final int exitStatus) {
		super(getSpecFileName(clazz), GEN_SPEC_PATH, new String[] {"-config", getSpecFileName(clazz)}, exitStatus);
		this.clazz = clazz;
		this.specPath = BASE_PATH + path;
	}

	public TTraceModelCheckerTestCase(final Class<?> clazz, final int exitStatus) {
		super(getSpecFileName(clazz), GEN_SPEC_PATH, new String[] {"-config", getSpecFileName(clazz)}, exitStatus);
		this.clazz = clazz;
		this.specPath = BASE_PATH;
	}

	public TTraceModelCheckerTestCase(final Class<?> clazz, final String[] extraArgs, final int exitStatus) {
		super(getSpecFileName(clazz), GEN_SPEC_PATH, Stream
				.concat(Arrays.stream(new String[] { "-config", getSpecFileName(clazz) }), Arrays.stream(extraArgs))
				.toArray(String[]::new), exitStatus);
		this.clazz = clazz;
		this.specPath = BASE_PATH;
	}
	
	@Before
	public void setUp() {
		beforeSetUp();

		//TODO Assume that the generated file exist.
		Path sourcePath = Paths
				.get(BASE_PATH + path + File.separator + spec);
		Assume.assumeTrue("No TE spec was generated, please run test with original spec", sourcePath.toFile().isFile());

		super.setUp();
	}

	@Override
	protected boolean noGenerateSpec() {
		return true;
	}
	
	@Override
	protected boolean doCoverage() {
		// A trace evaluation spec (TESpec) usually shows many warnings related to
		// coverage. Until those warnings are addressed or silenced in the
		// CostModelCreator/OpApplNodeWrapper, let's not report coverage for trace
		// evaluation specs.
		return false;
	}

	@Override
	protected FilenameToStream getResolver() {
		return new SimpleFilenameToStream(new String[] {specPath});
	}
}
