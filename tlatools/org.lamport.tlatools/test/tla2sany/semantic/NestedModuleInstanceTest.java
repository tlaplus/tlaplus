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
 ******************************************************************************/
package tla2sany.semantic;

import java.io.File;

import org.junit.Assert;
import org.junit.Ignore;
import org.junit.Test;

import tla2sany.SANYTest;
import tla2sany.drivers.FrontEndException;
import tla2sany.drivers.SANY;
import tla2sany.drivers.SanySettings;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.output.LogLevel;
import tla2sany.output.SanyOutput;
import tla2sany.output.SimpleSanyOutput;
import tlc2.tool.CommonTestCase;
import util.SimpleFilenameToStream;
import util.ToolIO;

/**
 * Tests instantiating a module that is nested in the body of the module that
 * instantiates it.
 */
public class NestedModuleInstanceTest extends SANYTest {

	private static final String SPEC_DIR = CommonTestCase.BASE_PATH + "sany" + File.separator;

	/**
	 * Parses the syntax of the given spec of {@link #SPEC_DIR} and returns the
	 * diagnostics of its semantic analysis.
	 */
	private static Errors semanticErrorsOf(final String moduleName) throws FrontEndException {
		final String specPath = SPEC_DIR + moduleName + ".tla";
		final SanyOutput out = new SimpleSanyOutput(ToolIO.err, LogLevel.ERROR);
		final SpecObj spec = new SpecObj(specPath, new SimpleFilenameToStream(SPEC_DIR));
		SANY.parse(spec, specPath, out, SanySettings.defaultSettings());
		Assert.assertTrue(spec.getParseErrors().toString(), spec.getParseErrors().isSuccess());
		return spec.getSemanticErrors();
	}

	@Test
	public void testTopLevelInstanceOfNestedModule() throws FrontEndException {
		final Errors errors = semanticErrorsOf("NestedModuleTopLevelInstance");
		Assert.assertTrue(errors.toString(), errors.isSuccess());
	}

	/**
	 * Instantiating a nested module from inside a LET is as legal as doing so at
	 * the module level, but SANY rejects it with a spurious
	 * {@link ErrorCode#MODULE_REDEFINED} diagnostic that blames the nested module
	 * for conflicting with itself. Instantiating the module at the module level as
	 * well makes the diagnostic go away, which is what gives it away as a bug
	 * rather than a rule.
	 */
	@Test
	@Ignore("A nested module instantiated only from inside a LET is reported as multiply-defined")
	public void testLetInstanceOfNestedModule() throws FrontEndException {
		final Errors errors = semanticErrorsOf("NestedModuleLetInstance");
		Assert.assertTrue(errors.toString(), errors.isSuccess());
	}
}
