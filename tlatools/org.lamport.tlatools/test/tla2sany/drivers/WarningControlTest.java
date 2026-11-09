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
package tla2sany.drivers;

import java.io.File;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;

import tlc2.tool.CommonTestCase;
import tla2sany.SANYTest;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.output.LogLevel;
import tla2sany.output.RecordedSanyOutput;
import tla2sany.semantic.ErrorCode;
import util.SimpleFilenameToStream;
import util.TestPrintStream;
import util.ToolIO;

/**
 * Tests for the {@code -suppressMessages} and {@code -messagesAsErrors} CLI
 * flags and corresponding {@link SanySettings} API fields, as part of GitHub
 * issue #1186.
 *
 * <p>
 * The fixture spec {@code W4802_Pre_Test.tla} triggers warning 4802
 * ({@link ErrorCode#RECORD_CONSTRUCTOR_FIELD_NAME_CLASH}) reliably: it defines
 * {@code Foo == TRUE} and then constructs {@code [Foo |-> 42]}, where the field
 * name {@code Foo} clashes with the existing definition.
 */
public class WarningControlTest extends SANYTest {

	private static final String TEST_SPEC_DIR = CommonTestCase.BASE_DIR + File.separator + "test" + File.separator
			+ "tla2sany" + File.separator + "semantic" + File.separator + "error_corpus" + File.separator;
	private static final String TEST_SPEC_PATH = TEST_SPEC_DIR + "W4802_Pre_Test.tla";

	private static final ErrorCode CODE_4802 = ErrorCode.RECORD_CONSTRUCTOR_FIELD_NAME_CLASH;

	// ── API-level tests: SANY.parse() + SanySettings ─────────────────────────

	/**
	 * Baseline: with default settings the warning fires and SANY succeeds.
	 */
	@Test
	public void testWarningAppearsWithDefaultSettings() throws Exception {
		final RecordedSanyOutput out = new RecordedSanyOutput(LogLevel.WARNING);
		final SpecObj spec = new SpecObj(TEST_SPEC_PATH, new SimpleFilenameToStream(TEST_SPEC_DIR));
		final SanyExitCode result = SANY.parse(spec, TEST_SPEC_PATH, out, SanySettings.defaultSettings());

		Assert.assertEquals(SanyExitCode.OK, result);
		Assert.assertTrue("Expected field-name-clash warning in output", out.getMessages().stream()
				.anyMatch(m -> m.getLevel() == LogLevel.WARNING && m.getText().contains("Foo")));
	}

	/**
	 * Suppressing code 4802 via {@link SanySettings#suppressedCodes} silences the
	 * warning and SANY still succeeds.
	 */
	@Test
	public void testSuppressMessagesViaSettings() throws Exception {
		final RecordedSanyOutput out = new RecordedSanyOutput(LogLevel.WARNING);
		final SpecObj spec = new SpecObj(TEST_SPEC_PATH, new SimpleFilenameToStream(TEST_SPEC_DIR));
		final SanySettings settings = new SanySettings(true, true, true, true, Set.of(CODE_4802), Set.of());
		final SanyExitCode result = SANY.parse(spec, TEST_SPEC_PATH, out, settings);

		Assert.assertEquals(SanyExitCode.OK, result);
		Assert.assertFalse("Expected no warnings in output when code is suppressed",
				out.getMessages().stream().anyMatch(m -> m.getLevel() == LogLevel.WARNING));
	}

	/**
	 * Elevating code 4802 via {@link SanySettings#messagesAsErrorCodes} causes
	 * {@link SanyExitCode#SEMANTIC_ANALYSIS_OR_LEVEL_CHECKING_FAILURE} and emits a
	 * "Warning treated as error" message at ERROR level.
	 */
	@Test
	public void testMessagesAsErrorsViaSettings() throws Exception {
		final RecordedSanyOutput out = new RecordedSanyOutput(LogLevel.WARNING);
		final SpecObj spec = new SpecObj(TEST_SPEC_PATH, new SimpleFilenameToStream(TEST_SPEC_DIR));
		final SanySettings settings = new SanySettings(true, // doStrictErrorCodes
				true, true, true, true, Set.of(), Set.of(CODE_4802));
		final SanyExitCode result = SANY.parse(spec, TEST_SPEC_PATH, out, settings);

		Assert.assertEquals(SanyExitCode.SEMANTIC_ANALYSIS_OR_LEVEL_CHECKING_FAILURE, result);
		Assert.assertTrue("Expected 'Warning treated as error' message at ERROR level", out.getMessages().stream()
				.anyMatch(m -> m.getLevel() == LogLevel.ERROR && m.getText().contains("Warning treated as error")));
	}

	// ── CLI tests: SANYmain0() ────────────────────────────────────────────────

	/**
	 * {@code -suppressMessages 4802} silences the warning; SANY exits cleanly even
	 * with {@code -error-codes}.
	 */
	@Test
	public void testCLISuppressMessagesSilencesWarning() throws SANYExitException {
		final TestPrintStream out = new TestPrintStream();
		ToolIO.out = out;
		ToolIO.err = out;
		SANY.SANYmain0(new String[] { "-suppressMessages", "4802", "-error-codes", TEST_SPEC_PATH });
		out.assertNoSubstring("field name");
	}

	/**
	 * {@code -messagesAsErrors 4802} causes a {@link SANYExitException} with code
	 * {@link SanyExitCode#SEMANTIC_ANALYSIS_OR_LEVEL_CHECKING_FAILURE} and prints
	 * "Warning treated as error".
	 */
	@Test
	public void testCLIMessagesAsErrorsCausesFailure() {
		final TestPrintStream out = new TestPrintStream();
		ToolIO.out = out;
		ToolIO.err = out;
		try {
			SANY.SANYmain0(new String[] { "-messagesAsErrors", "4802", "-error-codes", TEST_SPEC_PATH });
			Assert.fail("Expected SANYExitException for elevated warning");
		} catch (SANYExitException e) {
			Assert.assertEquals(SanyExitCode.SEMANTIC_ANALYSIS_OR_LEVEL_CHECKING_FAILURE, e.getEnumeratedExitCode());
		}
		out.assertSubstring("Warning treated as error");
	}

	/**
	 * A comma-separated list of codes works; both codes must be valid SANY codes
	 * (4800 and 4802).
	 */
	@Test
	public void testCLIMultipleCodesSuppressed() throws SANYExitException {
		final TestPrintStream out = new TestPrintStream();
		ToolIO.out = out;
		ToolIO.err = out;
		SANY.SANYmain0(new String[] { "-suppressMessages", "4800,4802", "-error-codes", TEST_SPEC_PATH });
		out.assertNoSubstring("field name");
	}

	/**
	 * An unknown code in {@code -suppressMessages} causes an error exit and reports
	 * "unknown message code".
	 */
	@Test
	public void testCLIUnknownCodeInSuppressMessages() {
		final TestPrintStream out = new TestPrintStream();
		ToolIO.out = out;
		ToolIO.err = out;
		try {
			SANY.SANYmain0(new String[] { "-suppressMessages", "9999", TEST_SPEC_PATH });
			Assert.fail("Expected SANYExitException for unknown code");
		} catch (SANYExitException e) {
			Assert.assertEquals(SanyExitCode.ERROR, e.getEnumeratedExitCode());
		}
		out.assertSubstring("unknown message code");
	}

	/**
	 * An unknown code in {@code -messagesAsErrors} causes an error exit and reports
	 * "unknown message code".
	 */
	@Test
	public void testCLIUnknownCodeInMessagesAsErrors() {
		final TestPrintStream out = new TestPrintStream();
		ToolIO.out = out;
		ToolIO.err = out;
		try {
			SANY.SANYmain0(new String[] { "-messagesAsErrors", "9999", TEST_SPEC_PATH });
			Assert.fail("Expected SANYExitException for unknown code");
		} catch (SANYExitException e) {
			Assert.assertEquals(SanyExitCode.ERROR, e.getEnumeratedExitCode());
		}
		out.assertSubstring("unknown message code");
	}

	/**
	 * {@code -suppressMessages} with no following argument reports an error.
	 */
	@Test
	public void testCLISuppressMessagesMissingArgument() {
		try {
			SANY.SANYmain0(new String[] { "-suppressMessages" });
			Assert.fail("Expected SANYExitException when argument is missing");
		} catch (SANYExitException e) {
			Assert.assertEquals(SanyExitCode.ERROR, e.getEnumeratedExitCode());
		}
	}

	/**
	 * {@code -messagesAsErrors} with no following argument reports an error.
	 */
	@Test
	public void testCLIMessagesAsErrorsMissingArgument() {
		try {
			SANY.SANYmain0(new String[] { "-messagesAsErrors" });
			Assert.fail("Expected SANYExitException when argument is missing");
		} catch (SANYExitException e) {
			Assert.assertEquals(SanyExitCode.ERROR, e.getEnumeratedExitCode());
		}
	}

	/**
	 * Passing the same code to both -suppressMessages and -messagesAsErrors causes
	 * an error exit and reports "overlap for codes".
	 */
	@Test
	public void testCLIOverlapBetweenSuppressMessagesAndMessagesAsErrors() throws SANYExitException {
		final TestPrintStream out = new TestPrintStream();
		ToolIO.out = out;
		ToolIO.err = out;
		try {
			SANY.SANYmain0(new String[] { "-suppressMessages", "4800", "-messagesAsErrors", "4800", TEST_SPEC_PATH });
			Assert.fail("Expected SANYExitException for overlap");
		} catch (SANYExitException e) {
			Assert.assertEquals(SanyExitCode.ERROR, e.getEnumeratedExitCode());
		}
		out.assertSubstring("codes were set to both -suppressMessages and -messagesAsErrors");
	}

	/**
	 * Passing an error-level code (4200 = SYMBOL_UNDEFINED) to
	 * {@code -suppressMessages} is rejected with an error and a message indicating
	 * the code is not suppressable.
	 */
	@Test
	public void testCLIErrorLevelCodeInSuppressMessages() {
		final TestPrintStream out = new TestPrintStream();
		ToolIO.out = out;
		ToolIO.err = out;
		try {
			SANY.SANYmain0(new String[] { "-suppressMessages", "4200", TEST_SPEC_PATH });
			Assert.fail("Expected SANYExitException for non-suppressable code");
		} catch (SANYExitException e) {
			Assert.assertEquals(SanyExitCode.ERROR, e.getEnumeratedExitCode());
		}
		out.assertSubstring("cannot be suppressed");
	}
}
