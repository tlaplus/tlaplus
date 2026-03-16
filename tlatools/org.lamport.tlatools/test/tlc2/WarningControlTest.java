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
package tlc2;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.util.Set;

import org.junit.After;
import org.junit.Test;

import tla2sany.semantic.ErrorCode;
import tlc2.output.EC;
import tlc2.output.MP;
import util.Assert.TLCRuntimeException;
import util.TLAConstants;
import util.ToolIO;

/**
 * Tests for the {@code -suppressMessages} and {@code -messagesAsErrors} CLI
 * flags in TLC ({@link TLC#handleParameters}), as part of GitHub issue #1186.
 *
 * <p>The test suite is split into two layers:
 * <ol>
 *   <li><em>Parameter-parsing tests</em> ({@code test*}) verify that
 *       {@link TLC#handleParameters} accepts valid inputs, registers the codes
 *       with {@link MP}, and rejects invalid inputs.</li>
 *   <li><em>Runtime-behavior tests</em> ({@code testRuntime*}) call
 *       {@link MP#printWarning} directly and verify that suppressed warnings
 *       produce no console output, and that warnings elevated to errors cause
 *       {@link TLCRuntimeException} to be thrown.</li>
 * </ol>
 */
public class WarningControlTest {

  private static final String DUMMY_SPEC = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;

  /** A known TLC (non-SANY) warning code. */
  private static final int TLC_CODE = EC.TLC_FEATURE_UNSUPPORTED;       // 2156

  /** A known SANY warning-level code (RECORD_CONSTRUCTOR_FIELD_NAME_CLASH). */
  private static final int SANY_WARNING_CODE =
      ErrorCode.RECORD_CONSTRUCTOR_FIELD_NAME_CLASH.getStandardValue();  // 4802

  /** A known SANY error-level code (SYMBOL_UNDEFINED). */
  private static final int SANY_ERROR_CODE =
      ErrorCode.SYMBOL_UNDEFINED.getStandardValue();                     // 4200

  @After
  public void tearDown() {
    MP.resetMessageControl();
    TLCGlobals.warn = true;
  }

  // === Parameter parsing: -suppressMessages ===

  /**
   * A known SANY warning code is accepted and registered in {@link MP}'s
   * suppressed set.
   */
  @Test
  public void testSuppressMessagesSanyCode() {
    final TLC tlc = new TLC();
    assertTrue(tlc.handleParameters(
        new String[]{"-suppressMessages", String.valueOf(SANY_WARNING_CODE), DUMMY_SPEC}));
    assertTrue("SANY warning code should be suppressed",
        MP.getSanySuppressedCodes().contains(ErrorCode.fromStandardValue(SANY_WARNING_CODE)));
  }

  /**
   * SANY error-level codes must be rejected when passed to
   * {@code -suppressMessages}: they are already errors and cannot be suppressed.
   */
  @Test
  public void testSuppressMessagesSanyErrorCodeFails() {
    final TLC tlc = new TLC();
    assertFalse("SANY error-level code should be rejected for -suppressMessages",
        tlc.handleParameters(
            new String[]{"-suppressMessages", String.valueOf(SANY_ERROR_CODE), DUMMY_SPEC}));
    assertTrue("No SANY codes should have been suppressed on failure",
        MP.getSanySuppressedCodes().isEmpty());
  }

  /**
   * A known TLC (non-SANY) code is accepted and registered in {@link MP}'s
   * suppressed set.
   */
  @Test
  public void testSuppressMessagesTlcCode() {
    final TLC tlc = new TLC();
    assertTrue(tlc.handleParameters(
        new String[]{"-suppressMessages", String.valueOf(TLC_CODE), DUMMY_SPEC}));
    assertTrue("TLC code should be suppressed",
        MP.getTlcSuppressedCodes().contains(TLC_CODE));
  }

  /**
   * A comma-separated list of codes suppresses all listed codes.
   */
  @Test
  public void testSuppressMessagesMultipleCodes() {
    final TLC tlc = new TLC();
    final String codes = TLC_CODE + "," + SANY_WARNING_CODE;
    assertTrue(tlc.handleParameters(new String[]{"-suppressMessages", codes, DUMMY_SPEC}));
    assertTrue(MP.getTlcSuppressedCodes().contains(TLC_CODE));
    assertTrue(MP.getSanySuppressedCodes().contains(ErrorCode.fromStandardValue(SANY_WARNING_CODE)));
  }

  /**
   * An unknown code causes {@link TLC#handleParameters} to return {@code false}
   * and no codes are registered in {@link MP}.
   */
  @Test
  public void testSuppressMessagesUnknownCodeFails() {
    final TLC tlc = new TLC();
    assertFalse("Unknown code should cause handleParameters to return false",
        tlc.handleParameters(new String[]{"-suppressMessages", "9999999", DUMMY_SPEC}));
    assertTrue("No TLC codes should have been registered on failure",
        MP.getTlcSuppressedCodes().isEmpty());
    assertTrue("No SANY codes should have been registered on failure",
        MP.getSanySuppressedCodes().isEmpty());
  }

  /**
   * Omitting the code list causes {@link TLC#handleParameters} to return
   * {@code false} (the spec filename is misinterpreted as the code and is
   * not a valid integer, so parsing fails).
   */
  @Test
  public void testSuppressMessagesMissingArgFails() {
    final TLC tlc = new TLC();
    assertFalse(tlc.handleParameters(new String[]{"-suppressMessages", DUMMY_SPEC}));
  }

  // === Parameter parsing: -messagesAsErrors ===

  /**
   * A known SANY warning-level code is accepted and registered in {@link MP}'s
   * warnings-as-errors set.
   */
  @Test
  public void testMessagesAsErrorsSanyWarningCode() {
    final TLC tlc = new TLC();
    assertTrue(tlc.handleParameters(
        new String[]{"-messagesAsErrors", String.valueOf(SANY_WARNING_CODE), DUMMY_SPEC}));
    assertTrue("SANY warning code should be registered as error",
        MP.getSanyMessagesAsErrorCodes().contains(ErrorCode.fromStandardValue(SANY_WARNING_CODE)));
  }

  /**
   * TLC codes have no WARNING-level metadata; they are accepted without level validation.
   */
  @Test
  public void testMessagesAsErrorsTlcCode() {
    final TLC tlc = new TLC();
    assertTrue(tlc.handleParameters(
        new String[]{"-messagesAsErrors", String.valueOf(TLC_CODE), DUMMY_SPEC}));
    assertTrue("TLC code should be registered as error",
        MP.getTlcMessagesAsErrorCodes().contains(TLC_CODE));
  }

  /** An unknown code causes failure. */
  @Test
  public void testMessagesAsErrorsUnknownCodeFails() {
    final TLC tlc = new TLC();
    assertFalse(tlc.handleParameters(
        new String[]{"-messagesAsErrors", "9999999", DUMMY_SPEC}));
  }

  /**
   * Omitting the code list causes {@link TLC#handleParameters} to return
   * {@code false}.
   */
  @Test
  public void testMessagesAsErrorsMissingArgFails() {
    final TLC tlc = new TLC();
    assertFalse(tlc.handleParameters(new String[]{"-messagesAsErrors", DUMMY_SPEC}));
  }

  // === Parameter parsing: conflict with -nowarning ===

  /**
   * Combining {@code -nowarning} and {@code -suppressMessages} is rejected.
   */
  @Test
  public void testNowarningConflictWithSuppressMessages() {
    final TLC tlc = new TLC();
    assertFalse("-nowarning + -suppressMessages must be rejected",
        tlc.handleParameters(new String[]{
            "-nowarning", "-suppressMessages", String.valueOf(SANY_WARNING_CODE), DUMMY_SPEC}));
  }

  /**
   * Combining {@code -nowarning} and {@code -messagesAsErrors} is rejected.
   */
  @Test
  public void testNowarningConflictWithmessagesAsErrors() {
    final TLC tlc = new TLC();
    assertFalse("-nowarning + -messagesAsErrors must be rejected",
        tlc.handleParameters(new String[]{
            "-nowarning", "-messagesAsErrors", String.valueOf(SANY_WARNING_CODE), DUMMY_SPEC}));
  }

  // === Parameter parsing: overlap between -suppressMessages and -messagesAsErrors ===

  /** The same TLC code cannot be passed to both -suppressMessages and -messagesAsErrors. */
  @Test
  public void testSameTlcCode() {
    final TLC tlc = new TLC();
    final String code = String.valueOf(TLC_CODE);
    assertFalse(tlc.handleParameters(
        new String[]{"-suppressMessages", code, "-messagesAsErrors", code, DUMMY_SPEC}));
  }

  /** The same SANY code cannot be passed to both -suppressMessages and -messagesAsErrors. */
  @Test
  public void testSameSanyCode() {
    final TLC tlc = new TLC();
    assertFalse(tlc.handleParameters(
        new String[]{"-suppressMessages", String.valueOf(SANY_WARNING_CODE), "-messagesAsErrors", String.valueOf(SANY_WARNING_CODE), DUMMY_SPEC}));
  }

  // === Runtime behavior: suppressed warnings ===

  /**
   * When a code is suppressed via {@link MP#addSuppressed}, calling
   * {@link MP#printWarning} for that code does not write anything to
   * {@link ToolIO#out}.
   */
  @Test
  public void testRuntimeSuppressedWarningProducesNoOutput() {
    final PrintStream savedOut = ToolIO.out;
    final PrintStream savedErr = ToolIO.err;
    try {
      final ByteArrayOutputStream captured = new ByteArrayOutputStream();
      final PrintStream out = new PrintStream(captured);
      ToolIO.out = out;
      ToolIO.err = out;

      MP.addTlcSuppressed(Set.of(TLC_CODE));
      MP.printWarning(TLC_CODE, "suppression-test");

      assertTrue("Suppressed warning should produce no output to ToolIO.out",
          captured.toString().isEmpty());
    } finally {
      ToolIO.out = savedOut;
      ToolIO.err = savedErr;
    }
  }

  /**
   * Without suppression the same warning <em>does</em> produce output, proving
   * the code under test actually has an effect.
   */
  @Test
  public void testRuntimeUnsuppressedWarningProducesOutput() {
    final PrintStream savedOut = ToolIO.out;
    final PrintStream savedErr = ToolIO.err;
    try {
      final ByteArrayOutputStream captured = new ByteArrayOutputStream();
      final PrintStream out = new PrintStream(captured);
      ToolIO.out = out;
      ToolIO.err = out;

      // TLC_CODE is NOT suppressed here.
      MP.printWarning(TLC_CODE, "unsuppressed-test");

      assertFalse("Unsuppressed warning should produce output to ToolIO.out",
          captured.toString().isEmpty());
    } finally {
      ToolIO.out = savedOut;
      ToolIO.err = savedErr;
    }
  }

  // === Runtime behavior: warnings elevated to errors ===

  /**
   * When a code is registered via {@link MP#addTlcMessagesAsErrors}, calling
   * {@link MP#printWarning} for that code throws {@link TLCRuntimeException}
   * instead of printing a warning.
   */
  @Test(expected = TLCRuntimeException.class)
  public void testRuntimeWarningAsErrorThrowsTLCRuntimeException() {
    MP.addTlcMessagesAsErrors(Set.of(TLC_CODE));
    MP.printWarning(TLC_CODE, "elevation-test");
    // If we reach here the exception was not thrown — the @expected annotation
    // will cause the test to fail.
  }

  /**
   * Without elevation the same {@link MP#printWarning} call does NOT throw,
   * proving the code under test actually has an effect.
   */
  @Test
  public void testRuntimeWarningWithoutElevationDoesNotThrow() {
    // TLC_CODE is NOT in WARNING_AS_ERRORS here.
    MP.printWarning(TLC_CODE, "no-elevation-test");
    // Reaching this point means no exception was thrown — test passes.
  }
}
