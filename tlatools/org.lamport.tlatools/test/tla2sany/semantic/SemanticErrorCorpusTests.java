/*******************************************************************************
 * Copyright (c) 2024 Linux Foundation. All rights reserved.
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

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.PathMatcher;
import java.nio.file.Paths;
import java.util.Comparator;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.junit.Assert;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.junit.Test;

import tla2sany.drivers.SANY;
import tla2sany.drivers.SemanticException;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.parser.ParseException;
import tla2sany.output.LogLevel;
import tla2sany.output.SanyOutput;
import tla2sany.output.SimpleSanyOutput;
import tla2sany.semantic.Errors.ErrorDetails;
import tlc2.tool.CommonTestCase;
import util.FilenameToStream;
import util.SimpleFilenameToStream;
import util.WrongInvocationException;

/**
 * This class parses a set of small .tla files which should trigger specific
 * error codes identified by their filename. By testing SANY's error handling
 * & validating that it rejects certain parse inputs, these tests form the
 * complement of the {@link SemanticCorpusTests}.
 */
@RunWith(Parameterized.class)
public class SemanticErrorCorpusTests {

  private static class SemanticErrorTestCase {

    /**
     * A regex pattern to match & extract an error code from a filename.
     * Matches files of the form:
     * - W1004_Test.tla
     * - E2006_Test.tla
     * - E2006_SpecificTestCaseName_Test.tla
     */
    private static final Pattern FILENAME_PATTERN = Pattern.compile("[W|E](?<code>\\d+)(_(?<case>\\S+))?_Test\\.tla");

    public final Path modulePath;
    public final ErrorCode expectedCode;
    public SemanticErrorTestCase(final Path modulePath) {
      this.modulePath = modulePath;
      final String filename = modulePath.getFileName().toString();
      final Matcher m = FILENAME_PATTERN.matcher(filename);
      if (!m.matches()) {
          throw new IllegalArgumentException(filename);
      }
      final int errorCode = Integer.parseInt(m.group("code"));
      this.expectedCode = ErrorCode.fromStandardValue(errorCode);
    }
    // Used by JUnit to identify this test case.
    public String toString() {
      return this.modulePath.getFileName().toString();
    }
  }

  /**
   * The directory containing all the semantic error corpus test files.
   */
  private static final String CORPUS_DIR = "test/tla2sany/semantic/error_corpus";

  /**
   * Finds all semantic error corpus test files.
   * TODO: Modify this so it works when tests are run against tla2tools.jar,
   * where files cannot be resolved using a {@link Path} in this way. Likely
   * this will need to hook into resource loading logic exposed in the new
   * SANY API.
   */
  @Parameters(name = "{index}: {0}")
  public static List<SemanticErrorTestCase> getTestFiles() throws IOException {
    Path corpusDir = Paths.get(CommonTestCase.BASE_DIR).resolve(CORPUS_DIR);
    PathMatcher matcher = FileSystems.getDefault().getPathMatcher("glob:**/*Test.tla");
    return Files
      .walk(corpusDir)
      .filter(matcher::matches)
      .map(SemanticErrorTestCase::new)
      .sorted(Comparator.comparing(SemanticErrorTestCase::toString))
      .collect(Collectors.toList());
  }

  /**
   * The current semantic error corpus file to test.
   */
  @Parameter
  public SemanticErrorTestCase testCase;

  /**
   * Check to ensure the correct error code is triggered by the parse input.
   */
  @Test
  public void test() {
    final Errors log = parse(this.testCase.modulePath);
    switch (this.testCase.expectedCode.getSeverityLevel()) {
      case WARNING: {
        Assert.assertTrue(log.toString(), log.isSuccess());
        final List<ErrorDetails> actual = log.getWarningDetails();
        Assert.assertFalse(log.toString(), actual.stream().anyMatch(error -> error.getCode() == ErrorCode.SUSPECTED_UNREACHABLE_CHECK));
        Assert.assertTrue(log.toString(), actual.stream().anyMatch(error -> error.getCode() == this.testCase.expectedCode));
        break;
      } case ERROR: {
        Assert.assertTrue(log.toString(), log.isFailure());
        final List<ErrorDetails> actual = log.getErrorDetails();
        Assert.assertFalse(log.toString(), actual.stream().anyMatch(error -> error.getCode() == ErrorCode.SUSPECTED_UNREACHABLE_CHECK));
        Assert.assertTrue(log.toString(), actual.stream().anyMatch(error -> error.getCode() == this.testCase.expectedCode));
        break;
      } default: {
        Assert.fail(this.testCase.toString());
      }
    }
  }

  /**
   * Parse the spec; we expect the parse to fail, so catch any thrown
   * exceptions and return the error log.
   *
   * @param rootModulePath The path to the module to parse.
   * @return A log of parse errors.
   */
  private static Errors parse(Path rootModulePath) {
    final FilenameToStream fts = new SimpleFilenameToStream(rootModulePath.getParent().toString());
    final SpecObj spec = new SpecObj(rootModulePath.toString(), fts);
    final ByteArrayOutputStream output = new ByteArrayOutputStream();
    final PrintStream outStream = new PrintStream(output);
    final SanyOutput out = new SimpleSanyOutput(outStream, LogLevel.INFO);
    SANY.frontEndInitialize();
    try {
      SANY.frontEndParse(spec, out);
      if (spec.parseErrors.getNumMessages() > 0) {
        return spec.parseErrors;
      }
    } catch (ParseException e) {
      Assert.assertNotEquals(e.toString() + output.toString(), 0, spec.parseErrors.getNumMessages());
      return spec.parseErrors;
    } try {
      SANY.frontEndSemanticAnalysis(spec, out, true);
    } catch (SemanticException e) {
      return spec.semanticErrors;
    } catch (WrongInvocationException e) {
      // https://github.com/tlaplus/tlaplus/issues/1149
      return spec.semanticErrors;
    }
    return spec.semanticErrors;
  }
}
