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
import tla2sany.semantic.Errors.ErrorDetails;
import tlc2.tool.CommonTestCase;
import util.FilenameToStream;
import util.SimpleFilenameToStream;

@RunWith(Parameterized.class)
public class SemanticErrorCorpusTests {

  private static class SemanticErrorTestCase {

    /**
     * A regex pattern to match & extract an error code from a filename.
     * Matches files of the form:
     * - W1004.tla
     * - E2006.tla
     * - E2006_SpecificTestCaseName.tla
     */
    private static final Pattern FILENAME_PATTERN = Pattern.compile("[W|E](?<code>\\d+)(_(?<case>\\S+))?\\.tla");

    public final Path modulePath;
    public final ErrorCode expectedCode;
    public final String testCaseName;
    public SemanticErrorTestCase(final Path modulePath) {
      this.modulePath = modulePath;
      final String filename = modulePath.getFileName().toString();
      final Matcher m = FILENAME_PATTERN.matcher(filename);
      if (!m.matches()) {
          throw new IllegalArgumentException(filename);
      }
      final int errorCode = Integer.parseInt(m.group("code"));
      this.expectedCode = ErrorCode.fromStandardValue(errorCode);
      final String caseName = m.group("case");
      this.testCaseName = null == caseName ? "" : caseName;
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
   */
  @Parameters(name = "{index}: {0}")
  public static List<SemanticErrorTestCase> getTestFiles() throws IOException {
    Path corpusDir = Paths.get(CommonTestCase.BASE_DIR).resolve(CORPUS_DIR);
    PathMatcher matcher = FileSystems.getDefault().getPathMatcher("glob:**/*.tla");
    return Files
      .walk(corpusDir)
      .filter(matcher::matches)
      .map(SemanticErrorTestCase::new)
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
    switch (this.testCase.expectedCode.level) {
      case WARNING: {
        final List<ErrorDetails> actual = log.getWarningDetails();
        Assert.assertEquals(1, log.getNumMessages());
        Assert.assertEquals(1, actual.size());
        Assert.assertEquals(this.testCase.expectedCode, actual.get(0).code);
        break;
      } case ERROR: {
        final List<ErrorDetails> actual = log.getErrorDetails();
        Assert.assertEquals(1, log.getNumMessages());
        Assert.assertEquals(1, log.getNumErrors());
        Assert.assertEquals(1, actual.size());
        Assert.assertEquals(this.testCase.expectedCode, actual.get(0).code);
        break;
      } case ABORT: {
        final List<ErrorDetails> actual = log.getAbortDetails();
        Assert.assertEquals(1, log.getNumMessages());
        Assert.assertEquals(1, log.getNumAbortsAndErrors());
        Assert.assertEquals(1, actual.size());
        Assert.assertEquals(this.testCase.expectedCode, actual.get(0).code);
        break;
      } default: {
        Assert.fail();
      }
    }
  }

  private static Errors parse(Path rootModulePath) {
    final FilenameToStream fts = new SimpleFilenameToStream(rootModulePath.getParent().toString());
    final SpecObj spec = new SpecObj(rootModulePath.toString(), fts);
    final ByteArrayOutputStream out = new ByteArrayOutputStream();
    SANY.frontEndInitialize();
    try {
      SANY.frontEndParse(spec, new PrintStream(out));
    } catch (ParseException e) {
      Assert.fail(e.toString() + out.toString());
    }
    try {
      SANY.frontEndSemanticAnalysis(spec, new PrintStream(out), true);
    } catch (SemanticException e) {
      return spec.semanticErrors;
    }
    return spec.semanticErrors;
  }
}
