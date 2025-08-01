/*******************************************************************************
 * Copyright (c) 2025 Linux Foundation. All rights reserved.
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
package tla2sany.parser;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.output.LogLevel;
import tla2sany.output.RecordedSanyOutput;
import util.FilenameToStream;
import util.SimpleFilenameToStream;


/**
 * Currently, SANY's syntax parser level has its own error reporting
 * machinery distinct from the {@link tla2sany.semantic.Errors} class. Until
 * these are unified and syntax parser errors are tagged with an appropriate
 * error code, these tests ensure syntax error text is output appropriately.
 */
@RunWith(Parameterized.class)
public class ParseErrorTests {

  public static class ParseErrorTest {
    public final String moduleBody;
    public final String error;
    public ParseErrorTest(String moduleBody, String error) {
      this.moduleBody = moduleBody;
      this.error = error;
    }
    @Override
    public String toString() {
      return this.moduleBody;
    }
  }

	@Parameters(name = "{index}: {0}")
	public static ParseErrorTest[] getTestCases() {
	  return new ParseErrorTest[] {
	      new ParseErrorTest("x = 0", "Was expecting \"==== or more Module body\"\nEncountered \"x\" at line")
	  };
	}

  @Parameter
  public ParseErrorTest testCase;

  @Test
  public void testAll() throws IOException {
    Path inputFile = Files.createTempFile("SanyTest", ".tla");
    String fileName = inputFile.getFileName().toString();
    String moduleName = fileName.substring(0, fileName.length() - 4);
    String input = String.format("---- MODULE %s ----\n%s\n====", moduleName, this.testCase.moduleBody);
    Files.writeString(inputFile, input);

    final FilenameToStream fts = new SimpleFilenameToStream(inputFile.getParent().toString());
    final SpecObj spec = new SpecObj(inputFile.toString(), fts);
    final RecordedSanyOutput out = new RecordedSanyOutput(LogLevel.INFO);
    SANY.frontEndInitialize();
    try {
      SANY.frontEndParse(spec, out, false);
      Assert.fail("Expected parse failure.");
    } catch (ParseException e) {
      Assert.assertTrue(out.toString(), out.toString().contains(this.testCase.error));
    }
  }
}
