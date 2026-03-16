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
package tlc2.tool;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;

import org.junit.Test;

import tla2sany.semantic.ErrorCode;
import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;
import util.TestPrintStream;
import util.ToolIO;

public class ElevatedSanyWarning extends ModelCheckerTestCase {
    private static final String TEST_SPEC_DIR = CommonTestCase.BASE_DIR + File.separator +
            "test" + File.separator + "tla2sany" + File.separator + "semantic" + File.separator + 
            "error_corpus" + File.separator;
    private static final String TEST_SPEC_PATH = TEST_SPEC_DIR + "W4802_Pre_Test.tla";
    private static final ErrorCode CODE_4802 = ErrorCode.RECORD_CONSTRUCTOR_FIELD_NAME_CLASH;
    private TestPrintStream testPrintStream;

    public ElevatedSanyWarning() {
        super(TEST_SPEC_PATH, new String[] { "-messagesAsErrors", String.valueOf(CODE_4802.getStandardValue()) }, ExitStatus.ERROR_SPEC_PARSE);
    }

    @Override
    public void beforeSetUp() {
      testPrintStream = new TestPrintStream();
      ToolIO.out = testPrintStream;
    }
  
      @Test
    public void testSpec() {
        assertTrue(recorder.recorded(EC.TLC_PARSING_FAILED));
        testPrintStream.assertSubstring("Warning treated as error");
    }
}
