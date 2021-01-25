/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved.
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
package tlc2.tool;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;
import util.TestPrintStream;
import util.ToolIO;

public class Github362Test extends ModelCheckerTestCase {

  private TestPrintStream testPrintStream;

  public Github362Test() {
    super("Github362", new String[] {"-config", "Github362.tla"},ExitStatus.SUCCESS);
  }

  @Override
  public void beforeSetUp() {
    testPrintStream = new TestPrintStream();
    ToolIO.out = testPrintStream;
  }

  @Test
  public void testSpec() {
    testPrintStream.assertSubstring("<<\"Evaluated initial state in A; overloadedName is: \", \"fizzbuzz\">>");
    testPrintStream.assertSubstring("<<\"From A's perspective, B's overloadedName is: \", \"x\">>");
    testPrintStream.assertSubstring("<<\"Evaluating initial state in B; overloadedName is \", \"x\">>");

    testPrintStream.assertSubstring("<<\"Evaluated initial state in A; overloadedConst is: \", 4711>>");
    testPrintStream.assertSubstring("<<\"From A's perspective, B's overloadedConst is: \", 42>>");
    testPrintStream.assertSubstring("<<\"Evaluating initial state in B; overloadedConst is \", 42>>");
    
    assertTrue(recorder.recorded(EC.TLC_FINISHED));
    assertTrue(recorder.recorded(EC.TLC_SUCCESS));
  }

}
