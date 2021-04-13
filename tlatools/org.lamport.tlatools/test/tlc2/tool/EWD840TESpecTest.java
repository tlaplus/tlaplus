/*******************************************************************************
 * Copyright (c) 2016 Microsoft Research. All rights reserved. 
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

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.junit.Test;

import tlc2.TraceExpressionTestCase;
import tlc2.output.EC;

public class EWD840TESpecTest extends TraceExpressionTestCase {
    
	public EWD840TESpecTest() {
        super("EWD840", "GeneratedTESpecs", new String[] {}, EC.ExitStatus.VIOLATION_LIVENESS, 
            new HashMap<String, Object>() {{
                put("expectedJsonPath", BASE_PATH + "GeneratedTESpecs" + File.separator + "EWD840_TTrace_JsonOutput.json");                
            }});
	}
        
    @Test
	public void test() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValueAt(EC.TLC_STATS, "1", 1));
		assertTrue(recorder.recordedWithStringValueAt(EC.TLC_STATS, "0", 2));
		assertFalse(recorder.recorded(EC.GENERAL));

        final List<String> expectedTrace = new ArrayList<String>();
		expectedTrace.add(
            "/\\ tpos = 0\n" + 
            "/\\ active = ( 0 :> FALSE @@\n" +
            "  1 :> FALSE @@\n" +
            "  2 :> FALSE @@\n" +
            "  3 :> FALSE @@\n" +
            "  4 :> FALSE @@\n" +
            "  5 :> FALSE @@\n" +
            "  6 :> FALSE @@\n" +
            "  7 :> FALSE @@\n" +
            "  8 :> FALSE @@\n" +
            "  9 :> FALSE )\n" +
            "/\\ tcolor = \"black\"\n" +
            "/\\ color = ( 0 :> \"white\" @@\n" +
            "  1 :> \"white\" @@\n" +
            "  2 :> \"white\" @@\n" +
            "  3 :> \"white\" @@\n" +
            "  4 :> \"white\" @@\n" +
            "  5 :> \"white\" @@\n" +
            "  6 :> \"white\" @@\n" +
            "  7 :> \"white\" @@\n" +
            "  8 :> \"white\" @@\n" +
            "  9 :> \"white\" )");
        assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);
	}
}
