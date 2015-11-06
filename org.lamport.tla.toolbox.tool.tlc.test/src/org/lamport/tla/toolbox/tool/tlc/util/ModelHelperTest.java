/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
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
 *   Simon Zambrovski - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.tool.tlc.util;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.junit.Assert;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;

import junit.framework.TestCase;

/**
 * Test for toolkit methods
 */
public class ModelHelperTest extends TestCase
{

    /* (non-Javadoc)
     * @see junit.framework.TestCase#setUp()
     */
    protected void setUp() throws Exception
    {
        super.setUp();
    }

    /**
     * Test method for {@link org.lamport.tla.toolbox.tool.tlc.util.ModelHelper#getCheckpoints(org.eclipse.debug.core.ILaunchConfiguration)}.
     */
    public void testRegexGetCheckpoints()
    {
        String input = "09-08-13-15-07-32";
        String input2 = "hello dolly";
        
        Pattern pattern = Pattern.compile("[0-9]{2}-[0-9]{2}-[0-9]{2}-[0-9]{2}-[0-9]{2}-[0-9]{2}");
        
        Matcher matcher = pattern.matcher(input);
        Assert.assertTrue(matcher.matches());

        Matcher matcher2 = pattern.matcher(input2);
        Assert.assertFalse(matcher2.matches());
    }
    
    public void testStripSymmetry() {
    	final List<String> serializedList = new ArrayList<String>();
    	serializedList.add("Procs;;{A, B};1;1");
    	
    	// Symmetry not stripped
    	List<Assignment> deserializeAssignmentList = ModelHelper.deserializeAssignmentList(serializedList);
    	assertEquals(1, deserializeAssignmentList.size());
    	assertTrue(deserializeAssignmentList.get(0).isSymmetricalSet());
    	
    	// Symmetry stripped
    	deserializeAssignmentList = ModelHelper.deserializeAssignmentList(serializedList, true);
    	assertEquals(1, deserializeAssignmentList.size());
    	assertFalse(deserializeAssignmentList.get(0).isSymmetricalSet());
    }
}
