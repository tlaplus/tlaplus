package org.lamport.tla.toolbox.tool.tlc.util;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import junit.framework.Assert;
import junit.framework.TestCase;

/**
 * Test for toolkit methods
 * @author Simon Zambrovski
 * @version $Id$
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
}
