package org.lamport.tla.toolbox.tool.tlc.ui.util;

import junit.framework.TestCase;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class FormHelperTest extends TestCase
{

    /* (non-Javadoc)
     * @see junit.framework.TestCase#setUp()
     */
    protected void setUp() throws Exception
    {
        super.setUp();
    }

    
    public void testIsIdetifier()
    {
        
        assertFalse(FormHelper.isIdentifier(""));
        assertFalse(FormHelper.isIdentifier(null));
        assertTrue(FormHelper.isIdentifier("ksdhf"));
        assertTrue(FormHelper.isIdentifier("090a0909"));
        assertFalse(FormHelper.isIdentifier("ksd hf"));
        
        assertFalse(FormHelper.isIdentifier("ksd hf"));
        assertFalse(FormHelper.isIdentifier("0000"));
        assertFalse(FormHelper.isIdentifier("000_111"));
    }
}
