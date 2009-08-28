package org.lamport.tla.toolbox.tool.tlc.ui.util;

import java.util.Date;

import junit.framework.TestCase;

/**
 * Tests for semantic helper
 * @author Simon Zambrovski
 * @version $Id$
 */
public class SemanticHelperTest extends TestCase
{
    private SemanticHelper helper;

    /**
     * @see junit.framework.TestCase#setUp()
     */
    protected void setUp() throws Exception
    {
        super.setUp();
        helper = new SemanticHelper();
        helper.resetModelNames();
    }
    
    public void testTest()
    {
        assertTrue(true);
    }

    /**
     * Testing the keywords
     */
    public void testKeywords()
    {
        for (int i = 0; i < ITLAReserveredWords.ALL_WORDS_ARRAY.length; i++)
        {
            // all keywords should be found
            assertEquals(SemanticHelper.KEYWORD, helper.getUsedHint(ITLAReserveredWords.ALL_WORDS_ARRAY[i]));
        }
    }

    /**
     * Test of the items on using the same page id
     */
    public void testPutIsGet()
    {
        String[] name = { "my name", "your name" };
        String[] description = { "foo", "bar" };
        Object pageKey = new Integer(1);

        // check pre-condition
        assertFalse(helper.isNameUsed(name[0]));
        assertFalse(helper.isNameUsed(name[1]));
        assertNull(helper.getUsedHint(name[0]));
        assertNull(helper.getUsedHint(name[1]));

        helper.addName(name[0], pageKey, description[0]);

        // check post-condition
        assertTrue(helper.isNameUsed(name[0]));
        assertFalse(helper.isNameUsed(name[1]));
        assertEquals(description[0], helper.getUsedHint(name[0]));
        assertNull(helper.getUsedHint(name[1]));

        helper.addName(name[1], pageKey, description[1]);

        // check post-condition
        assertTrue(helper.isNameUsed(name[0]));
        assertTrue(helper.isNameUsed(name[1]));
        assertEquals(description[0], helper.getUsedHint(name[0]));
        assertEquals(description[1], helper.getUsedHint(name[1]));
    }

    /**
     * Check the opage independence
     */
    public void testPageIndepenednce()
    {
        String name = "my name";
        String[] description = {"foo", "bar"};
        Object[] pageKey = { new Integer(1), new Date() };

        // check pre-condition
        assertFalse(helper.isNameUsed(name));
        assertNull(helper.getUsedHint(name));

        helper.addName(name, pageKey[0], description[0]);
        
        // check post-condition
        assertTrue(helper.isNameUsed(name));
        assertEquals(description[0], helper.getUsedHint(name));
        
        // adding it twice
        helper.addName(name, pageKey[1], description[1]);
        // should not change anything
        assertTrue(helper.isNameUsed(name));
        // one of the pages 
        assertTrue(helper.getUsedHint(name).equals(description[0]) || helper.getUsedHint(name).equals(description[1]));
        
        // reset the first page
        helper.resetModelNames(pageKey[0]);
        // should not change anything
        assertTrue(helper.isNameUsed(name));
        // should be still on the second page
        assertTrue(helper.getUsedHint(name).equals(description[1]));

        // reset the second page
        helper.resetModelNames(pageKey[1]);

        // should be not there
        assertFalse(helper.isNameUsed(name));
        assertNull(helper.getUsedHint(name));
    }
}
