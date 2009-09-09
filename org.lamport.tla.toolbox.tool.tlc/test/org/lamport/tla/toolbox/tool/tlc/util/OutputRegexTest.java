package org.lamport.tla.toolbox.tool.tlc.util;

import java.util.regex.Matcher;

import org.eclipse.jface.text.IRegion;

import tla2sany.st.Location;

import junit.framework.TestCase;

/**
 * Tests the regex matcher for generated ids
 * @author Simon Zambrovski
 * @version $Id$
 */
public class OutputRegexTest extends TestCase
{

    private String id;
    private final String random = " ksj fhksd hfskd hfsdk hsdk hj ";
    private final String random2 = " lksjfh ksfh ksdhf sdkhf sdk hj ";
    private final String location = "line 11, col 8 to line 14, col 26 of module MTest3";
    private final String ulocation = "In module MTest3";

    protected void setUp() throws Exception
    {
        super.setUp();
        id = ModelWriter.getValidIdentifier(ModelWriter.CONSTANT_SCHEME);
    }

    public void testRegexMatchId()
    {
        // exact match
        assertTrue(ModelWriter.ID_MATCHER.matcher(id).matches());
    }

    public void testRegexFindId()
    {
        Matcher matcher = ModelWriter.ID_MATCHER.matcher(random + id + random2);
        // find the id inside of the text
        assertTrue(matcher.find());
        // start points to the beginning
        assertEquals(random.length(), matcher.start());
        // end to the end
        assertEquals(id.length(), matcher.end() - matcher.start());
        // here is how the content can be extracted
        assertEquals(id, (random + id + random2).substring(matcher.start(), matcher.end()));
        // not a false positive
        assertFalse(ModelWriter.ID_MATCHER.matcher(random + random2).find());
    }

    public void testRegexFindManyIds()
    {
        Matcher matcher = ModelWriter.ID_MATCHER.matcher(random + id + random2 + id + random);
        // find the id inside of the text
        assertTrue(matcher.find());
        // start points to the beginning
        assertEquals(random.length(), matcher.start());
        // find the id inside of the text
        assertTrue(matcher.find());
        // start points to the beginning
        assertEquals(random.length() + id.length() + random2.length(), matcher.start());
    }

    /**
     * Method test
     */
    public void testFindIds()
    {
        IRegion[] regions = ModelWriter.findIds(random + id + random2 + id + random);
        assertEquals(2, regions.length);
        // start points to the beginning
        assertEquals(random.length(), regions[0].getOffset());
        // start points to the beginning
        assertEquals(random.length() + id.length() + random2.length(), regions[1].getOffset());
    }

    public void testRegexMatchLocation()
    {
        Matcher matcher = Location.LOCATION_MATCHER.matcher(location);
        assertTrue(matcher.matches());
    }

    public void testRegexFindLocation()
    {
        Matcher matcher = Location.LOCATION_MATCHER.matcher(random + location + random2 + location + random);
        // find the id inside of the text
        assertTrue(matcher.find());
        // start points to the beginning
        assertEquals(random.length(), matcher.start());
        // find the id inside of the text
        assertTrue(matcher.find());
        // start points to the beginning
        assertEquals(random.length() + location.length() + random2.length(), matcher.start());

        // get the groups
        assertEquals(5, matcher.groupCount());
        // bl
        assertEquals(11, Integer.parseInt(matcher.group(1)));
        // bc
        assertEquals(8, Integer.parseInt(matcher.group(2)));
        // el
        assertEquals(14, Integer.parseInt(matcher.group(3)));
        // ec
        assertEquals(26, Integer.parseInt(matcher.group(4)));
        // module
        assertEquals("MTest3", matcher.group(5));
    }

    public void testRegex2FindLocation()
    {
        Matcher matcher = Location.LOCATION_MATCHER2.matcher(random + ulocation + random);
        // find the id inside of the text
        assertTrue(matcher.find());

        // get the groups
        assertEquals(1, matcher.groupCount());
        // module
        assertEquals("MTest3", matcher.group(1));
    }

    /**
     * Method test
     */
    public void testFindLocations()
    {
        IRegion[] regions = ModelHelper.findLocations(random + location + random2 + location + random);
        assertEquals(2, regions.length);
        // start points to the beginning
        assertEquals(random.length(), regions[0].getOffset());
        // start points to the beginning
        assertEquals(random.length() + location.length() + random2.length(), regions[1].getOffset());
    }

    public void testLocationParsing()
    {
        String inputString = random + location + random2 + location + random;
        IRegion[] regions = ModelHelper.findLocations(inputString);
        assertEquals(2, regions.length);

        String loc1 = inputString.substring(regions[0].getOffset(), regions[0].getOffset() + regions[0].getLength());
        String loc2 = inputString.substring(regions[1].getOffset(), regions[1].getOffset() + regions[1].getLength());

        assertEquals("MTest3", Location.parseLocation(loc1).source());
        assertEquals("MTest3", Location.parseLocation(loc2).source());
    }

    public void testLocationParsing2()
    {
        String inputString = random + location + random2 + location + random;
        Matcher matcher = Location.LOCATION_MATCHER.matcher(inputString);
        if (matcher.find())
        {
            String locationString = matcher.group();
            Location location = Location.parseLocation(locationString);
            assertEquals("MTest3", location.source());
        } else
        {
            fail();
        }
    }

}
