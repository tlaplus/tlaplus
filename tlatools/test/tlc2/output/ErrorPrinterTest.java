package tlc2.output;

import static org.junit.Assert.assertEquals;

import org.junit.Before;
import org.junit.Test;
import util.ToolIO;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ErrorPrinterTest
{

    /* (non-Javadoc)
     * @see junit.framework.TestCase#setUp()
     */
    @Before
	public void setUp() throws Exception
    {
        ToolIO.setMode(ToolIO.TOOL);
        ToolIO.reset();
    }

    /**
     * Test method for {@link tlc2.output.MP#printError(int)}.
     */
    @Test
	public void testPrintErrorInt()
    {
        MP.printError(EC.UNIT_TEST);
        String[] allMessages = ToolIO.getAllMessages();
        assertEquals(1, allMessages.length);
        assertEquals("Error: [%1%][%2%]", allMessages[0]);
    }

    /**
     * Test method for {@link tlc2.output.MP#printError(int, java.lang.String)}.
     */
    @Test
	public void testPrintErrorIntString()
    {
        String parameter = "EXPECTED";
        MP.printError(EC.UNIT_TEST, parameter);
        String[] allMessages = ToolIO.getAllMessages();
        assertEquals(1, allMessages.length);
        assertEquals("Error: [" + parameter + "][%2%]", allMessages[0]);
    }

    /**
     * Test method for {@link tlc2.output.MP#printError(int, java.lang.String[])}.
     */
    @Test
	public void testPrintErrorIntStringArray()
    {
        String[] parameters = new String[] { "EXPECTED", "EXPECTED2", "TOO MANY" };
        MP.printError(EC.UNIT_TEST, parameters);
        String[] allMessages = ToolIO.getAllMessages();
        assertEquals(1, allMessages.length);
        assertEquals("Error: [" + parameters[0] + "][" + parameters[1] + "]", allMessages[0]);
    }


}
