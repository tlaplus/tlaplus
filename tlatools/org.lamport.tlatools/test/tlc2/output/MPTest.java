package tlc2.output;

import org.junit.Before;
import org.junit.Test;
import util.ToolIO;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class MPTest {

    /* (non-Javadoc)
     * @see junit.framework.TestCase#setUp()
     */
    @Before
    public void setUp() {
        ToolIO.setMode(ToolIO.TOOL);
        ToolIO.reset();
    }

    /**
     * Test method for {@link tlc2.output.MP#printError(int)}.
     */
    @Test
    public void testPrintErrorInt() {
        MP.printError(EC.UNIT_TEST);
        final String[] allMessages = ToolIO.getAllMessages();
        assertEquals(1, allMessages.length);
        assertEquals("Error: [%1%][%2%]", allMessages[0]);
    }

    /**
     * Test method for {@link tlc2.output.MP#printError(int, java.lang.String)}.
     */
    @Test
    public void testPrintErrorIntString() {
        final String parameter = "EXPECTED";
        MP.printError(EC.UNIT_TEST, parameter);
        final String[] allMessages = ToolIO.getAllMessages();
        assertEquals(1, allMessages.length);
        assertEquals("Error: [" + parameter + "][%2%]", allMessages[0]);
    }

    /**
     * Test method for {@link tlc2.output.MP#printError(int, java.lang.String[])}.
     */
    @Test
    public void testPrintErrorIntStringArray() {
        final String[] parameters = new String[]{"EXPECTED", "EXPECTED2", "TOO MANY"};
        MP.printError(EC.UNIT_TEST, parameters);
        final String[] allMessages = ToolIO.getAllMessages();
        assertEquals(1, allMessages.length);
        assertEquals("Error: [" + parameters[0] + "][" + parameters[1] + "]", allMessages[0]);
    }

    @Test
    public void testPrintProgressStats() {
        final String[] parameters = new String[]{
                "this.trace.getLevelForReporting()",
                MP.format(3000000),
                MP.format(5000),
                MP.format(1222333444),
                MP.format(10000),
                MP.format(1234)
        };
        MP.printMessage(EC.TLC_PROGRESS_STATS, parameters);
        final String[] allMessages = ToolIO.getAllMessages();
        assertEquals(1, allMessages.length);
        assertTrue(allMessages[0], allMessages[0].contains(
                "3,000,000 states generated (10,000 s/min), 5,000 distinct states found (1,234 ds/min), 1,222,333,444 states left on queue.")
                || allMessages[0].contains(
                "3.000.000 states generated (10.000 s/min), 5.000 distinct states found (1.234 ds/min), 1.222.333.444 states left on queue."));
    }
}
