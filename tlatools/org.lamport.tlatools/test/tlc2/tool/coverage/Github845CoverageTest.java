package tlc2.tool.coverage;

import org.junit.Test;
import tlc2.output.EC;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class Github845CoverageTest extends AbstractCoverageTest {
    public Github845CoverageTest() {
        super("Github845");
    }

    @Test
    public void testSpec() {
        // ModelChecker has finished and generated the expected amount of states
        assertTrue(recorder.recorded(EC.TLC_FINISHED));
        assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "2"));
        assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "5", "2", "0"));

        // No 'general' errors recorded
        assertFalse(recorder.recorded(EC.GENERAL));

        assertCoverage("<Init line 5, col 1 to line 5, col 4 of module Github845>: 1:1\n" +
                "  line 5, col 9 to line 5, col 13 of module Github845: 1\n" +
                "<A1 line 7, col 1 to line 7, col 2 of module Github845>: 1:2\n" +
                "  line 8, col 11 to line 8, col 15 of module Github845: 2\n" +
                "  line 9, col 13 to line 9, col 18 of module Github845: 0\n" +
                "  line 10, col 13 to line 10, col 16 of module Github845: 2\n" +
                "  line 11, col 8 to line 11, col 13 of module Github845: 2\n" +
                "<Next line 13, col 1 to line 13, col 4 of module Github845 (15 8 17 24)>: 0:2\n" +
                "  line 15, col 11 to line 15, col 15 of module Github845: 2\n" +
                "  line 16, col 14 to line 16, col 15 of module Github845: 0\n" +
                "  |line 8, col 11 to line 8, col 15 of module Github845: 0\n" +
                "  |line 9, col 13 to line 9, col 18 of module Github845: 0\n" +
                "  |line 10, col 13 to line 10, col 16 of module Github845: 0\n" +
                "  |line 11, col 8 to line 11, col 13 of module Github845: 0\n" +
                "  line 17, col 14 to line 17, col 24 of module Github845: 2");
        assertFalse(recorder.recorded(EC.TLC_COVERAGE_MISMATCH));
    }
}
