package tlc2.tool;

import org.junit.Test;
import tlc2.TLC;
import tlc2.TestMPRecorder;
import tlc2.output.EC;
import tlc2.output.MP;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assume.assumeFalse;

public class AbsoluteSpecPathTest extends CommonTestCase {

    public AbsoluteSpecPathTest() {
        super(new TestMPRecorder());
    }

    @Test
    public void test() {
        // Check that BASE_DIR is actually set to make sure we have an absolute path to
        // work with. If this test gets executed from within the Eclipse IDE, manually
        // set -Dbasedir=/path/to/tlatools/
        assumeFalse(BASE_DIR.equals(""));

        MP.setRecorder(recorder);

        // Do not call TLC#main because we won't get control back (system.exit) to check
        // assertions below.
        final TLC tlc = new TLC();
        tlc.handleParameters(new String[]{TEST_MODEL_PATH + "Test2"});
        tlc.process();

        MP.unsubscribeRecorder(recorder);

        assertTrue(recorder.recorded(EC.TLC_FINISHED));
        assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "5"));
        assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "6", "5", "0"));

        // No 'general' errors recorded
        assertFalse(recorder.recorded(EC.GENERAL));
    }
}
