package pcal;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import util.ToolIO;

import java.util.Arrays;

public class Github776Test extends PCalModelCheckerTestCase {

    public Github776Test() {
        super("Github776", "pcal");
    }

    @Test
    public void testSpec() {
        assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
        assertTrue(recorder.recorded(EC.TLC_FINISHED));
        assertFalse(recorder.recorded(EC.GENERAL));

        assertZeroUncovered();
    }
}
