package pcal;

import org.junit.Test;
import tlc2.tool.CommonTestCase;
import util.ToolIO;

import java.util.Arrays;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

public class CallGotoUnlabeledTest extends PCalTest {

    // https://groups.google.com/forum/#!topic/tlaplus/6M1oFOtN-5k/discussion

    @Test
    public void test() {
        ToolIO.setMode(ToolIO.TOOL);

        final String fileName = "CallGotoUnlabeledTest.tla";
        var t = new trans();

        assertEquals(0, t.runMe(new String[]{"-nocfg", "-unixEOL", "-reportLabels", CommonTestCase.TEST_MODEL_PATH + fileName}));
        final TLAtoPCalMapping mapping = t.pcalParams.tlaPcalMapping;
        assertNotNull(mapping);

        final String[] messages = ToolIO.getAllMessages();
        assertEquals(Arrays.toString(messages), 6, messages.length);

        assertEquals("The following labels were added:", messages[0]);
        assertEquals("  Lbl_1 at line 10, column 3", messages[1]);
        assertEquals("  Lbl_2 at line 19, column 3", messages[2]);
        assertEquals("Parsing completed.", messages[3]);
        assertEquals("Translation completed.", messages[4]);
        // Ignore last line "New file ...." because it depends on from where the test is executed.
//		assertEquals("New file test-model/" + fileName + " written.", messages[5]);
    }
}
