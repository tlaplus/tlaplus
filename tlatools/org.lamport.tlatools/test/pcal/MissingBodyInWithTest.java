package pcal;

import org.junit.Test;
import tlc2.tool.CommonTestCase;
import util.ToolIO;

import static org.junit.Assert.assertEquals;

public class MissingBodyInWithTest extends PCalTest {

    @Test
    public void test() {
        assertEquals(trans.STATUS_EXIT_WITH_ERRORS,
                new trans().runMe(new String[]{"-nocfg", CommonTestCase.TEST_MODEL_PATH + "MissingBodyInWith.tla"}));

        final String[] messages = ToolIO.getAllMessages();
        assertEquals(1, messages.length);

        final String msg = messages[0];
        assertEquals("""
                Unrecoverable error:
                 -- Missing body of with statement
                    at line 5, column 5.""", msg.trim());
    }
}
