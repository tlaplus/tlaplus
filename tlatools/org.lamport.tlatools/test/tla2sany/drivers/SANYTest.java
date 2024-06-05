package tla2sany.drivers;

import org.junit.Test;
import tla2sany.AbstractSANYTest;
import util.TestPrintStream;
import util.ToolIO;

public class SANYTest extends AbstractSANYTest {
    @Test
    public void testHelp() {
        final TestPrintStream testPrintStream = new TestPrintStream();
        ToolIO.out = testPrintStream;

        SANY.SANYmain(new String[] { "-help" });

        testPrintStream.assertSubstring(SANY.SANY_BUILD_VERSION);
    }

}
