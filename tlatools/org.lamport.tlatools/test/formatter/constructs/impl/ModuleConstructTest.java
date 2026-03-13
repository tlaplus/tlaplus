package formatter.constructs.impl;

import static org.junit.Assert.*;
import formatter.TLAPlusFormatter;
import formatter.exceptions.SanyFrontendException;
import org.junit.Test;

import java.io.IOException;


public class ModuleConstructTest {
    @Test
    public void testDashesArePreserved() throws SanyFrontendException, IOException {
        var s = "----- MODULE m -----------\n" + "=============================";

        var f = (new TLAPlusFormatter(s)).getOutput();
        assertEquals(s, f);
    }

    @Test
    public void testModuleNamePreservedWhenSanyKeyword() throws SanyFrontendException, IOException {
        // "Token" is a SANY keyword where getHumanReadableImage() returns empty string
        // The formatter should still preserve the module name using getImage() as fallback
        var s = "---- MODULE Token ----\n" +
                "VARIABLE x\n" +
                "====";

        var f = (new TLAPlusFormatter(s)).getOutput();
        assertTrue("Module name 'Token' should be preserved in output, got: " + f, f.contains("MODULE Token"));
    }
}
