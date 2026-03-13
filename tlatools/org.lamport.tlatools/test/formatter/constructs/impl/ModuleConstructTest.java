package formatter.constructs.impl;

import formatter.TLAPlusFormatter;
import formatter.exceptions.SanyFrontendException;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class ModuleConstructTest {
    @Test
    void testDashesArePreserved() throws SanyFrontendException, IOException {
        var s = "----- MODULE m -----------\n" + "=============================";

        var f = (new TLAPlusFormatter(s)).getOutput();
        assertEquals(s, f);
    }

    @Test
    void testModuleNamePreservedWhenSanyKeyword() throws SanyFrontendException, IOException {
        // "Token" is a SANY keyword where getHumanReadableImage() returns empty string
        // The formatter should still preserve the module name using getImage() as fallback
        var s = "---- MODULE Token ----\n" +
                "VARIABLE x\n" +
                "====";

        var f = (new TLAPlusFormatter(s)).getOutput();
        assertTrue(f.contains("MODULE Token"), "Module name 'Token' should be preserved in output, got: " + f);
    }
}
