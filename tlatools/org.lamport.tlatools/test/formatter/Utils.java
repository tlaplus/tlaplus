package formatter;

import formatter.exceptions.SanyFrontendException;
import tla2sany.st.TreeNode;

import java.io.IOException;

import static org.junit.Assert.*;

public class Utils {

    public static void assertUnchanged(String spec) {
        try {
            var f = (new TLAPlusFormatter(spec)).getOutput();
            assertEquals(spec.replace("\r\n", "\n"), f.replace("\r\n", "\n"));
            idempotency(spec);
        } catch (Exception e) {
            fail(e.getMessage());
        }
    }

    static void assertAstEquals(TreeNode root1, TreeNode root2) {
        AstComparator.Result result = AstComparator.compare(root1, root2);
        assertTrue(result.formatDiagnostic(), result.isMatch());
    }

    /**
     * Helper method to test formatting with idempotency check
     */
    public static void idempotency(String spec) throws IOException, SanyFrontendException {
        // First pass
        TLAPlusFormatter formatter1 = new TLAPlusFormatter(spec);
        String output1 = formatter1.getOutput();
        // Second pass - must be identical
        TLAPlusFormatter formatter2 = new TLAPlusFormatter(output1);
        String output2 = formatter2.getOutput();
        // Verify idempotency
        assertEquals("Formatter should be idempotent",
                output1.replace("\r\n", "\n"), output2.replace("\r\n", "\n"));
        assertAstEquals(formatter1.root, formatter2.root);
    }

    public static void assertSpecEquals(String expected, String input, FormatConfig config) {
        try {
            var f = new TLAPlusFormatter(input, config);
            var received = f.getOutput();
            assertEquals("Formatted output does not match expected output",
                    expected.replace("\r\n", "\n"), received.replace("\r\n", "\n"));

        } catch (Exception e) {
            fail(e.getMessage());
        }
        try {
            idempotency(input);
        } catch (Exception e) {
            fail(e.getMessage());
        }
    }

    /**
     * Verify that formatting the input spec does not change it.
     * Idempotency is also checked.
     *
     */
    public static void assertSpecUnchanged(String input) {
        assertSpecEquals(input, input, new FormatConfig());
    }

    public static void assertSpecEquals(String expected, String input) {
        assertSpecEquals(expected, input, new FormatConfig());
    }

    public static void assertSpecEquals(String expected, String input, int lineWidth) {
        assertSpecEquals(expected, input, new FormatConfig(lineWidth, FormatConfig.DEFAULT_INDENT_SIZE));
    }
}
