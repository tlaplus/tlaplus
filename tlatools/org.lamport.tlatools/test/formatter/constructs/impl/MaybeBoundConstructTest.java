package formatter.constructs.impl;

import org.junit.Test;

import static formatter.Utils.assertSpecEquals;
import static formatter.Utils.assertUnchanged;

public class MaybeBoundConstructTest {
    @Test
    public void testCompact() {
        var s = "----- MODULE MaybeBound -----\n" +
                "CONSTANT S\n" +
                "Test == CHOOSE e \\in S: TRUE\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    public void testWrapped() {
        var t = "AVeryLongTestName == CHOOSE AVeryLongConstantName \\in AVeryLongConstantNameThatForcesWrapping : TRUE";
        var s = "----- MODULE MaybeBound -----\n" +
                "CONSTANT AVeryLongConstantNameThatForcesWrapping\n" +
                t + "\n" +
                "====";
        var expected = "----- MODULE MaybeBound -----\n" +
                "CONSTANT AVeryLongConstantNameThatForcesWrapping\n" +
                "AVeryLongTestName ==\n" +
                "  CHOOSE AVeryLongConstantName \\in AVeryLongConstantNameThatForcesWrapping:\n" +
                "    TRUE\n" +
                "====";

        assertSpecEquals(expected, s, t.length() / 2);
    }
}