package formatter.constructs.impl;

import org.junit.jupiter.api.Test;

import static formatter.Utils.assertSpecEquals;
import static formatter.Utils.assertUnchanged;

class MaybeBoundConstructTest {
    @Test
    void testCompact() {
        var s = "----- MODULE MaybeBound -----\n" +
                "CONSTANT S\n" +
                "Test == CHOOSE e \\in S: TRUE\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    void testWrapped() {
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