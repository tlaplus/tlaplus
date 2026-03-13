package formatter.constructs.impl;

import org.junit.jupiter.api.Test;

import static formatter.Utils.assertSpecEquals;
import static formatter.Utils.assertUnchanged;

class InfixExprConstructTest {
    @Test
    void testCompact() {
        var s = "----- MODULE InfixExpr -----\n" +
                "CONSTANTS S, Z\n" +
                "Test == S \\in Z\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    void testWrapped() {
        var t = "AVeryLongTestName == AVeryLongConstantName \\in AVeryLongConstantNameThatForcesWrapping";
        var s = "----- MODULE InfixExpr -----\n" +
                "CONSTANT AVeryLongConstantName, AVeryLongConstantNameThatForcesWrapping\n" +
                t + "\n" +
                "====";
        var expected = "----- MODULE InfixExpr -----\n" +
                "CONSTANT AVeryLongConstantName, AVeryLongConstantNameThatForcesWrapping\n" +
                "AVeryLongTestName ==\n" +
                "  AVeryLongConstantName \\in\n" +
                "    AVeryLongConstantNameThatForcesWrapping\n" +
                "====";

        assertSpecEquals(expected, s, t.length() / 2);
    }
}