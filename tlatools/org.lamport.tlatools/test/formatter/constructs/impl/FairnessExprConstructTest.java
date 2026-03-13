package formatter.constructs.impl;

import org.junit.jupiter.api.Test;

import static formatter.Utils.assertSpecEquals;
import static formatter.Utils.assertUnchanged;

public class FairnessExprConstructTest {

    @Test
    void testSimpleWF() {
        var s = "----- MODULE Test -----\n" +
                "VARIABLE x\n" +
                "op == WF_x(x' = x)\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    void testWFWithConjunctionBreaksToNewLine() {
        // When the action inside WF_() is a conjunction list that doesn't fit
        // on one line, the /\ items should be properly aligned.
        // This was causing SANY parse errors in InnerSerial.tla.
        var s = "----- MODULE Test -----\n" +
                "VARIABLE x, y\n" +
                "op ==\n" +
                "  WF_x(\n" +
                "    /\\ x' = x\n" +
                "    /\\ y' = y\n" +
                "    /\\ x' = y \\/ y' = x)\n" +
                "====";
        var expected = "----- MODULE Test -----\n" +
                "VARIABLE x, y\n" +
                "op == WF_x(/\\ x' = x\n" +
                "           /\\ y' = y\n" +
                "           /\\ x' = y \\/ y' = x)\n" +
                "====";
        assertSpecEquals(expected, s);
    }

    @Test
    void testSFWithConjunctionBreaksToNewLine() {
        var s = "----- MODULE Test -----\n" +
                "VARIABLE x, y\n" +
                "op ==\n" +
                "  SF_x(\n" +
                "    /\\ x' = x\n" +
                "    /\\ y' = y)\n" +
                "====";
        var expected = "----- MODULE Test -----\n" +
                "VARIABLE x, y\n" +
                "op == SF_x(/\\ x' = x\n" +
                "           /\\ y' = y)\n" +
                "====";
        assertSpecEquals(expected, s);
    }
}
