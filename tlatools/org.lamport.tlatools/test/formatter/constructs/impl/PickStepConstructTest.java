package formatter.constructs.impl;

import org.junit.jupiter.api.Test;

import static formatter.Utils.*;

public class PickStepConstructTest {

    @Test
    void testPickWithConjunctionList() {
        // PICK with conjunction list body must remain parseable
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS, Naturals\n" +
                "THEOREM Test == TRUE\n" +
                "<1>1. PICK v \\in {1, 2} :\n" +
                "         /\\ v > 0\n" +
                "         /\\ v < 3\n" +
                "  OBVIOUS\n" +
                "<1>2. QED OBVIOUS\n" +
                "====";
        var expected = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS, Naturals\n" +
                "THEOREM Test == TRUE\n" +
                "<1>1. PICK v \\in { 1, 2 } :\n" +
                "  /\\ v > 0\n" +
                "  /\\ v < 3\n" +
                "  OBVIOUS\n" +
                "<1>2. QED OBVIOUS\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    void testPickSimpleBody() {
        // PICK with a simple (non-conjunction) body can stay on same line
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS, Naturals\n" +
                "THEOREM Test == TRUE\n" +
                "<1>1. PICK v \\in {1, 2} : v > 0\n" +
                "  OBVIOUS\n" +
                "<1>2. QED OBVIOUS\n" +
                "====";
        var expected = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS, Naturals\n" +
                "THEOREM Test == TRUE\n" +
                "<1>1. PICK v \\in { 1, 2 } : v > 0 OBVIOUS\n" +
                "<1>2. QED OBVIOUS\n" +
                "====";
        assertSpecEquals(expected, input);
    }
}
