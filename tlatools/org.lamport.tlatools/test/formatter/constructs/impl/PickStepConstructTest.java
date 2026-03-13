package formatter.constructs.impl;

import org.junit.BeforeClass;
import org.junit.Test;

import static formatter.Utils.*;
import static org.junit.Assume.assumeTrue;

public class PickStepConstructTest {

    @BeforeClass
    public static void checkTlapsAvailable() {
        String tlaLib = System.getProperty("TLA-Library", System.getenv().getOrDefault("TLA_LIBRARY", ""));
        assumeTrue("Skipping: TLAPS not available (set -DTLA-Library=... to include tlapm/library)", !tlaLib.isEmpty());
    }

    @Test
    public void testPickWithConjunctionList() {
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
    public void testPickSimpleBody() {
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
