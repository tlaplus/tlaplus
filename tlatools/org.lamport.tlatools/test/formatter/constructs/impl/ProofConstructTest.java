package formatter.constructs.impl;

import org.junit.BeforeClass;
import org.junit.Test;

import static formatter.Utils.assertSpecEquals;
import static formatter.Utils.assertUnchanged;
import static org.junit.Assume.assumeTrue;

public class ProofConstructTest {

    @BeforeClass
    public static void checkTlapsAvailable() {
        String tlaLib = System.getProperty("TLA-Library", System.getenv().getOrDefault("TLA_LIBRARY", ""));
        assumeTrue("Skipping: TLAPS not available (set -DTLA-Library=... to include tlapm/library)", !tlaLib.isEmpty());
    }

    @Test
    public void testSimpleProof() {
        var s = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x\n" +
                "<1>1. x = x OBVIOUS\n" +
                "<1>. QED BY <1>1\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    public void testNestedProofSteps() {
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x\n" +
                "<1>1. x = x\n" +
                "  <2>1. x = x\n" +
                "    OBVIOUS\n" +
                "  <2>. QED BY <2>1\n" +
                "<1>. QED BY <1>1\n" +
                "====";
        var expected = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x\n" +
                "<1>1. x = x\n" +
                "  <2>1. x = x OBVIOUS\n" +
                "  <2>. QED BY <2>1\n" +
                "<1>. QED BY <1>1\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void testProofWithBY() {
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x OBVIOUS\n" +
                "====";
        var expected = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x\n" +
                "OBVIOUS\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void testBlockCommentBeforeBY() {
        // Pattern from ReachabilityProofs.tla: block comment before BY keyword
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x\n" +
                "<1>1. x = x\n" +
                "  (**************)\n" +
                "  (* A comment. *)\n" +
                "  (**************)\n" +
                "  OBVIOUS\n" +
                "<1>. QED BY <1>1\n" +
                "====";
        assertUnchanged(input);
    }

    @Test
    public void testLineCommentBeforeBY() {
        // Line comment before BY keyword in proof step
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x\n" +
                "<1>1. x = x\n" +
                "  \\* This step is obvious.\n" +
                "  OBVIOUS\n" +
                "<1>. QED BY <1>1\n" +
                "====";
        assertUnchanged(input);
    }

    @Test
    public void testBlockCommentBeforeOBVIOUS() {
        // Block comment before OBVIOUS keyword in proof step
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x\n" +
                "<1>1. x = x\n" +
                "  (* This is trivial. *)\n" +
                "  OBVIOUS\n" +
                "<1>. QED BY <1>1\n" +
                "====";
        assertUnchanged(input);
    }

    @Test
    public void testLineCommentBeforeBYWithRef() {
        // Line comment before BY <ref> in terminal proof
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x\n" +
                "<1>1. x = x OBVIOUS\n" +
                "<1>. QED\n" +
                "  \\* Use the step above.\n" +
                "  BY <1>1\n" +
                "====";
        assertUnchanged(input);
    }

    @Test
    public void testCommentInNestedProofBeforeBY() {
        // Comment before BY/OBVIOUS in nested proof steps (multiple levels)
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x\n" +
                "<1>1. x = x\n" +
                "  <2>1. x = x\n" +
                "    \\* Nested proof comment.\n" +
                "    OBVIOUS\n" +
                "  <2>. QED\n" +
                "    \\* QED is simple.\n" +
                "    BY <2>1\n" +
                "<1>. QED BY <1>1\n" +
                "====";
        assertUnchanged(input);
    }

    @Test
    public void testProofWithSuffices() {
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "CONSTANT S\n" +
                "THEOREM S = S\n" +
                "<1>. SUFFICES ASSUME S = S\n" +
                "             PROVE S = S\n" +
                "  OBVIOUS\n" +
                "<1>. QED\n" +
                "====";
        var expected = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "CONSTANT S\n" +
                "THEOREM S = S\n" +
                "<1>. SUFFICES ASSUME S = S PROVE S = S OBVIOUS\n" +
                "<1>. QED\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void testDefineWithMultipleDefinitions() {
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x\n" +
                "<1>. DEFINE P == x = x\n" +
                "            Q == x # x\n" +
                "<1>1. P OBVIOUS\n" +
                "<1>. QED BY <1>1\n" +
                "====";
        var expected = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x\n" +
                "<1>. DEFINE P == x = x\n" +
                "         Q == x # x\n" +
                "<1>1. P OBVIOUS\n" +
                "<1>. QED BY <1>1\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void testDefineWithSingleDefinition() {
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x\n" +
                "<1>. DEFINE P == x = x\n" +
                "<1>1. P OBVIOUS\n" +
                "<1>. QED BY <1>1\n" +
                "====";
        assertUnchanged(input);
    }

    @Test
    public void testAssumeProveInLemma() {
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "CONSTANT S\n" +
                "LEMMA Test ==\n" +
                "  ASSUME NEW f \\in S\n" +
                "  PROVE f = f\n" +
                "PROOF OMITTED\n" +
                "====";
        var expected = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "CONSTANT S\n" +
                "LEMMA Test == ASSUME NEW f \\in S PROVE f = f\n" +
                "PROOF OMITTED\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void testAssumeProveWithMultipleAssumptions() {
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "CONSTANT S\n" +
                "LEMMA Test ==\n" +
                "  ASSUME NEW f \\in S,\n" +
                "         NEW g \\in S\n" +
                "  PROVE f = g\n" +
                "PROOF OMITTED\n" +
                "====";
        var expected = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "CONSTANT S\n" +
                "LEMMA Test == ASSUME NEW f \\in S , NEW g \\in S PROVE f = g\n" +
                "PROOF OMITTED\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void testAssumeProveWrapsWhenLong() {
        // When the ASSUME/PROVE is too long, it should wrap
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "CONSTANT SomeLongVariableName\n" +
                "LEMMA Test ==\n" +
                "  ASSUME NEW f \\in SomeLongVariableName,\n" +
                "         NEW g \\in SomeLongVariableName,\n" +
                "         NEW h \\in SomeLongVariableName\n" +
                "  PROVE f = g\n" +
                "PROOF OMITTED\n" +
                "====";
        var expected = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "CONSTANT SomeLongVariableName\n" +
                "LEMMA Test ==\n" +
                "  ASSUME NEW f \\in SomeLongVariableName , NEW g \\in SomeLongVariableName , NEW h \\in SomeLongVariableName\n" +
                "  PROVE f = g\n" +
                "PROOF OMITTED\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void testImplicitDefineNoKeyword() {
        // Implicit DEFINE step (no DEFINE keyword): <1> P(b) == expr
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x\n" +
                "<1> P == x = x\n" +
                "<1>1. P OBVIOUS\n" +
                "<1>. QED BY <1>1\n" +
                "====";
        assertUnchanged(input);
    }
}
