package formatter;

import org.junit.jupiter.api.Test;

/**
 * Tests that infix conjunction/disjunction expressions preserve their AST structure
 * after formatting. When /\ or \/ is used as an infix operator (not in a bulleted list),
 * the formatter must not break lines in a way that causes SANY to re-parse them as
 * N_ConjList/N_DisjList instead of N_InfixExpr.
 */
class InfixConjAlignmentTest {

    private void assertAstPreserved(String spec, int lineWidth) throws Exception {
        var config = new FormatConfig(lineWidth, FormatConfig.DEFAULT_INDENT_SIZE);
        var f = new TLAPlusFormatter(spec, config);
        String output = f.getOutput();
        var f2 = new TLAPlusFormatter(output, config);
        Utils.assertAstEquals(f.root, f2.root);
    }

    private void assertAstPreserved(String spec) throws Exception {
        assertAstPreserved(spec, FormatConfig.DEFAULT_LINE_WIDTH);
    }

    /**
     * Conjunction list followed by => on same alignment column.
     * SANY parses as N_InfixExpr(ConjList, =>, right) with 3 children.
     * Formatter must not collapse => onto the last conj item line.
     */
    @Test
    void testConjListFollowedByImplication() throws Exception {
        var spec = "----- MODULE test -----\n" +
                "CONSTANTS A, B, C, D, E, msgs\n" +
                "Test == \\A m \\in msgs : /\\ A = B\n" +
                "                        /\\ C = D\n" +
                "                        => E\n" +
                "====";
        assertAstPreserved(spec);
    }

    @Test
    void testInfixConjDoesNotBecomeConjList() throws Exception {
        var spec = "----- MODULE test -----\n" +
                "CONSTANTS VeryLongA, VeryLongB, VeryLongC\n" +
                "Test == VeryLongA /\\ VeryLongB /\\ VeryLongC\n" +
                "====";
        assertAstPreserved(spec, 40);
    }

    @Test
    void testInfixDisjDoesNotBecomeDisjList() throws Exception {
        var spec = "----- MODULE test -----\n" +
                "CONSTANTS VeryLongA, VeryLongB, VeryLongC\n" +
                "Test == VeryLongA \\/ VeryLongB \\/ VeryLongC\n" +
                "====";
        assertAstPreserved(spec, 40);
    }

    /**
     * Test infix /\ inside an implication -- pattern from Paxos.tla.
     */
    @Test
    void testInfixConjInsideImplication() throws Exception {
        var spec = "----- MODULE test -----\n" +
                "CONSTANTS LongNameA, LongNameB, LongNameC, LongNameD\n" +
                "Test == LongNameA /\\ LongNameB /\\ LongNameC => LongNameD\n" +
                "====";
        assertAstPreserved(spec, 50);
    }

    @Test
    void testChainedInfixConjDefaultWidth() throws Exception {
        var spec = "----- MODULE test -----\n" +
                "CONSTANTS ReallyLongVariableNameAlpha, ReallyLongVariableNameBeta, ReallyLongVariableNameGamma\n" +
                "Test == ReallyLongVariableNameAlpha /\\ ReallyLongVariableNameBeta /\\ ReallyLongVariableNameGamma\n" +
                "====";
        assertAstPreserved(spec);
    }

    @Test
    void testInfixDisjInQuantifierBody() throws Exception {
        var spec = "----- MODULE test -----\n" +
                "CONSTANTS S\n" +
                "VARIABLES x, y\n" +
                "Test == \\A s \\in S: x[s] \\/ y[s] \\/ s # 0\n" +
                "====";
        assertAstPreserved(spec, 35);
    }

    /**
     * Test nested infix /\ with quantifier -- pattern from MCWriteThroughCache.
     * The infix /\ between quantifier body and next operand must not place the
     * right operand at the same column as the quantifier's inner conj list items.
     */
    @Test
    void testNestedInfixConjWithQuantifier() throws Exception {
        var spec = "----- MODULE test -----\n" +
                "CONSTANTS S, A, B, C, D, E\n" +
                "Test == A\n" +
                "         /\\ \\E s \\in S:\n" +
                "              /\\ B\n" +
                "              /\\ C\n" +
                "              /\\ D\n" +
                "         /\\ E\n" +
                "====";
        assertAstPreserved(spec);
    }

    @Test
    void testNestedInfixDisjWithQuantifier() throws Exception {
        var spec = "----- MODULE test -----\n" +
                "CONSTANTS S, A, B, C, D, E\n" +
                "Test == A\n" +
                "         \\/ \\E s \\in S:\n" +
                "              \\/ B\n" +
                "              \\/ C\n" +
                "         \\/ E\n" +
                "====";
        assertAstPreserved(spec);
    }
}
