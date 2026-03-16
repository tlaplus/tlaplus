package formatter.constructs.impl;

import org.junit.Test;

import static formatter.Utils.assertUnchanged;

public class ExceptSpecConstructTest {

    @Test
    public void testSimpleExcept() {
        var s = "----- MODULE ExceptTest -----\n" +
                "VARIABLE x\n" +
                "Test == x' = [x EXCEPT ![1] = 2]\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    public void testChainedExceptComponents() {
        // Regression test for bug where chained EXCEPT components (e.g., ![r].smoking)
        // would lose the value (FALSE) because ExceptSpecConstruct assumed exactly 4 children.
        var s = "----- MODULE ExceptChained -----\n" +
                "VARIABLE smokers, r\n" +
                "Test == smokers' = [smokers EXCEPT ![r].smoking = FALSE]\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    public void testTripleChainedExceptComponents() {
        // Test three chained components: ![a][b].c
        var s = "----- MODULE ExceptTriple -----\n" +
                "VARIABLE f, a, b\n" +
                "Test == f' = [f EXCEPT ![a][b].c = TRUE]\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    public void testExceptWithAt() {
        // Test EXCEPT with @ (reference to current value)
        var s = "----- MODULE ExceptAt -----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLE x\n" +
                "Test == x' = [x EXCEPT ![1] = @ + 1]\n" +
                "====";
        assertUnchanged(s);
    }
}
