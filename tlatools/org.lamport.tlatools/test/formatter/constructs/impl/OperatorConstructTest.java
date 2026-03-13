package formatter.constructs.impl;

import formatter.Utils;
import org.junit.Test;

/**
 * Tests for OperatorConstruct formatting.
 * Verifies LOCAL qualifier preservation and operator definition formatting.
 */
public class OperatorConstructTest {

    @Test
    public void testLocalSimpleOperator() {
        String spec = "---- MODULE Spec ----\n" +
                "LOCAL foo == 42\n" +
                "====\n";
        Utils.assertSpecUnchanged(spec);
    }

    @Test
    public void testLocalOperatorWithParams() {
        String spec = "---- MODULE Spec ----\n" +
                "LOCAL Bar(x, y) == x\n" +
                "====\n";
        Utils.assertSpecUnchanged(spec);
    }

    @Test
    public void testLocalOperatorWithRecursive() {
        String input = "---- MODULE Spec ----\n" +
                "RECURSIVE F(_, _)\n" +
                "LOCAL F(x, y) == x\n" +
                "====\n";
        // RECURSIVE formatting strips spaces after commas (pre-existing behavior)
        String expected = "---- MODULE Spec ----\n" +
                "RECURSIVE F(_,_)\n" +
                "LOCAL F(x, y) == x\n" +
                "====\n";
        Utils.assertSpecEquals(expected, input);
    }

    @Test
    public void testNonLocalOperatorUnchanged() {
        String spec = "---- MODULE Spec ----\n" +
                "foo == 42\n" +
                "====\n";
        Utils.assertSpecUnchanged(spec);
    }

    @Test
    public void testNonLocalOperatorWithParamsUnchanged() {
        String spec = "---- MODULE Spec ----\n" +
                "Bar(x, y) == x\n" +
                "====\n";
        Utils.assertSpecUnchanged(spec);
    }

    @Test
    public void testMultipleLocalOperators() {
        String spec = "---- MODULE Spec ----\n" +
                "LOCAL foo == 42\n" +
                "LOCAL bar == 99\n" +
                "====\n";
        Utils.assertSpecUnchanged(spec);
    }

    @Test
    public void testMixedLocalAndNonLocal() {
        String spec = "---- MODULE Spec ----\n" +
                "LOCAL foo == 42\n" +
                "bar == 99\n" +
                "LOCAL baz == 0\n" +
                "====\n";
        Utils.assertSpecUnchanged(spec);
    }

    @Test
    public void testConjListBodyBreaksAfterEquals() {
        String input = "---- MODULE Spec ----\n" +
                "CONSTANTS a, b\n" +
                "TypeInv == /\\ a = 1\n" +
                "           /\\ b = 2\n" +
                "====\n";
        String expected = "---- MODULE Spec ----\n" +
                "CONSTANTS a, b\n" +
                "TypeInv ==\n" +
                "  /\\ a = 1\n" +
                "  /\\ b = 2\n" +
                "====\n";
        Utils.assertSpecEquals(expected, input);
    }

    @Test
    public void testDisjListBodyBreaksAfterEquals() {
        String input = "---- MODULE Spec ----\n" +
                "CONSTANTS a, b\n" +
                "Next == \\/ a = 1\n" +
                "        \\/ b = 2\n" +
                "====\n";
        String expected = "---- MODULE Spec ----\n" +
                "CONSTANTS a, b\n" +
                "Next ==\n" +
                "  \\/ a = 1\n" +
                "  \\/ b = 2\n" +
                "====\n";
        Utils.assertSpecEquals(expected, input);
    }

    @Test
    public void testSimpleExpressionStaysOnSameLine() {
        String spec = "---- MODULE Spec ----\n" +
                "Zero == 0\n" +
                "====\n";
        Utils.assertSpecUnchanged(spec);
    }
}
