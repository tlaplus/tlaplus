package formatter.constructs.impl;

import org.junit.jupiter.api.Test;

import static formatter.Utils.assertUnchanged;

/**
 * Tests for identifiers starting with N_ which could be confused with
 * SANY internal node kind names (like N_OperatorDefinition).
 * Covers ASSUME, CONSTANT, VARIABLE, and operator definitions.
 */
public class AssumptionConstructTest {

    @Test
    void testNamedAssumeWithNPrefix() {
        // Identifiers starting with N_ must not be dropped by buildGeneric
        var s = "----- MODULE Test -----\n" +
                "EXTENDS Naturals\n" +
                "CONSTANT N\n" +
                "ASSUME N_Assumption == N \\in Nat\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    void testNamedAssume() {
        var s = "----- MODULE Test -----\n" +
                "EXTENDS Naturals\n" +
                "CONSTANT N\n" +
                "ASSUME Foo == N \\in Nat\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    void testSimpleAssume() {
        var s = "----- MODULE Test -----\n" +
                "EXTENDS Naturals\n" +
                "CONSTANT N\n" +
                "ASSUME N \\in Nat\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    void testNamedAssumeWithNPrefixVariant() {
        var s = "----- MODULE Test -----\n" +
                "EXTENDS Naturals\n" +
                "CONSTANT X\n" +
                "ASSUME N_Positive == X > 0\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    void testConstantWithNPrefix() {
        var s = "----- MODULE Test -----\n" +
                "EXTENDS Naturals\n" +
                "CONSTANT N_Value\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    void testMultipleConstantsWithNPrefix() {
        var s = "----- MODULE Test -----\n" +
                "EXTENDS Naturals\n" +
                "CONSTANTS N_First, N_Second, Normal\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    void testVariableWithNPrefix() {
        var s = "----- MODULE Test -----\n" +
                "VARIABLE N_State\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    void testOperatorWithNPrefix() {
        var s = "----- MODULE Test -----\n" +
                "EXTENDS Naturals\n" +
                "N_Op(x) == x + 1\n" +
                "====";
        assertUnchanged(s);
    }
}
