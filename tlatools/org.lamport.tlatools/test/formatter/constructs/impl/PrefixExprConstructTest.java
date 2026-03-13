package formatter.constructs.impl;

import org.junit.Test;

import static formatter.Utils.assertUnchanged;

public class PrefixExprConstructTest {

    @Test
    public void testBoxOperatorNoSpaceWithActionExpr() {
        var s = "----- MODULE Test -----\n" +
                "VARIABLE x\n" +
                "Next == x' = x\n" +
                "Spec == [][Next]_x\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    public void testBoxOperatorNoSpaceWithIdentifier() {
        var s = "----- MODULE Test -----\n" +
                "VARIABLE x\n" +
                "Inv == x = 0\n" +
                "Prop == []Inv\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    public void testDiamondOperatorNoSpace() {
        var s = "----- MODULE Test -----\n" +
                "VARIABLE x\n" +
                "Inv == x = 0\n" +
                "Prop == <>Inv\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    public void testDomainHasSpace() {
        var s = "----- MODULE Test -----\n" +
                "VARIABLE f\n" +
                "op == DOMAIN f\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    public void testSubsetHasSpace() {
        var s = "----- MODULE Test -----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLE x\n" +
                "op == SUBSET x\n" +
                "====";
        assertUnchanged(s);
    }

}
