package formatter.constructs.impl;

import org.junit.Test;

import static formatter.Utils.assertSpecEquals;
import static formatter.Utils.assertUnchanged;

public class SubsetOfConstructTest {

    @Test
    public void testSimpleSubsetOf() {
        var s = "----- MODULE Test -----\n" +
                "VARIABLE x\n" +
                "op == {y \\in x: y = y}\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    public void testSubsetOfWithConjunctionListWraps() {
        // When the predicate after : is a conjunction list and the line is too long,
        // the predicate should break to a new line with proper indentation,
        // keeping conjunction items aligned.
        // This is the InnerSerial.tla bug: conjunction items were misaligned.
        var s = "----- MODULE Test -----\n" +
                "VARIABLE x\n" +
                "op ==\n" +
                "  {R \\in SUBSET ( x \\X x ):\n" +
                "    /\\ \\A oi, oj \\in x: ( oi = oj ) \\/ ( oi = oj ) \\/ ( oj = oi )\n" +
                "    /\\ \\A oi, oj, ok \\in x: ( oi = oj ) /\\ ( oj = ok ) => ( oi = ok )\n" +
                "    /\\ \\A oi \\in x: oi = oi\n" +
                "  }\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    public void testSubsetOfWithConjunctionNarrowWidth() {
        // With narrow width, but conjunction fits aligned on same line as :
        var s = "----- MODULE Test -----\n" +
                "VARIABLE x\n" +
                "op == {R \\in x: /\\ R = R\n" +
                "                /\\ x = x}\n" +
                "====";
        assertSpecEquals(s, s, 30);
    }

    @Test
    public void testSubsetOfWithDisjunctionListWraps() {
        // Disjunction list also aligns properly
        var s = "----- MODULE Test -----\n" +
                "VARIABLE x\n" +
                "op == {R \\in x: \\/ R = R\n" +
                "                \\/ x = x\n" +
                "                \\/ x = R}\n" +
                "====";
        assertSpecEquals(s, s, 30);
    }
}
