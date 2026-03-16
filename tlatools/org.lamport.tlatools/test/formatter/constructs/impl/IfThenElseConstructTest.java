package formatter.constructs.impl;

import org.junit.Test;

import static formatter.Utils.assertSpecEquals;
import static formatter.Utils.assertUnchanged;

public class IfThenElseConstructTest {
    @Test
    public void testCompact() {
        var s = "----- MODULE Times -----\n" +
                "CONSTANTS A, B\n" +
                "AVeryLongName == IF TRUE THEN A ELSE B\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    public void testWrapped() {

        var t = "ALongLineName == IF TRUE THEN AVeryLongConstName ELSE BVeryLongConstName";
        var s = "----- MODULE Times -----\n" +
                "CONSTANTS AVeryLongConstName, BVeryLongConstName\n" +
                t + "\n" +
                "====";
        var expected = "----- MODULE Times -----\n" +
                "CONSTANTS AVeryLongConstName, BVeryLongConstName\n" +
                "ALongLineName ==\n" +
                "  IF TRUE\n" +
                "  THEN AVeryLongConstName\n" +
                "  ELSE BVeryLongConstName\n" +
                "====";

        assertSpecEquals(expected, s, t.length() / 2);
    }

}