package formatter.constructs.impl;

import org.junit.Test;

import static formatter.Utils.assertSpecEquals;
import static formatter.Utils.assertUnchanged;

public class TimesConstructTest {
    @Test
    public void testTimesCompact() {
        var s = "----- MODULE Times -----\n" +
                "CONSTANTS A, B\n" +
                "AVeryLongName == A \\X B\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    public void testTimesChained() {
        var s = "----- MODULE Times -----\n" +
                "CONSTANTS A, B, C\n" +
                "AVeryLongName == A \\X B \\X C\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    public void testTimesChainedFour() {
        var s = "----- MODULE Times -----\n" +
                "CONSTANTS A, B, C, D\n" +
                "AVeryLongName == A \\X B \\X C \\X D\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    public void testTimesWrapped() {
        var t = "ALongLineName == AVeryLongConstName \\X BVeryLongConstName";
        var s = "----- MODULE Spec -----\n" +
                "CONSTANTS AVeryLongConstName, BVeryLongConstName\n" +
                t + "\n" +
                "====";

        var expected = "----- MODULE Spec -----\n" +
                "CONSTANTS AVeryLongConstName, BVeryLongConstName\n" +
                "ALongLineName ==\n" +
                "  AVeryLongConstName \\X\n" +
                "    BVeryLongConstName\n" +
                "====";
        assertSpecEquals(expected, s, t.length() / 2);
    }
}