package formatter.constructs.impl;

import org.junit.jupiter.api.Test;

import static formatter.Utils.assertSpecEquals;
import static formatter.Utils.assertUnchanged;

public class BoundedQuantConstructTest {
    @Test
    void testBoundQuantCompact() {
        var s = "----- MODULE Times -----\n" +
                "CONSTANTS A, B\n" +
                "AVeryLongName == A \\X B\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    void testBoundQuantWrapped() {
        var t = "ALongLineName == AVeryLongConstName \\X BVeryLongConstName";
        var s = "----- MODULE Times -----\n" +
                "CONSTANTS AVeryLongConstName, BVeryLongConstName\n" +
                t + "\n" +
                "====";
        var expected = "----- MODULE Times -----\n" +
                "CONSTANTS AVeryLongConstName, BVeryLongConstName\n" +
                "ALongLineName ==\n" +
                "  AVeryLongConstName \\X\n" +
                "    BVeryLongConstName\n" +
                "====";

        assertSpecEquals(expected, s, t.length() / 2);
    }

    @Test
    void testBoundQuantLong() {
        var spec = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT max\n" +
                "S == \\A a \\in 1..max: \\E b \\in 1..max: a < b \n" +
                "====\n";
        var expected = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT max\n" +
                "S == \\A a \\in 1 .. max: \\E b \\in 1 .. max: a < b\n" +
                "====\n";
        assertSpecEquals(expected, spec);
    }
}