package formatter;

import org.junit.Test;

import static formatter.Utils.assertSpecEquals;

public class BlockCommentFormattingTest {

    @Test
    public void simpleInlineBlockComment() {
        // Single-line block comments should preserve their formatting.
        var input = "---------- MODULE Test -----\n" +
                "(* Simple block comment *)\n" +
                "Init == TRUE\n" +
                "====";
        var expected = "---------- MODULE Test -----\n" +
                "(* Simple block comment *)\n" +
                "Init == TRUE\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void nestedBlockComments() {
        // SANY splits multi-line block comments at nested (* markers.
        // The formatter must reassemble them correctly without inserting
        // extra newlines between the pieces.
        var input = "---------- MODULE Test -----\n" +
                "(* outer block with\n" +
                "(* inner single-line comment *)\n" +
                "more content *)\n" +
                "Init == TRUE\n" +
                "====";
        var expected = "---------- MODULE Test -----\n" +
                "(* outer block with\n" +
                "(* inner single-line comment *)\n" +
                "more content *)\n" +
                "Init == TRUE\n" +
                "====";
        assertSpecEquals(expected, input);
    }
}
