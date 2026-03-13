package formatter.constructs.impl;

import org.junit.jupiter.api.Test;

import static formatter.Utils.assertUnchanged;

class StringConstructTest {

    @Test
    void testEscapedBackslashInString() {
        // TLA+ string "\\b" represents literal string \b (backslash followed by b)
        // The formatter should preserve the original escape sequences
        String input = "----- MODULE EscapedStrings -----\n" +
                "A == { \"\\\\b\", \"\\\\B\" }\n" +
                "====";
        assertUnchanged(input);
    }

    @Test
    void testEscapedQuoteInString() {
        // TLA+ string "\"" represents a literal double-quote character
        // The formatter should preserve the escape sequence
        String input = "----- MODULE EscapedQuote -----\n" +
                "A == { \"\\\"\" }\n" +
                "====";
        assertUnchanged(input);
    }

    @Test
    void testMultipleEscapeSequences() {
        // Test various escape sequences that might be used in TLA+ strings
        String input = "----- MODULE MultipleEscapes -----\n" +
                "A == { \"\\\\o\", \"\\\\O\", \"\\\\h\", \"\\\\H\" }\n" +
                "====";
        assertUnchanged(input);
    }
}
