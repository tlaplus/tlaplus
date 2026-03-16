package formatter.constructs.impl;

import static org.junit.Assert.*;
import static org.junit.Assume.assumeTrue;
import formatter.TLAPlusFormatter;
import org.junit.Test;

import static formatter.Utils.assertUnchanged;

public class ExtendsConstructTest {

    private static void assumeTlapsAvailable() {
        String tlaLib = System.getProperty("TLA-Library", System.getenv().getOrDefault("TLA_LIBRARY", ""));
        assumeTrue("Skipping: TLAPS not available (set -DTLA-Library=... to include tlapm/library)", !tlaLib.isEmpty());
    }

    @Test
    public void testExtendsWithCommentsOnMultipleModules() {
        // Comments after non-last EXTENDS modules are preserved as pre-comments
        // on the following module node. The comment after the last module goes to the
        // next construct keyword (VARIABLE), which is handled by that construct.
        String spec = "---- MODULE TestExtendsComments ----\n" +
                "EXTENDS Naturals,\n" +
                "        TLC,\n" +
                "        Sequences, \\* Trace operator\n" +
                "        FiniteSets\n" +
                "VARIABLE x\n" +
                "====\n";
        assertUnchanged(spec);
    }

    @Test
    public void testExtendsWithCommentOnEveryNonLastModule() {
        String spec = "---- MODULE TestExtendsAllComments ----\n" +
                "EXTENDS Naturals, \\* basic math\n" +
                "        Sequences, \\* sequence ops\n" +
                "        FiniteSets\n" +
                "VARIABLE x\n" +
                "====\n";
        assertUnchanged(spec);
    }

    @Test
    public void testExtendsWithCommentsOnAllNonLastModulesFour() {
        String spec = "---- MODULE TestExtendsFourComments ----\n" +
                "EXTENDS Naturals, \\* basic math\n" +
                "        Sequences, \\* sequence ops\n" +
                "        FiniteSets, \\* finite set ops\n" +
                "        TLC\n" +
                "VARIABLE x\n" +
                "====\n";
        assertUnchanged(spec);
    }

    @Test
    public void testExtendsWithBlockCommentOnModule() {
        String spec = "---- MODULE TestExtendsBlockComment ----\n" +
                "EXTENDS Naturals,\n" +
                "        (* utility module *)\n" +
                "        TLC\n" +
                "VARIABLE x\n" +
                "====\n";
        assertUnchanged(spec);
    }

    /**
     * Helper to assert no line in the formatted output exceeds the line width.
     * Module names after EXTENDS should indent at ~8 chars ("EXTENDS "), not at
     * the rendered length of any preComments on the EXTENDS keyword.
     */
    private void assertNoExcessiveIndentation(String output) {
        for (String line : output.split("\n")) {
            assertTrue("Line has excessive indentation (" + line.length() + " chars): " +
                            line.substring(0, Math.min(80, line.length())),
                    line.length() <= 90);
        }
    }

    @Test
    public void testExtendsWithPreCommentAndManyModulesExceedingLineWidth() throws Exception {
        assumeTlapsAvailable();
        // Quicksort.tla pattern: block comment before EXTENDS + >3 modules + line > 80 chars.
        // The preComment on the EXTENDS keyword inflated prefix.render().length() causing
        // massive indentation when SMART_BREAK triggered line wrapping.
        String spec = "---- MODULE TestExtendsPreComment ----\n" +
                "(***********************************************)\n" +
                "(* A block comment before EXTENDS.             *)\n" +
                "(***********************************************)\n" +
                "EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems, FiniteSetTheorems\n" +
                "VARIABLE x\n" +
                "====\n";
        TLAPlusFormatter f = new TLAPlusFormatter(spec);
        String out = f.getOutput();
        assertTrue("EXTENDS keyword not found in output:\n" + out, out.contains("EXTENDS"));
        assertNoExcessiveIndentation(out);
    }

    @Test
    public void testExtendsWithLineCommentAndManyModulesExceedingLineWidth() throws Exception {
        assumeTlapsAvailable();
        // Same bug with a line comment instead of block comment before EXTENDS
        String spec = "---- MODULE TestExtendsLineComment ----\n" +
                "\\* A line comment before EXTENDS that is long enough to trigger the bug\n" +
                "EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems, FiniteSetTheorems\n" +
                "VARIABLE x\n" +
                "====\n";
        TLAPlusFormatter f = new TLAPlusFormatter(spec);
        String out = f.getOutput();
        assertNoExcessiveIndentation(out);
    }

    @Test
    public void testExtendsWithMultiplePreCommentsAndManyModules() throws Exception {
        assumeTlapsAvailable();
        // Multiple comments before EXTENDS
        String spec = "---- MODULE TestExtendsMultiPreComments ----\n" +
                "\\* First comment explaining the module purpose\n" +
                "\\* Second comment with additional details about the specification\n" +
                "(* Block comment with even more context *)\n" +
                "EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems, FiniteSetTheorems\n" +
                "VARIABLE x\n" +
                "====\n";
        TLAPlusFormatter f = new TLAPlusFormatter(spec);
        String out = f.getOutput();
        assertNoExcessiveIndentation(out);
    }

    @Test
    public void testExtendsWithLargePreCommentPreservesSemantics() throws Exception {
        assumeTlapsAvailable();
        // The formatted output must still be valid TLA+ (parseable by SANY)
        String spec = "---- MODULE TestExtendsSemantic ----\n" +
                "(***********************************************)\n" +
                "(* Large block comment with many lines.        *)\n" +
                "(* More text to make the prefix large.         *)\n" +
                "(* Even more text for good measure.            *)\n" +
                "(***********************************************)\n" +
                "EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems, FiniteSetTheorems\n" +
                "VARIABLE x\n" +
                "====\n";
        TLAPlusFormatter f1 = new TLAPlusFormatter(spec);
        String out1 = f1.getOutput();
        assertNoExcessiveIndentation(out1);
        // Must be parseable (no exception)
        TLAPlusFormatter f2 = new TLAPlusFormatter(out1);
        String out2 = f2.getOutput();
        // Must be idempotent
        assertEquals("Formatter should be idempotent", out1, out2);
    }
}
