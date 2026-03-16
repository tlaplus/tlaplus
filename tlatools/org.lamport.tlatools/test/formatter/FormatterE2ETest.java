package formatter;

import formatter.exceptions.SanyFrontendException;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import static formatter.Utils.assertSpecEquals;
import static formatter.Utils.assertSpecUnchanged;
import static org.junit.Assert.*;

/**
 * End-to-end tests for the TLA+ formatter.
 * These tests create TLA+ specifications as strings, format them,
 * and verify the output structure and formatting quality.
 */
public class FormatterE2ETest {

    @Test
    public void testSimpleModuleFormatting() {
        String spec = "---- MODULE SimpleTest ----\n" +
                "VARIABLE x\n" +
                "Init == x = 0\n" +
                "====\n";
        assertSpecUnchanged(spec);
    }

    @Test
    public void testModuleWithExtends() {
        String spec = "---- MODULE TestWithExtends ----\n" +
                "EXTENDS Naturals, TLC\n" +
                "VARIABLE counter\n" +
                "====\n";
        assertSpecUnchanged(spec);
    }

    @Test
    public void testMultipleVariables() {
        String spec = "---- MODULE MultiVar ----\n" +
                "VARIABLES x, y, z\n" +
                "====\n";
        assertSpecUnchanged(spec);
    }

    @Test
    public void testOperatorDefinition() {
        String spec = "---- MODULE OpTest ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLE x\n" +
                "Inc == x + 1\n" +
                "====\n";

        assertSpecUnchanged(spec);
    }

    @Test
    public void testComplexExpression() {
        String spec = "---- MODULE ComplexTest ----\n" +
                "VARIABLE state\n" +
                "NextState == state' = IF state = \"ready\" THEN \"running\" ELSE \"done\"\n" +
                "====\n";
        assertSpecUnchanged(spec);
    }

    @Test
    public void testLineWidthConfiguration() {
        String spec = "---- MODULE WidthTest ----\n" +
                "VARIABLES verylongvariablename, anotherlongname, yetanothername, abc\n" +
                "====\n";
        assertSpecUnchanged(spec);
        String wrapped = "---- MODULE WidthTest ----\n" +
                "VARIABLES verylongvariablename,\n" +
                "          anotherlongname,\n" +
                "          yetanothername,\n" +
                "          abc\n" +
                "====\n";
        assertSpecEquals(wrapped, spec, 20);
    }

    @Test
    public void testLongOperatorBreaking() {
        String spec = "---- MODULE LongOpTest ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLE state\n" +
                "VeryLongOperatorName == state = \"this is a long expression that should break\"\n" +
                "====\n";
        String wrapped = "---- MODULE LongOpTest ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLE state\n" +
                "VeryLongOperatorName ==\n" +
                "  state = \"this is a long expression that should break\"\n" +
                "====\n";
        assertSpecUnchanged(spec);
        assertSpecEquals(wrapped, spec, 60);
    }

    @Test
    public void testShortVsLongOperatorFormatting() {
        // Short operator should stay on one line
        String shortSpec = "---- MODULE ShortOp ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLE x\n" +
                "Inc == x + 1\n" +
                "====\n";
        assertSpecUnchanged(shortSpec);

        // Long operator should break with narrow width
        String longSpec = "---- MODULE LongOp ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLE state\n" +
                "VeryLongOperatorName == state = \"this is a very long expression that should break when narrow\"\n" +
                "====\n";
        String expectedWrapped = "---- MODULE LongOp ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLE state\n" +
                "VeryLongOperatorName ==\n" +
                "  state =\n" +
                "    \"this is a very long expression that should break when narrow\"\n" +
                "====\n";
        assertSpecEquals(expectedWrapped, longSpec, 40);
    }

    @Test
    public void testPreAndPostModuleContent() {
        String spec = "This is a comment before the module.\n" +
                "---- MODULE TestModule ----\n" +
                "VARIABLE x\n" +
                "====\n" +
                "This is content after the module.\n";
        assertSpecUnchanged(spec);
    }

    @Test
    public void testTheorem() {
        String spec = "---- MODULE TheoremTest ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLE x\n" +
                "THEOREM TRUE\n" +
                "====\n";
        assertSpecUnchanged(spec);
    }

    @Test
    public void testNamedTheorem() {
        String spec = "---- MODULE NamedTheoremTest ----\n" +
                "VARIABLE x\n" +
                "THEOREM MyTheorem == x = 0\n" +
                "====\n";
        assertSpecUnchanged(spec);
    }

    @Test
    public void testEmptyModule() {
        String spec = "---- MODULE Empty ----\n" +
                "====\n";
        assertSpecUnchanged(spec);
    }

    @Test
    public void testConfigurationValidation() {
        try {
            new FormatConfig(-1, 4);
            fail("Expected IllegalArgumentException");
        } catch (IllegalArgumentException e) {
            // expected
        }
        try {
            new FormatConfig(80, -1);
            fail("Expected IllegalArgumentException");
        } catch (IllegalArgumentException e) {
            // expected
        }

        // These should be valid — no exception expected
        new FormatConfig(1, 0);
        new FormatConfig(200, 8);
    }

    @Test
    public void testComplexModuleStructure() {
        String spec = "---- MODULE ComplexStructure ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLES x, y, z\n" +
                "\n" +
                "Init == x = 0\n" +
                "\n" +
                "Next == x + 1\n" +
                "\n" +
                "Spec == TRUE\n" +
                "\n" +
                "THEOREM TRUE\n" +
                "====\n";
        assertSpecUnchanged(spec);
    }

    @Test
    public void testNewlinePreservation() {
        String spec = "---- MODULE NewlineTest ----\n" +
                //"\n" + TODO: currently removing leading newlines
                "VARIABLE x\n" +
                "\n" +
                "\n" +
                "Init == x = 0\n" +
                "\n" +
                "====\n";
        assertSpecUnchanged(spec);
    }

    @Test
    public void testMultipleNewlinePatterns() {
        String spec = "---- MODULE MultiNewline ----\n" +
                "EXTENDS Naturals\n" +
                "\n" +
                "\n" +
                "\n" +
                "VARIABLES x, y\n" +
                "\n" +
                "Op1 == TRUE\n" +
                "\n" +
                "\n" +
                "Op2 == FALSE\n" +
                "====\n";
        assertSpecUnchanged(spec);
    }

    @Test
    public void testSingleNewlinesRemainSingle() {
        String spec = "---- MODULE SingleNewlines ----\n" +
                "VARIABLE x\n" +
                "Init == x = 0\n" +
                "====\n";
        assertSpecUnchanged(spec);
    }

    @Test
    public void testExtendsLocalModuleWithOtherModules() throws IOException, SanyFrontendException {
        // SANY returns empty getHumanReadableImage() for certain local module names
        // in EXTENDS, even though getImage() has the correct value.
        // This caused "EXTENDS , TLC" instead of "EXTENDS TokenRing, TLC".
        Path tmpDir = Files.createTempDirectory("tlatest");
        try {
            String baseModule = "---- MODULE TokenRing ----\n" +
                    "EXTENDS Naturals\n" +
                    "VARIABLE x\n" +
                    "====\n";
            Files.writeString(tmpDir.resolve("TokenRing.tla"), baseModule);

            String mainModule = "---- MODULE Main ----\n" +
                    "EXTENDS TokenRing, TLC\n" +
                    "====\n";
            File mainFile = tmpDir.resolve("Main.tla").toFile();
            Files.writeString(mainFile.toPath(), mainModule);

            TLAPlusFormatter formatter = new TLAPlusFormatter(mainFile);
            String output = formatter.getOutput();
            assertTrue("EXTENDS should preserve local module name, got: " + output,
                    output.contains("EXTENDS TokenRing, TLC"));
        } finally {
            Files.walk(tmpDir).sorted(java.util.Comparator.reverseOrder())
                    .map(Path::toFile).forEach(File::delete);
        }
    }

    @Test
    public void testModuleWithExtendsBreak() {
        String spec = "---- MODULE TestWithExtends ----\n" +
                "EXTENDS Naturals, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC\n" +
                "VARIABLE counter\n" +
                "====\n";
        String wrapped = "---- MODULE TestWithExtends ----\n" +
                "EXTENDS Naturals,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC\n" +
                "VARIABLE counter\n" +
                "====\n";
        assertSpecEquals(wrapped, spec);

    }
}