package formatter;

import formatter.exceptions.AstVerificationException;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.*;

class AstVerificationTest {

    private static final String SIMPLE_SPEC =
            "---- MODULE Spec ----\nVARIABLE x\nInit == x = 0\n====\n";

    @TempDir
    Path tempDir;

    @Test
    void testVerificationEnabledByDefault() throws Exception {
        // Default constructor enables verification — should succeed on valid spec
        TLAPlusFormatter formatter = new TLAPlusFormatter(SIMPLE_SPEC);
        assertNotNull(formatter.getOutput());
    }

    @Test
    void testVerificationCanBeExplicitlyEnabled() throws Exception {
        TLAPlusFormatter formatter = new TLAPlusFormatter(SIMPLE_SPEC, new FormatConfig(), true);
        assertNotNull(formatter.getOutput());
    }

    @Test
    void testVerificationCanBeSkipped() throws Exception {
        TLAPlusFormatter formatter = new TLAPlusFormatter(SIMPLE_SPEC, new FormatConfig(), false);
        assertNotNull(formatter.getOutput());
    }

    @Test
    void testAstComparatorMatchingTrees() throws Exception {
        TLAPlusFormatter f1 = new TLAPlusFormatter(SIMPLE_SPEC, new FormatConfig(), false);
        TLAPlusFormatter f2 = new TLAPlusFormatter(f1.getOutput(), new FormatConfig(), false);
        AstComparator.Result result = AstComparator.compare(f1.root, f2.root);
        assertTrue(result.isMatch());
        assertEquals("ASTs match.", result.formatDiagnostic());
    }

    @Test
    void testAstComparatorResultContainsNodePath() throws Exception {
        // Two different specs produce different ASTs
        String spec1 = "---- MODULE Spec ----\nVARIABLE x\n====\n";
        String spec2 = "---- MODULE Spec ----\nVARIABLES x, y\n====\n";
        TLAPlusFormatter f1 = new TLAPlusFormatter(spec1, new FormatConfig(), false);
        TLAPlusFormatter f2 = new TLAPlusFormatter(spec2, new FormatConfig(), false);
        AstComparator.Result result = AstComparator.compare(f1.root, f2.root);
        assertFalse(result.isMatch());
        assertNotNull(result.getDescription());
        assertFalse(result.getNodePath().isEmpty(), "Node path should not be empty on mismatch");
        String diagnostic = result.formatDiagnostic();
        assertTrue(diagnostic.contains("AST verification failed"));
        assertTrue(diagnostic.contains("Node path:"));
    }

    @Test
    void testAstVerificationExceptionContainsResult() {
        AstComparator.Result failResult = new AstComparator.Result("test failure");
        AstVerificationException ex = new AstVerificationException(failResult);
        assertSame(failResult, ex.getResult());
        assertTrue(ex.getMessage().contains("test failure"));
    }

    @Test
    void testSkipAstVerificationFlag() throws Exception {
        Path inputFile = tempDir.resolve("TestModule.tla");
        Files.writeString(inputFile, "---- MODULE TestModule ----\nVARIABLE x\n====================");

        PrintStream originalOut = System.out;
        PrintStream originalErr = System.err;
        try {
            ByteArrayOutputStream outContent = new ByteArrayOutputStream();
            ByteArrayOutputStream errContent = new ByteArrayOutputStream();
            System.setOut(new PrintStream(outContent, false, StandardCharsets.UTF_8));
            System.setErr(new PrintStream(errContent, false, StandardCharsets.UTF_8));

            int exitCode = Main.mainWrapper(new String[]{
                    "--skip-ast-verification", inputFile.toString()
            });

            assertEquals(0, exitCode, "Exit code should be 0 with --skip-ast-verification");
            String stdout = outContent.toString(StandardCharsets.UTF_8);
            assertTrue(stdout.contains("MODULE TestModule"), "Should produce formatted output");
        } finally {
            System.setOut(originalOut);
            System.setErr(originalErr);
        }
    }

    @Test
    void testDefaultVerificationSucceedsViaCli() throws Exception {
        Path inputFile = tempDir.resolve("TestModule.tla");
        Files.writeString(inputFile, "---- MODULE TestModule ----\nVARIABLE x\n====================");

        PrintStream originalOut = System.out;
        PrintStream originalErr = System.err;
        try {
            ByteArrayOutputStream outContent = new ByteArrayOutputStream();
            ByteArrayOutputStream errContent = new ByteArrayOutputStream();
            System.setOut(new PrintStream(outContent, false, StandardCharsets.UTF_8));
            System.setErr(new PrintStream(errContent, false, StandardCharsets.UTF_8));

            // No --skip-ast-verification flag -- verification is enabled by default
            int exitCode = Main.mainWrapper(new String[]{inputFile.toString()});

            assertEquals(0, exitCode, "Exit code should be 0 when verification passes");
            String stdout = outContent.toString(StandardCharsets.UTF_8);
            assertTrue(stdout.contains("MODULE TestModule"), "Should produce formatted output");
        } finally {
            System.setOut(originalOut);
            System.setErr(originalErr);
        }
    }
}
