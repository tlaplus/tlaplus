package formatter;

import formatter.exceptions.AstVerificationException;
import org.junit.Test;
import org.junit.Rule;
import org.junit.rules.TemporaryFolder;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.Assert.*;

public class AstVerificationTest {

    private static final String SIMPLE_SPEC =
            "---- MODULE Spec ----\nVARIABLE x\nInit == x = 0\n====\n";

    @Rule
    public TemporaryFolder tempDir = new TemporaryFolder();

    @Test
    public void testVerificationEnabledByDefault() throws Exception {
        // Default constructor enables verification — should succeed on valid spec
        TLAPlusFormatter formatter = new TLAPlusFormatter(SIMPLE_SPEC);
        assertNotNull(formatter.getOutput());
    }

    @Test
    public void testVerificationCanBeExplicitlyEnabled() throws Exception {
        TLAPlusFormatter formatter = new TLAPlusFormatter(SIMPLE_SPEC, new FormatConfig(), true);
        assertNotNull(formatter.getOutput());
    }

    @Test
    public void testVerificationCanBeSkipped() throws Exception {
        TLAPlusFormatter formatter = new TLAPlusFormatter(SIMPLE_SPEC, new FormatConfig(), false);
        assertNotNull(formatter.getOutput());
    }

    @Test
    public void testAstComparatorMatchingTrees() throws Exception {
        TLAPlusFormatter f1 = new TLAPlusFormatter(SIMPLE_SPEC, new FormatConfig(), false);
        TLAPlusFormatter f2 = new TLAPlusFormatter(f1.getOutput(), new FormatConfig(), false);
        AstComparator.Result result = AstComparator.compare(f1.root, f2.root);
        assertTrue(result.isMatch());
        assertEquals("ASTs match.", result.formatDiagnostic());
    }

    @Test
    public void testAstComparatorResultContainsNodePath() throws Exception {
        // Two different specs produce different ASTs
        String spec1 = "---- MODULE Spec ----\nVARIABLE x\n====\n";
        String spec2 = "---- MODULE Spec ----\nVARIABLES x, y\n====\n";
        TLAPlusFormatter f1 = new TLAPlusFormatter(spec1, new FormatConfig(), false);
        TLAPlusFormatter f2 = new TLAPlusFormatter(spec2, new FormatConfig(), false);
        AstComparator.Result result = AstComparator.compare(f1.root, f2.root);
        assertFalse(result.isMatch());
        assertNotNull(result.getDescription());
        assertFalse("Node path should not be empty on mismatch", result.getNodePath().isEmpty());
        String diagnostic = result.formatDiagnostic();
        assertTrue(diagnostic.contains("AST verification failed"));
        assertTrue(diagnostic.contains("Node path:"));
    }

    @Test
    public void testAstVerificationExceptionContainsResult() {
        AstComparator.Result failResult = new AstComparator.Result("test failure");
        AstVerificationException ex = new AstVerificationException(failResult);
        assertSame(failResult, ex.getResult());
        assertTrue(ex.getMessage().contains("test failure"));
    }

    @Test
    public void testSkipAstVerificationFlag() throws Exception {
        Path inputFile = tempDir.getRoot().toPath().resolve("TestModule.tla");
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

            assertEquals("Exit code should be 0 with --skip-ast-verification", 0, exitCode);
            String stdout = outContent.toString(StandardCharsets.UTF_8);
            assertTrue("Should produce formatted output", stdout.contains("MODULE TestModule"));
        } finally {
            System.setOut(originalOut);
            System.setErr(originalErr);
        }
    }

    @Test
    public void testDefaultVerificationSucceedsViaCli() throws Exception {
        Path inputFile = tempDir.getRoot().toPath().resolve("TestModule.tla");
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

            assertEquals("Exit code should be 0 when verification passes", 0, exitCode);
            String stdout = outContent.toString(StandardCharsets.UTF_8);
            assertTrue("Should produce formatted output", stdout.contains("MODULE TestModule"));
        } finally {
            System.setOut(originalOut);
            System.setErr(originalErr);
        }
    }
}
