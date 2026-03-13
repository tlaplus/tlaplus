package formatter;

import org.junit.Test;
import static org.junit.Assert.*;
import org.junit.Rule;
import org.junit.rules.TemporaryFolder;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;


public class MainTest {
    @Rule
    public TemporaryFolder tempDir = new TemporaryFolder();

    @Test
    public void testMainWithValidInput() throws Exception {
        // Create a sample TLA+ file
        Path inputFile = tempDir.getRoot().toPath().resolve("TestModule.tla");
        Files.writeString(inputFile, "---- MODULE TestModule ----\nVARIABLE x\n====================");

        Path outputFile = tempDir.getRoot().toPath().resolve("output.tla");

        // Redirect System.out to capture output
        ByteArrayOutputStream outContent = new ByteArrayOutputStream();
        System.setOut(new PrintStream(outContent, false, StandardCharsets.UTF_8));

        // Redirect System.err to capture error output
        ByteArrayOutputStream errContent = new ByteArrayOutputStream();
        System.setErr(new PrintStream(errContent, false, StandardCharsets.UTF_8));

        int exitCode = Main.mainWrapper(new String[]{inputFile.toString(), outputFile.toString()});

        // Check if the output file was created
        assertTrue("Output file should be created", Files.exists(outputFile));

        // Read the content of the output file
        String outputContent = Files.readString(outputFile);

        // Assert the content is formatted as expected
        String expectedOutput = "---- MODULE TestModule ----\n" +
                "VARIABLE x\n" +
                "====================";
        assertEquals("Output content should match expected formatted content", expectedOutput, outputContent);

        // Check exit code
        assertEquals("Exit code should be 0 for successful execution", 0, exitCode);
    }


    @Test
    public void testMainWithInvalidArguments() {
        // Run the main method with invalid arguments
        int exitCode = Main.mainWrapper(new String[]{});

        // Check exit code
        assertEquals("Exit code should be 1 for invalid arguments", 1, exitCode);
    }

    @Test
    public void testMainWithNonExistentInputFile() {
        // Run the main method with a non-existent input file
        int exitCode = Main.mainWrapper(new String[]{"nonexistent.tla", "output.tla"});

        // Check exit code
        assertEquals("Exit code should be 1 for non-existent input file", 1, exitCode);
    }

    @Test
    public void testMainWithVerbosityOption() throws Exception {
        // Create a sample TLA+ file
        Path inputFile = tempDir.getRoot().toPath().resolve("TestModule.tla");
        Files.writeString(inputFile, "---- MODULE TestModule ----\nVARIABLE x\n====================");
        Path outputFile = tempDir.getRoot().toPath().resolve("output.tla");

        // Run the main method with verbosity option
        int exitCode = Main.mainWrapper(new String[]{"-v", "DEBUG", inputFile.toString(), outputFile.toString()});

        assertEquals("Exit code should be 0 for valid arguments", 0, exitCode);
    }
}
