package formatter;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class MainTest {
    @TempDir
    Path tempDir;

    @Test
    void testMainWithValidInput() throws Exception {
        // Create a sample TLA+ file
        Path inputFile = tempDir.resolve("TestModule.tla");
        Files.writeString(inputFile, "---- MODULE TestModule ----\nVARIABLE x\n====================");

        Path outputFile = tempDir.resolve("output.tla");

        // Redirect System.out to capture output
        ByteArrayOutputStream outContent = new ByteArrayOutputStream();
        System.setOut(new PrintStream(outContent, false, StandardCharsets.UTF_8));

        // Redirect System.err to capture error output
        ByteArrayOutputStream errContent = new ByteArrayOutputStream();
        System.setErr(new PrintStream(errContent, false, StandardCharsets.UTF_8));

        int exitCode = Main.mainWrapper(new String[]{inputFile.toString(), outputFile.toString()});

        // Check if the output file was created
        assertTrue(Files.exists(outputFile), "Output file should be created");

        // Read the content of the output file
        String outputContent = Files.readString(outputFile);

        // Assert the content is formatted as expected
        String expectedOutput = "---- MODULE TestModule ----\n" +
                "VARIABLE x\n" +
                "====================";
        assertEquals(expectedOutput, outputContent, "Output content should match expected formatted content");

        // Check console output
        assertTrue(outContent.toString(StandardCharsets.UTF_8).contains("Formatted output written to:"), "Console should indicate successful formatting");
        assertTrue(errContent.toString(StandardCharsets.UTF_8).isEmpty(), "No error messages should be printed");

        // Check exit code
        assertEquals(0, exitCode, "Exit code should be 0 for successful execution");
    }


    @Test
    void testMainWithInvalidArguments() {
        // Redirect System.err to capture error output
        ByteArrayOutputStream errContent = new ByteArrayOutputStream();
        System.setOut(new PrintStream(errContent, false, StandardCharsets.UTF_8));

        // Run the main method with invalid arguments
        int exitCode = Main.mainWrapper(new String[]{});

        // Check if the error message is printed
        assertTrue(errContent.toString(StandardCharsets.UTF_8).contains("Please provide one or two file paths"), "Error message should be printed for invalid arguments");
        assertEquals(1, exitCode, "Exit code should be 1 for invalid arguments");
    }

    @Test
    void testMainWithNonExistentInputFile() {
        // Redirect System.err to capture error output
        ByteArrayOutputStream errContent = new ByteArrayOutputStream();
        System.setOut(new PrintStream(errContent, false, StandardCharsets.UTF_8));

        // Run the main method with a non-existent input file
        int exitCode = Main.mainWrapper(new String[]{"nonexistent.tla", "output.tla"});

        // Check if the error message is printed
        assertTrue(errContent.toString(StandardCharsets.UTF_8).contains("Input file does not exist"), "Error message should be printed for non-existent input file");
        assertEquals(1, exitCode, "Exit code should be 1 for non-existent input file");
    }

    @Test
    void testMainWithVerbosityOption() throws Exception {
        // Create a sample TLA+ file
        Path inputFile = tempDir.resolve("TestModule.tla");
        Files.writeString(inputFile, "---- MODULE TestModule ----\nVARIABLE x\n====================");
        Path outputFile = tempDir.resolve("output.tla");

        // Redirect System.out to capture output
        ByteArrayOutputStream outContent = new ByteArrayOutputStream();
        System.setOut(new PrintStream(outContent, false, StandardCharsets.UTF_8));

        // Run the main method with verbosity option
        int exitCode = Main.mainWrapper(new String[]{"-v", "DEBUG", inputFile.toString(), outputFile.toString()});

        // Check if debug messages are printed
        assertTrue(outContent.toString(StandardCharsets.UTF_8).contains("DEBUG"), "Debug messages should be printed with verbosity option");
        assertEquals(0, exitCode, "Exit code should be 0 for valid arguments");
    }
}
