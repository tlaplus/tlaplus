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
        Path inputFile = tempDir.getRoot().toPath().resolve("TestModule.tla");
        Files.writeString(inputFile, "---- MODULE TestModule ----\nVARIABLE x\n====================");

        Path outputFile = tempDir.getRoot().toPath().resolve("output.tla");

        ByteArrayOutputStream outContent = new ByteArrayOutputStream();
        System.setOut(new PrintStream(outContent, false, StandardCharsets.UTF_8));

        ByteArrayOutputStream errContent = new ByteArrayOutputStream();
        System.setErr(new PrintStream(errContent, false, StandardCharsets.UTF_8));

        int exitCode = Main.mainWrapper(new String[]{inputFile.toString(), outputFile.toString()});

        assertTrue("Output file should be created", Files.exists(outputFile));

        String outputContent = Files.readString(outputFile);
        String expectedOutput = "---- MODULE TestModule ----\n" +
                "VARIABLE x\n" +
                "====================";
        assertEquals("Output content should match expected formatted content",
                expectedOutput.replace("\r\n", "\n"), outputContent.replace("\r\n", "\n"));

        assertEquals("Exit code should be 0 for successful execution", 0, exitCode);
    }


    @Test
    public void testMainWithInvalidArguments() {
        int exitCode = Main.mainWrapper(new String[]{});
        assertEquals("Exit code should be 1 for invalid arguments", 1, exitCode);
    }

    @Test
    public void testMainWithNonExistentInputFile() {
        int exitCode = Main.mainWrapper(new String[]{"nonexistent.tla", "output.tla"});
        assertEquals("Exit code should be 1 for non-existent input file", 1, exitCode);
    }

    @Test
    public void testMainWithVerbosityOption() throws Exception {
        Path inputFile = tempDir.getRoot().toPath().resolve("TestModule.tla");
        Files.writeString(inputFile, "---- MODULE TestModule ----\nVARIABLE x\n====================");
        Path outputFile = tempDir.getRoot().toPath().resolve("output.tla");

        int exitCode = Main.mainWrapper(new String[]{"-v", "DEBUG", inputFile.toString(), outputFile.toString()});
        assertEquals("Exit code should be 0 for valid arguments", 0, exitCode);
    }
}
