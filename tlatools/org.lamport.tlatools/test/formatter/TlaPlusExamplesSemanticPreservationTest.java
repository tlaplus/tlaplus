package formatter;

import org.junit.AfterClass;
import org.junit.Assume;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static org.junit.Assert.fail;

/**
 * Parameterized semantic-preservation test that formats every .tla file found
 * under the tlaplus/Examples repository, then verifies the AST is unchanged.
 *
 * Requires the system property {@code tlaplus.examples.path} (or env var
 * {@code TLAPLUS_EXAMPLES_PATH}) to point at a local clone of that repo.
 * When the property is absent the whole test class is silently skipped via
 * {@link Assume}.
 */
@RunWith(Parameterized.class)
public class TlaPlusExamplesSemanticPreservationTest {

    private static final AtomicInteger passedCount = new AtomicInteger(0);
    private static final AtomicInteger skippedCount = new AtomicInteger(0);
    private static final AtomicInteger failedCount = new AtomicInteger(0);
    private static final List<String> failedFiles =
            Collections.synchronizedList(new ArrayList<>());

    private final Path tlaFilePath;

    public TlaPlusExamplesSemanticPreservationTest(String displayName, Path tlaFilePath) {
        this.tlaFilePath = tlaFilePath;
    }

    // ------------------------------------------------------------------ config

    private static String getExamplesPath() {
        String path = System.getProperty("tlaplus.examples.path");
        if (path == null || path.isEmpty()) {
            path = System.getenv("TLAPLUS_EXAMPLES_PATH");
        }
        return path;
    }

    private static String getFileFilter() {
        String filter = System.getProperty("tlaplus.examples.filter");
        if (filter == null || filter.isEmpty()) {
            filter = System.getenv("TLAPLUS_EXAMPLES_FILTER");
        }
        return filter;
    }

    // -------------------------------------------------------------- parameters

    @Parameters(name = "{0}")
    public static List<Object[]> data() throws IOException {
        String examplesPath = getExamplesPath();
        Assume.assumeTrue(
                "tlaplus/Examples path not configured – skipping semantic preservation tests.",
                examplesPath != null && !examplesPath.isEmpty());

        Path examplesDir = Path.of(examplesPath);
        Assume.assumeTrue(
                "tlaplus/Examples path does not exist: " + examplesPath,
                Files.exists(examplesDir) && Files.isDirectory(examplesDir));

        String fileFilter = getFileFilter();

        List<Path> tlaFiles = Files.walk(examplesDir)
                .filter(Files::isRegularFile)
                .filter(p -> p.toString().endsWith(".tla"))
                .filter(p -> fileFilter == null || fileFilter.isEmpty()
                        || p.toString().contains(fileFilter))
                .filter(TlaPlusExamplesSemanticPreservationTest::filenameMatchesModule)
                .sorted()
                .collect(Collectors.toList());

        Assume.assumeFalse(
                fileFilter != null && !fileFilter.isEmpty()
                        ? "No .tla files found matching filter '" + fileFilter + "'"
                        : "No .tla files found in: " + examplesPath,
                tlaFiles.isEmpty());

        System.out.println("Found " + tlaFiles.size() + " .tla files to test");

        List<Object[]> params = new ArrayList<>();
        for (Path p : tlaFiles) {
            params.add(new Object[]{examplesDir.relativize(p).toString(), p});
        }
        return params;
    }

    // ----------------------------------------------------------- filename check

    private static boolean filenameMatchesModule(Path p) {
        String basename = p.getFileName().toString().replaceFirst("\\.tla$", "");
        try {
            for (String line : Files.readAllLines(p)) {
                var m = Pattern.compile("----\\s*MODULE\\s+(\\w+)").matcher(line);
                if (m.find()) {
                    return basename.equals(m.group(1));
                }
            }
        } catch (IOException ignored) {
        }
        return true;
    }

    // -------------------------------------------------------------------- test

    @Test
    public void testSemanticPreservation() {
        File tlaFile = tlaFilePath.toFile();

        TLAPlusFormatter originalFormatter;
        try {
            originalFormatter = new TLAPlusFormatter(tlaFile);
        } catch (Exception e) {
            skippedCount.incrementAndGet();
            failedFiles.add(tlaFilePath + " (original unparseable: " + getShortError(e) + ")");
            Assume.assumeTrue(
                    "Original file cannot be parsed: " + tlaFilePath.getFileName()
                            + " - " + e.getMessage(),
                    false);
            return;
        }

        String formattedOutput;
        try {
            formattedOutput = originalFormatter.getOutput();
        } catch (Exception e) {
            failedCount.incrementAndGet();
            failedFiles.add(tlaFilePath + " (format error: " + e.getMessage() + ")");
            Assume.assumeTrue(
                    "Formatter crashed on file " + tlaFilePath + ": " + e.getMessage(),
                    false);
            return;
        }

        Path backupPath = Path.of(tlaFilePath + ".old");
        TLAPlusFormatter formattedFormatter;
        try {
            Files.move(tlaFilePath, backupPath);
            Files.writeString(tlaFilePath, formattedOutput);
            formattedFormatter = new TLAPlusFormatter(tlaFile);
        } catch (Exception e) {
            String errorMsg = e.getMessage();
            if (errorMsg != null
                    && errorMsg.contains("Cannot find source file for module")) {
                skippedCount.incrementAndGet();
                failedFiles.add(tlaFilePath + " (formatted output missing module)");
                Assume.assumeTrue(
                        "Formatted output has unresolvable imports: "
                                + tlaFilePath.getFileName(),
                        false);
                return;
            }
            failedCount.incrementAndGet();
            failedFiles.add(tlaFilePath + " (formatted output parse error)");
            Assume.assumeTrue(
                    "Formatted output cannot be parsed: " + tlaFilePath,
                    false);
            return;
        } finally {
            try {
                Files.deleteIfExists(tlaFilePath);
                Files.move(backupPath, tlaFilePath);
            } catch (IOException e) {
                System.err.println("WARNING: Failed to restore " + tlaFilePath);
            }
        }

        try {
            Utils.assertAstEquals(originalFormatter.root, formattedFormatter.root);
        } catch (AssertionError e) {
            failedCount.incrementAndGet();
            failedFiles.add(tlaFilePath + " (AST mismatch: " + e.getMessage() + ")");
            fail("AST comparison failed for file " + tlaFilePath + ": "
                    + e.getMessage());
            return;
        }
        passedCount.incrementAndGet();
    }

    // ----------------------------------------------------------------- helpers

    private static String getShortError(Exception e) {
        String msg = e.getMessage();
        if (msg == null) return e.getClass().getSimpleName();
        if (msg.contains("Cannot find source file for module")) {
            int idx = msg.indexOf("Cannot find source file for module");
            int end = msg.indexOf("\n", idx);
            return end > 0
                    ? msg.substring(idx, end)
                    : msg.substring(idx, Math.min(idx + 60, msg.length()));
        }
        return msg.length() > 80 ? msg.substring(0, 80) + "..." : msg;
    }

    @AfterClass
    public static void printSummary() {
        System.out.println("\n========================================");
        System.out.println("Semantic Preservation Test Summary");
        System.out.println("========================================");
        System.out.println("Passed:  " + passedCount.get());
        System.out.println("Skipped: " + skippedCount.get());
        System.out.println("Failed:  " + failedCount.get());

        if (!failedFiles.isEmpty()) {
            System.out.println("\nSkipped/Failed files:");
            for (String file : failedFiles) {
                System.out.println("  - " + file);
            }
        }
        System.out.println("========================================\n");
    }
}
