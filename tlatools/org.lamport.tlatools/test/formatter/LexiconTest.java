package formatter;

import tla2sany.st.TreeNode;

import java.io.File;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;

import static formatter.Utils.assertAstEquals;
import static org.junit.Assert.*;

public abstract class LexiconTest {

    /**
     * Compares src/test/resources/inputs/name.tla to src/test/resources/outputs/name.tla
     */
    public void testSpecFiles(String name) {
        try {
            URL resource = getClass().getClassLoader().getResource("inputs/" + name + ".tla");
            assertNotNull("Resource file not found", resource);
            File input = new File(resource.toURI());
            var f = new TLAPlusFormatter(input, new FormatConfig(80, 2));
            var actual = f.getOutput();
            compareOutputSpec(name, actual, f.root);
        } catch (Exception e) {
            fail(e.getMessage());
        }
    }

    void compareOutputSpec(String name, String actual, TreeNode root1) {
        try {
            URL outputFile = getClass().getClassLoader().getResource("outputs/" + name + ".tla");
            assertNotNull("Resource file not found", outputFile);
            String expected = Files.readString(Path.of(outputFile.toURI()));
            assertNotNull("Formatted output is null", actual);
            assertNotNull("Expected output is null", expected);
            assertEquals("Formatted output does not match expected output(" + outputFile.toURI() + ").", expected, actual);


            // initialize tlaplusfmt using output file path.
            // in this way, if the spec EXTENDS other specs, we can include them in the outputs resource folder.
            // For example see TowerOfHanoi.tla.
            // If output is an invalid spec, SANY will let us know.
            var f2 = new TLAPlusFormatter(new File(outputFile.toURI()));

            // the ast of the initial spec should match the ast of the output spec.
            // initial spec is the non-reformatted input. f2 is the parsed ast of the reformat output.
            assertAstEquals(root1, f2.root);

            // It should be a bit redundant with the compareAst above, but it's just an additional sanity check.
            // might remove later to keep tests fast
            actual = f2.getOutput();
            assertNotNull("Formatted output is null", actual);
            assertEquals("Second formatted output does not match expected output", expected, actual);
        } catch (Exception e) {
            fail(actual + ": " + e.getMessage());
        }
    }

    // TODO: compare AST of pre format and post format.
}