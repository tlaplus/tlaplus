package formatter;

import formatter.exceptions.SanyException;
import formatter.exceptions.SanyFrontendException;
import formatter.exceptions.SanySemanticException;
import formatter.exceptions.SanySyntaxException;
import tla2sany.drivers.FrontEndException;
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.output.LogLevel;
import tla2sany.output.SimpleSanyOutput;
import tla2sany.st.TreeNode;
import util.SimpleFilenameToStream;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;

public class SANYWrapper {
    public static TreeNode load(File file) throws IOException, SanyFrontendException {
        var errBuf = new StringWriter();

        String parentDirPath = file.getAbsoluteFile().getParent();

        // Build library paths: parent dir + any paths from -DTLA-Library
        var libraryPaths = buildLibraryPaths(parentDirPath);
        var filenameResolver = new CustomFilenameToStream(libraryPaths);

        // Set a unique tmpdir to avoid race-condition in SANY
        // TODO: RM once https://github.com/tlaplus/tlaplus/issues/688 is fixed
        System.setProperty("java.io.tmpdir", sanyTempDir().toString());

        var specObj = new SpecObj(file.getAbsolutePath(), filenameResolver);
        loadSpecObject(specObj, file, errBuf);
        Hashtable<String, ParseUnit> parseUnitContext = specObj.parseUnitContext;
        return parseUnitContext.get(specObj.getRootModule().getName().toString()).getParseTree();
    }

    /**
     * Builds the array of library paths for SANY's module resolution.
     * Includes the parent directory of the spec file and any paths
     * specified via the -DTLA-Library system property.
     */
    static String[] buildLibraryPaths(String parentDirPath) {
        List<String> paths = new ArrayList<>();
        paths.add(parentDirPath);

        String tlaLibrary = System.getProperty(SimpleFilenameToStream.TLA_LIBRARY);
        if (tlaLibrary != null && !tlaLibrary.isEmpty()) {
            for (String p : tlaLibrary.split(File.pathSeparator)) {
                if (!p.isEmpty()) {
                    paths.add(p);
                }
            }
        }

        return paths.toArray(new String[0]);
    }

    public static void loadSpecObject(SpecObj specObj, File file, StringWriter errBuf) throws IOException, SanyFrontendException {
        var baos = new ByteArrayOutputStream();

        try {
            SANY.frontEndMain(
                    specObj,
                    file.getAbsolutePath(),
                    new SimpleSanyOutput(new PrintStream(baos, false, StandardCharsets.UTF_8), LogLevel.INFO)
            );
        } catch (FrontEndException e) {
            throw new SanyFrontendException(e);
        }

        // Write captured output to errBuf for callers that need it
        errBuf.write(baos.toString(StandardCharsets.UTF_8));

        ThrowOnError(specObj);
    }


    private static File sanyTempDir() throws IOException {
        var tmpDir = Files.createTempDirectory("sanyimp").toFile();
        tmpDir.deleteOnExit();
        return tmpDir;
    }

    private static void ThrowOnError(SpecObj specObj) {
        var parseErrors = specObj.getParseErrors();
        if (parseErrors.isFailure()) {
            throw new SanySyntaxException(parseErrors.toString());
        }
        var semanticErrors = specObj.getSemanticErrors();
        if (semanticErrors.isFailure()) {
            throw new SanySemanticException(semanticErrors.toString());
        }
        // the error level is above zero, so SANY failed for an unknown reason
        if (specObj.getErrorLevel() > 0) {
            throw new SanyException(
                    String.format("Unknown SANY error (error level=%d)", specObj.getErrorLevel())
            );
        }
    }

    private static class CustomFilenameToStream extends SimpleFilenameToStream {
        public CustomFilenameToStream(String[] libraryPaths) {
            super(libraryPaths);
            this.tmpDir.toFile().deleteOnExit();
        }
    }
}
