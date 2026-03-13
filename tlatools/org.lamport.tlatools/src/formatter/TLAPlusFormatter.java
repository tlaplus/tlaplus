package formatter;

import com.opencastsoftware.prettier4j.Doc;
import formatter.exceptions.AstVerificationException;
import formatter.exceptions.SanyFrontendException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import tla2sany.st.TreeNode;

import java.io.File;
import java.io.IOException;
import java.lang.invoke.MethodHandles;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public final class TLAPlusFormatter {
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    final TreeNode root;
    private final File spec;
    private final TlaDocBuilder docBuilder;
    private String output;
    private final FormatConfig config;
    private final boolean verifyAst;

    public TLAPlusFormatter(File specPath) throws IOException, SanyFrontendException {
        this(specPath, new FormatConfig(), true);
    }

    public TLAPlusFormatter(File specPath, FormatConfig config) throws IOException, SanyFrontendException {
        this(specPath, config, true);
    }

    public TLAPlusFormatter(File specPath, FormatConfig config, boolean verifyAst) throws IOException, SanyFrontendException {
        this.docBuilder = new TlaDocBuilder(config);
        this.config = config.copy();
        this.verifyAst = verifyAst;
        this.root = SANYWrapper.load(specPath);
        this.spec = specPath;

        format();
    }

    public String getOutput() {
        return output;
    }

    /**
     * Create a new instance of the formatter from a string containing the spec.
     * The spec is written to a temporary file, which is then passed to SANY.
     * The temporary file is deleted after the formatting is complete.
     * <p>
     * Safety: The input spec should be called "Spec" otherwise SANY will complain.
     *
     */
    public TLAPlusFormatter(String spec) throws IOException, SanyFrontendException {
        this(storeToTmp(spec), new FormatConfig(), true);
    }

    public TLAPlusFormatter(String spec, FormatConfig config) throws IOException, SanyFrontendException {
        this(storeToTmp(spec), config, true);
    }

    public TLAPlusFormatter(String spec, FormatConfig config, boolean verifyAst) throws IOException, SanyFrontendException {
        this(storeToTmp(spec), config, verifyAst);
    }

    private void format() throws IOException {
        String[] extraSections = getPreAndPostModuleSectionsFromSpecFile(spec.toPath());

        // Pass original source to docBuilder for spacing preservation
        String originalSource = Files.readString(spec.toPath());
        docBuilder.setOriginalSource(originalSource);

        Doc moduleDoc = docBuilder.build(root);
        this.output = extraSections[0] +
                moduleDoc.render(this.config.getLineWidth()) +
                extraSections[1];

        if (verifyAst) {
            verifyAstPreservation();
        }
    }

    /**
     * Re-parses the formatted output and compares its AST to the original.
     * Throws AstVerificationException if the ASTs differ.
     */
    private void verifyAstPreservation() throws IOException {
        File tmpFile = null;
        try {
            // Write to the same directory as the original spec so SANY can resolve EXTENDS
            tmpFile = storeForVerification(this.output, this.spec);
            TreeNode formattedRoot = SANYWrapper.load(tmpFile);
            AstComparator.Result result = AstComparator.compare(this.root, formattedRoot);
            if (!result.isMatch()) {
                throw new AstVerificationException(result);
            }
        } catch (SanyFrontendException e) {
            throw new AstVerificationException(new AstComparator.Result(
                    "Formatted output failed to parse: " + e.getMessage()));
        } finally {
            if (tmpFile != null && !tmpFile.delete()) {
                LOG.debug("Failed to delete temporary verification file: {}", tmpFile);
            }
        }
    }

    /**
     * Writes spec content to a temp directory with copies of sibling .tla files,
     * so that SANY can resolve EXTENDS to sibling modules.
     */
    private static File storeForVerification(String content, File originalSpec) throws IOException {
        File parentDir = originalSpec.getAbsoluteFile().getParentFile();
        File tmpDir = Files.createTempDirectory("sany-verify").toFile();
        tmpDir.deleteOnExit();
        // Copy sibling .tla files so SANY can resolve EXTENDS
        File[] siblings = parentDir.listFiles((dir, name) -> name.endsWith(".tla"));
        if (siblings != null) {
            for (File sibling : siblings) {
                var dest = new File(tmpDir, sibling.getName());
                Files.copy(
                        sibling.toPath(),
                        dest.toPath(),
                        java.nio.file.StandardCopyOption.REPLACE_EXISTING);
                dest.deleteOnExit();
            }
        }
        // Write the formatted output with the original filename (SANY requires module name = filename)
        File verifyFile = new File(tmpDir, originalSpec.getName());
        verifyFile.deleteOnExit();
        try (java.io.FileWriter writer = new java.io.FileWriter(verifyFile, StandardCharsets.UTF_8)) {
            writer.write(content);
        }
        return verifyFile;
    }

    static String getModuleName(String spec) {
        String regex = "----\\s?MODULE\\s+(\\w+)\\s?----";
        Pattern pattern = Pattern.compile(regex);
        Matcher matcher = pattern.matcher(spec);

        // Find the first match
        if (matcher.find()) {
            return matcher.group(1);
        } else {
            return "Spec";
        }
    }

    private static File storeToTmp(String spec) throws IOException {
        File tmpFolder = Files.createTempDirectory("sanyimp").toFile();
        tmpFolder.deleteOnExit();
        var fileName = getModuleName(spec) + ".tla";
        File tmpFile = new File(tmpFolder, fileName);
        try (java.io.FileWriter writer = new java.io.FileWriter(tmpFile, StandardCharsets.UTF_8)) {
            writer.write(spec);
        }
        tmpFile.deleteOnExit();
        return tmpFile;
    }

    private String[] getPreAndPostModuleSections(String spec, int startLine, int endLine) {
        String[] lines = spec.split("\\R"); // Split by any line terminator
        StringBuilder preModuleSection = new StringBuilder();
        StringBuilder postModuleSection = new StringBuilder();
        for (int i = 0; i < startLine - 1; i++) {
            preModuleSection.append(lines[i]).append(System.lineSeparator());
        }
        for (int i = endLine; i < lines.length; i++) {
            postModuleSection.append(System.lineSeparator()).append(lines[i]);
        }
        if (spec.endsWith("\n")) {
            postModuleSection.append(System.lineSeparator());
        }

        return new String[]{preModuleSection.toString(), postModuleSection.toString()};
    }

    private String[] getPreAndPostModuleSectionsFromSpecFile(Path spec) throws IOException {
        try {
            String content = Files.readString(spec);
            //read all the content of spec:
            var startOfModuleRow = root.zero()[0].getLocation().getCoordinates()[0];
            var endOfModuleRow = root.zero()[3].getLocation().getCoordinates()[0];
            return getPreAndPostModuleSections(content, startOfModuleRow, endOfModuleRow);
        } catch (IOException e) {
            LOG.error("Failed to read content of the spec to get pre and post module sections: {}", String.valueOf(e));
            throw e;
        }
    }


}
