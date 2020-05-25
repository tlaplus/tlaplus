package tlc2;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;

import org.jline.reader.EndOfFileException;
import org.jline.reader.LineReader;
import org.jline.reader.LineReaderBuilder;
import org.jline.reader.UserInterruptException;
import org.jline.reader.impl.DefaultParser;
import org.jline.terminal.Terminal;
import org.jline.terminal.TerminalBuilder;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.EvalException;
import tlc2.tool.TLCState;
import tlc2.tool.impl.FastTool;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.impl.Value;
import util.Assert;
import util.SimpleFilenameToStream;
import util.TLAConstants;
import util.ToolIO;


/**
 * A TLA+ REPL which provides an interactive mode of evaluating expressions and specifications.
 */
public class REPL {

    // The spec file to use in the REPL context, if any.
    private File specFile = null;

    // The naming prefix of the temporary directory.
    static final String TEMP_DIR_PREFIX = "tlarepl";

    // The name of the spec used for evaluating expressions.
    final String REPL_SPEC_NAME = "tlarepl";

    // A temporary directory to place auxiliary files needed for REPL evaluation.
    Path replTempDir;

    public REPL(Path tempDir) {
        replTempDir = tempDir;
    }

    public void setSpecFile(final File pSpecFile) {
        specFile = pSpecFile;
    }

    /**
     * Evaluate the given string input as a TLA+ expression.
     *
     * @return the pretty printed result of the evaluation or an empty string if there was an error.
     */
    public String processInput(String evalExpr) {

        // The modules we will extend in the REPL environment.
        String moduleExtends = "Reals,Sequences,Bags,FiniteSets,TLC,Randomization";
        if (specFile != null) {
            String mainModuleName = specFile.getName().replaceFirst(TLAConstants.Files.TLA_EXTENSION + "$", "");
            moduleExtends += ("," + mainModuleName);
        }

        File tempFile, configFile;
        try {

            // We want to place the spec files used by REPL evaluation into the temporary directory.
            tempFile = new File(replTempDir.toString(), REPL_SPEC_NAME + TLAConstants.Files.TLA_EXTENSION);
            configFile = new File(replTempDir.toString(), REPL_SPEC_NAME + TLAConstants.Files.CONFIG_EXTENSION);

            // Create the config file.
            BufferedWriter cfgWriter = new BufferedWriter(new FileWriter(configFile.getAbsolutePath(), false));
            cfgWriter.append("INIT replinit");
            cfgWriter.newLine();
            cfgWriter.append("NEXT replnext");
            cfgWriter.newLine();
            cfgWriter.close();

            // Create the spec file lines.
            ArrayList<String> lines = new ArrayList<String>();
            String replValueVarName = "replvalue";
            lines.add("---- MODULE tlarepl ----");
            lines.add("EXTENDS " + moduleExtends);
            lines.add("VARIABLE replvar");
            // Dummy Init and Next predicates.
            lines.add("replinit == replvar = 0");
            lines.add("replnext == replvar' = 0");
            // The expression to evaluate.
            lines.add(replValueVarName + " == " + evalExpr);
            lines.add("====");

            // Write out the spec file.
            BufferedWriter writer = new BufferedWriter(new FileWriter(tempFile.getAbsolutePath(), false));
            for (String line : lines) {
                writer.append(line);
                writer.newLine();
            }
            writer.close();

            // Avoid sending log messages to stdout and reset the messages recording.
            ToolIO.setMode(ToolIO.TOOL);
            ToolIO.reset();

            try {
                // We placed the REPL spec files into a temporary directory, so, we add this temp directory
                // path to the filename resolver used by the Tool.
                SimpleFilenameToStream resolver = new SimpleFilenameToStream(replTempDir.toAbsolutePath().toString());
                Tool tool = new FastTool(REPL_SPEC_NAME, REPL_SPEC_NAME, resolver);
                ModuleNode module = tool.getSpecProcessor().getRootModule();
                OpDefNode valueNode = module.getOpDef(replValueVarName);
                Value exprVal = (Value) tool.eval(valueNode.getBody(), Context.Empty, TLCState.Empty);
                return exprVal.toString();
            } catch (Assert.TLCRuntimeException | EvalException exc) {
                // TODO: Improve error messages with more specific detail.
                System.out.println("Error evaluating expression: '" + evalExpr + "'");
            }

        } catch (IOException pe) {
            pe.printStackTrace();
        }
        return "";
    }

    /**
     * Runs the main REPL loop continuously until there is a fatal error or a user interrupt.
     */
    public void runREPL() throws IOException {
        // For TLA+ we don't want to treat backslashes as escape chars e.g. for LaTeX like operators.
        DefaultParser parser = new DefaultParser();
        parser.setEscapeChars(null);
        Terminal terminal = TerminalBuilder.builder().build();
        LineReader reader = LineReaderBuilder.builder().parser(parser).terminal(terminal).build();

        // Run the loop.
        String prompt = "(tla+) ";
        String expr;
        while (true) {
            try {
                expr = reader.readLine(prompt);
                String res = processInput(expr);
                if (res.equals("")) {
                    continue;
                }
                System.out.println(res);
            } catch (UserInterruptException e) {
                return;
            } catch (EndOfFileException e) {
                e.printStackTrace();
                return;
            }
        }
    }

    public static void main(String[] args) {
        try {
            Path tempDir = Files.createTempDirectory(TEMP_DIR_PREFIX);
            REPL repl = new REPL(tempDir);
            // TODO: Allow external spec file to be loaded into REPL context.
            System.out.println("Welcome to the TLA+ REPL!");
            MP.printMessage(EC.TLC_VERSION, TLCGlobals.versionOfTLC);
            System.out.println("Enter a constant-level TLA+ expression.");
            repl.runREPL();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}
