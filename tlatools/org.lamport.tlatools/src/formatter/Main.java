package formatter;

import formatter.exceptions.AstVerificationException;
import formatter.exceptions.SanyFrontendException;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;

public class Main {
    private static final Logger logger = Logger.getLogger(Main.class.getName());
    private static final String DEFAULT_VERBOSITY_OPTION = "INFO";

    private static void printHelp() {
        String header = "A TLA+ formatter. Use it to reformat your specs.";
        String footer = "Please contribute feedback or get the latest release from https://github.com/FedericoPonzi/tlaplus-formatter";
        System.err.println("usage: java -cp tla2tools.jar formatter.Main [OPTIONS] <FILE> [OUTFILE]");
        System.err.println(header);
        System.err.println();
        System.err.println("Options:");
        System.err.println("  -i, --indent <N>             Set the number of spaces for indentation (default: 4)");
        System.err.println("  -w, --width <N>              Set the target line width for formatting (default: 80)");
        System.err.println("  -v, --verbosity <LEVEL>      Set the verbosity level (ERROR, WARN, *INFO, DEBUG)");
        System.err.println("      --skip-ast-verification  Skip AST verification after formatting (not recommended,");
        System.err.println("                               verification is enabled by default)");
        System.err.println("  -h, --help                   Show this help message and exit");
        System.err.println();
        System.err.println(footer);
    }

    public static int mainWrapper(String[] args) {
        String verbosity = null;
        String widthStr = null;
        String indentStr = null;
        boolean skipAstVerification = false;
        List<String> positionalArgs = new ArrayList<>();

        // Manual argument parsing
        int i = 0;
        while (i < args.length) {
            String arg = args[i];
            if (arg.equals("-v") || arg.equals("--verbosity")) {
                if (i + 1 >= args.length) {
                    logger.severe("Error parsing command line arguments: Missing argument for option: " + arg);
                    printHelp();
                    return 1;
                }
                verbosity = args[++i];
            } else if (arg.equals("-w") || arg.equals("--width")) {
                if (i + 1 >= args.length) {
                    logger.severe("Error parsing command line arguments: Missing argument for option: " + arg);
                    printHelp();
                    return 1;
                }
                widthStr = args[++i];
            } else if (arg.equals("-i") || arg.equals("--indent")) {
                if (i + 1 >= args.length) {
                    logger.severe("Error parsing command line arguments: Missing argument for option: " + arg);
                    printHelp();
                    return 1;
                }
                indentStr = args[++i];
            } else if (arg.equals("--skip-ast-verification")) {
                skipAstVerification = true;
            } else if (arg.equals("-h") || arg.equals("--help")) {
                printHelp();
                return 0;
            } else if (arg.startsWith("-")) {
                logger.severe("Error parsing command line arguments: Unrecognized option: " + arg);
                printHelp();
                return 1;
            } else {
                positionalArgs.add(arg);
            }
            i++;
        }

        try {
            setLogLevel(DEFAULT_VERBOSITY_OPTION);

            if (verbosity != null) {
                String verbosityUpper = verbosity.toUpperCase();
                try {
                    setLogLevel(verbosityUpper);
                } catch (IllegalArgumentException e) {
                    logger.severe("Invalid log level: " + verbosityUpper);
                    printHelp();
                    return 1;
                }
            }

            // Parse formatting options
            int lineWidth = FormatConfig.DEFAULT_LINE_WIDTH;
            int indentSize = FormatConfig.DEFAULT_INDENT_SIZE;

            if (widthStr != null) {
                try {
                    lineWidth = Integer.parseInt(widthStr);
                } catch (NumberFormatException e) {
                    logger.severe("Invalid line width: " + widthStr);
                    printHelp();
                    return 1;
                }
            }

            if (indentStr != null) {
                try {
                    indentSize = Integer.parseInt(indentStr);
                } catch (NumberFormatException e) {
                    logger.severe("Invalid indent size: " + indentStr);
                    printHelp();
                    return 1;
                }
            }

            if (positionalArgs.isEmpty() || positionalArgs.size() > 2) {
                logger.severe("Please provide one or two file paths (input and optionally output) as arguments.");
                printHelp();
                return 1;
            }

            File inputFile = new File(positionalArgs.get(0));
            if (!inputFile.exists()) {
                logger.severe("Input file does not exist: " + inputFile.getAbsolutePath());
                return 1;
            }

            FormatConfig config = new FormatConfig(lineWidth, indentSize);
            boolean verifyAst = !skipAstVerification;
            TLAPlusFormatter formatter;
            try {
                formatter = new TLAPlusFormatter(inputFile, config, verifyAst);
            } catch (AstVerificationException e) {
                // AST verification failed: print original input to stdout, diagnostics to stderr
                System.out.print(Files.readString(inputFile.toPath()));
                System.err.println("AST verification failed after formatting.");
                System.err.println(e.getResult().formatDiagnostic());
                System.err.println("This is a bug in the formatter. Please report it at:");
                System.err.println("  https://github.com/FedericoPonzi/tlaplus-formatter/issues");
                return 1;
            }
            String formattedOutput = formatter.getOutput();

            if (positionalArgs.size() == 2) {
                File outputFile = new File(positionalArgs.get(1));
                Files.writeString(outputFile.toPath(), formattedOutput);
                logger.info("Formatted output written to: " + outputFile.getAbsolutePath());
            } else {
                System.out.println(formattedOutput);
            }

        } catch (IOException | SanyFrontendException e) {
            logger.severe("An error occurred while processing the file: " + e.getMessage());
            return 1;
        }
        return 0;
    }

    public static void main(String[] args) {
        System.exit(mainWrapper(args));
    }

    private static void setLogLevel(String levelStr) {
        Level level;
        switch (levelStr.toUpperCase()) {
            case "ERROR":
                level = Level.SEVERE;
                break;
            case "WARN":
                level = Level.WARNING;
                break;
            case "INFO":
                level = Level.INFO;
                break;
            case "DEBUG":
                level = Level.FINE;
                break;
            default:
                throw new IllegalArgumentException("Unknown log level: " + levelStr);
        }
        Logger rootLogger = Logger.getLogger("formatter");
        rootLogger.setLevel(level);
        logger.fine("Log level set to " + level);
    }
}