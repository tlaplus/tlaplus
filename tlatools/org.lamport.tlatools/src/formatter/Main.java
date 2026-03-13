package formatter;

import ch.qos.logback.classic.LoggerContext;
import formatter.exceptions.AstVerificationException;
import formatter.exceptions.SanyFrontendException;
import org.apache.commons.cli.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.io.IOException;
import java.lang.invoke.MethodHandles;
import java.nio.file.Files;

public class Main {
    private static final Logger logger = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());
    private static final String VERBOSITY_OPTION = "v";
    private static final String DEFAULT_VERBOSITY_OPTION = "INFO";
    private static void printHelp(Options options) {
        HelpFormatter formatter = new HelpFormatter();
        String header = "A TLA+ formatter. Use it to reformat your specs.";
        String footer = "Please contribute feedback or get the latest release from https://github.com/FedericoPonzi/tlaplus-formatter";
        formatter.printHelp("java -jar tlaplus-formatter.jar [OPTIONS] <FILE> [OUTFILE]", header, options, footer, true);
    }

    public static int mainWrapper(String[] args) {
        Options options = new Options();
        options.addOption(VERBOSITY_OPTION, "verbosity", true, "Set the verbosity level (ERROR, WARN, *INFO, DEBUG)");
        options.addOption("w", "width", true, "Set the target line width for formatting (default: 80)");
        options.addOption("i", "indent", true, "Set the number of spaces for indentation (default: 4)");
        options.addOption(null, "skip-ast-verification", false,
                "Skip AST verification after formatting (not recommended, verification is enabled by default)");

        CommandLine cmd;
        try {
            // Parse the command-line arguments
            CommandLineParser parser = new DefaultParser();
            cmd = parser.parse(options, args);

            // Set the default log level to INFO
            setLogLevel(DEFAULT_VERBOSITY_OPTION);

            // Set the log level based on the verbosity option
            if (cmd.hasOption(VERBOSITY_OPTION)) {
                String verbosity = cmd.getOptionValue(VERBOSITY_OPTION).toUpperCase();
                try {
                    setLogLevel(verbosity);
                } catch (IllegalArgumentException e) {
                    logger.error("Invalid log level: {}", verbosity);
                    printHelp(options);
                    return 1;
                }
            }
            
            // Parse formatting options
            int lineWidth = FormatConfig.DEFAULT_LINE_WIDTH;
            int indentSize = FormatConfig.DEFAULT_INDENT_SIZE;
            
            if (cmd.hasOption("w")) {
                try {
                    lineWidth = Integer.parseInt(cmd.getOptionValue("w"));
                } catch (NumberFormatException e) {
                    logger.error("Invalid line width: {}", cmd.getOptionValue("w"));
                    printHelp(options);
                    return 1;
                }
            }
            
            if (cmd.hasOption("i")) {
                try {
                    indentSize = Integer.parseInt(cmd.getOptionValue("i"));
                } catch (NumberFormatException e) {
                    logger.error("Invalid indent size: {}", cmd.getOptionValue("i"));
                    printHelp(options);
                    return 1;
                }
            }

            // Get the remaining arguments (positional arguments)
            String[] remainingArgs = cmd.getArgs();

            if (remainingArgs.length == 0 || remainingArgs.length > 2) {
                logger.error("Please provide one or two file paths (input and optionally output) as arguments.");
                printHelp(options);
                return 1;
            }

            // Get the input file path from the positional arguments
            File inputFile = new File(remainingArgs[0]);
            if (!inputFile.exists()) {
                logger.error("Input file does not exist: {}", inputFile.getAbsolutePath());
                return 1;
            }

            FormatConfig config = new FormatConfig(lineWidth, indentSize);
            boolean verifyAst = !cmd.hasOption("skip-ast-verification");
            TLAPlusFormatter formatter;
            try {
                formatter = new TLAPlusFormatter(inputFile, config, verifyAst);
            } catch (AstVerificationException e) {
                // AST verification failed: print original input to stdout, diagnostics to stderr
                System.out.print(Files.readString(inputFile.toPath()));
                System.err.println("AST verification failed after formatting.");
                System.err.println("tlaplus-formatter version: " + VersionInfo.getFullVersion());
                System.err.println(e.getResult().formatDiagnostic());
                System.err.println("This is a bug in the formatter. Please report it at:");
                System.err.println("  https://github.com/FedericoPonzi/tlaplus-formatter/issues");
                return 1;
            }
            String formattedOutput = formatter.getOutput();

            if (remainingArgs.length == 2) {
                // If output file is specified, write to the file
                File outputFile = new File(remainingArgs[1]);
                Files.writeString(outputFile.toPath(), formattedOutput);
                logger.info("Formatted output written to: {}", outputFile.getAbsolutePath());
            } else {
                // If no output file is specified, print to stdout
                System.out.println(formattedOutput);
            }

        } catch (ParseException e) {
            logger.error("Error parsing command line arguments: {}", e.getMessage());
            printHelp(options);
            return 1;
        } catch (IOException | SanyFrontendException e) {
            logger.error("An error occurred while processing the file: {}", e.getMessage());
            return 1;
        }
        return 0;
    }

    public static void main(String[] args) {
        System.exit(mainWrapper(args));
    }

    private static void setLogLevel(String levelStr) {
        LoggerContext context = (LoggerContext) LoggerFactory.getILoggerFactory();
        ch.qos.logback.classic.Level level = ch.qos.logback.classic.Level.toLevel(levelStr, ch.qos.logback.classic.Level.INFO);
        context.getLogger("root").setLevel(level);
        logger.debug("Log level set to {}", level);
    }
}