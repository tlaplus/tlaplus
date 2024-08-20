// Copyright (c) 2024, Oracle and/or its affiliates.

package tlc2.repl;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Helper class for {@link Command#parse(String)}.
 */
class CommandParser {

    private static final String COMMAND_PREFIX = ":";
    private static final Pattern COMMAND_PATTERN = Pattern.compile("^\\s*(" + Pattern.quote(COMMAND_PREFIX) + "\\w+)\\s*(.*?)\\s*$");

    public static Command parse(String line) throws CommandParseException {
        if (line.isBlank()) {
            return new NoOpCommand();
        }

        Matcher matcher = COMMAND_PATTERN.matcher(line);
        if (matcher.matches()) {
            switch (matcher.group(1)) {
                case ":help":
                    if (matcher.group(2).isBlank()) {
                        return new HelpCommand();
                    } else {
                        throw new CommandParseException("Junk input after help command: '" + matcher.group(2) + '\'');
                    }
                default:
                    throw new CommandParseException("Unknown command '" + matcher.group(1) + '\'');
            }
        } else {
            return new EvaluateExpressionCommand(line);
        }
    }

}
