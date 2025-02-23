// Copyright (c) 2024, Oracle and/or its affiliates.

package tlc2.repl;

import tlc2.REPL;

import java.io.PrintStream;

/**
 * A parsed command for the {@link REPL}.
 */
public interface Command {

    /**
     * Apply this command to the state of the REPL.
     *
     * @param replState the REPL state to modify
     * @param out where to write the output of the command, if any
     */
    void apply(REPL replState, PrintStream out);

    /**
     * Parse a command.
     *
     * @param line the input
     * @return a parsed command
     * @throws CommandParseException if the input was not a well-formed command
     */
    public static Command parse(String line) throws CommandParseException {
        return CommandParser.parse(line);
    }

}
