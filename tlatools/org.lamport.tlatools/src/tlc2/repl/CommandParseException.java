// Copyright (c) 2024, Oracle and/or its affiliates.

package tlc2.repl;

/**
 * Thrown when a {@link Command} cannot be parsed.
 *
 * @see Command#parse(String)
 */
public class CommandParseException extends Exception {
    public CommandParseException(String message) {
        super(message);
    }
}
