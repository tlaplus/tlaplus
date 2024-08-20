// Copyright (c) 2024, Oracle and/or its affiliates.

package tlc2.repl;

import tlc2.REPL;

import java.io.PrintStream;

/**
 * Command that does nothing.
 */
public class NoOpCommand implements Command {
    @Override
    public void apply(REPL replState, PrintStream out) {
    }
}
