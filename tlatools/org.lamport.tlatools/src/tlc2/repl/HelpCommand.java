// Copyright (c) 2024, Oracle and/or its affiliates.

package tlc2.repl;

import tlc2.REPL;

import java.io.PrintStream;

/**
 * Command to show REPL help.
 */
public class HelpCommand implements Command {

    @Override
    public void apply(REPL replState, PrintStream out) {
        out.println("---- REPL HELP ----");
        out.println("  :help");
        out.println("           show this help");
        out.println("  <expr>");
        out.println("           evaluate a TLA+ expression");
        out.println("===================");
    }

}
