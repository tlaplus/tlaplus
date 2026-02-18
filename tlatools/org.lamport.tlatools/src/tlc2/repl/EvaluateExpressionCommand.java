// Copyright (c) 2024, Oracle and/or its affiliates.

package tlc2.repl;

import tlc2.REPL;

import java.io.PrintStream;

/**
 * Command to evaluate an expression and print the result.
 */
public class EvaluateExpressionCommand implements Command {

    private final String expression;

    public EvaluateExpressionCommand(String expression) {
        this.expression = expression;
    }

    public String getExpression() {
        return expression;
    }

    @Override
    public void apply(REPL replState, PrintStream out) {
        String res = replState.processInput(expression);
        if (!res.isEmpty()) {
            out.println(res);
        }
    }

}
