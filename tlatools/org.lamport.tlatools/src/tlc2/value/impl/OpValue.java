// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Copyright (c) 2023, Oracle and/or its affiliates.
// Last modified on Mon 30 Apr 2007 at 13:21:02 PST by lamport
//      modified on Fri Sep 22 13:18:45 PDT 2000 by yuanyu

package tlc2.value.impl;

import tla2sany.semantic.ExprOrOpArgNode;
import tlc2.tool.EvalException;
import tlc2.tool.FingerprintException;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import util.Assert;
import util.WrongInvocationException;

/**
 * Operations for values that behave like operators.
 *
 * <p>Operators are not really values in TLA+, but TLC needs to be able to represent operators
 * to support operators that take higher-order operators as arguments.  To give an artificial
 * example:
 *
 * <pre>
 *     F(G(_, _), x) == G(x, x)
 *     Eq(x, y) == x = y
 *     Init == F(Eq, 1)
 * </pre>
 *
 * The argument <code>Eq</code> will be represented as an <code>OpValue</code> when TLC evaluates
 * the <code>Init</code> predicate.
 */
public abstract class OpValue extends Value implements Applicable {

    /**
     * Apply this operator to arguments.
     *
     * <p>Implementations will typically begin by evaluating each of the given <code>args</code>,
     * but that is not a firm requirement.  For instance, an implementation may optimize by skipping
     * evaluation of some arguments if their values are not needed.
     *
     * @param tool the evaluation tool
     * @param args the arguments
     * @param c the context
     * @param s0 the current state
     * @param s1 the next state (null when evaluating invariants or the initial predicate)
     * @param control the {@link tlc2.tool.EvalControl} mode
     * @param cm the current cost model (or null)
     * @return the result of evaluation
     */
    public Value eval(final Tool tool, final ExprOrOpArgNode[] args, final Context c, final TLCState s0,
                      final TLCState s1, final int control, final CostModel cm) {
        if (args.length == 0) {
            return eval(Tool.EmptyArgs, control);
        }

        final Value[] argVals = new Value[args.length];
        // evaluate the operator's arguments:
        for (int i = 0; i < args.length; i++) {
            argVals[i] = tool.eval(args[i], c, s0, s1, control, cm);
        }
        return eval(argVals, control);
    }

    /**
     * Apply this operator to already-evaluated arguments.
     *
     * @param args the arguments
     * @param control the {@link tlc2.tool.EvalControl} mode
     * @return the result of evaluation
     */
    public abstract Value eval(Value[] args, int control);

    /**
     * @deprecated use {@link #eval(Value[], int)}; this override will vanish when {@link Applicable} is removed
     */
    @Deprecated
    @Override
    public Value apply(Value[] args, int control) throws EvalException {
        return eval(args, control);
    }

    /**
     * @deprecated use {@link #eval(Value[], int)}; this override will vanish when {@link Applicable} is removed
     */
    @Deprecated
    @Override
    public Value apply(Value arg, int control) throws EvalException {
        return eval(new Value[] { arg }, control);
    }

    /**
     * @deprecated
     *   Operators do not have a domain; all implementations of this method throw an exception.  If you
     *   meant to use this as a function, use {@link FunctionValue} instead.
     */
    @Deprecated
    @Override
    public Value getDomain() throws EvalException {
        try {
            Assert.fail("Attempted to compute the domain of the operator " + this + ".", getSource());
            return SetEnumValue.EmptySet;   // make compiler happy
        } catch (RuntimeException | OutOfMemoryError e) {
            if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
            else { throw e; }
        }
    }

    /**
     * @deprecated
     *   Operators do not have a domain; all implementations of this method throw an exception.  If you
     *   meant to use this as a function, use {@link FunctionValue} instead.
     */
    @Deprecated
    @Override
    public Value select(Value arg) throws EvalException {
        // NOTE 2023/11/8: Yes, this is meant to be a convenience override for apply(), and there is an
        // obvious default implementation.  However, prior to the OpValue/FunctionValue split, ALL
        // operator-ish implementations of this method threw an exception, so we should preserve that
        // behavior to discourage use of this method.
        try {
            throw new WrongInvocationException("It is a TLC bug: Attempted to call OpValue.select().");
        } catch (RuntimeException | OutOfMemoryError e) {
            if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
            else { throw e; }
        }
    }

}
