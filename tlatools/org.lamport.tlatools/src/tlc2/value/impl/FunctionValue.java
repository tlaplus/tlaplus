// Copyright (c) 2023, Oracle and/or its affiliates.

package tlc2.value.impl;

import tlc2.tool.EvalControl;
import tlc2.tool.EvalException;

/**
 * Operations for values that behave like functions.
 *
 * <p>TODO: move some of the function operations from {@link Value} to this interface,
 *          such as {@link Value#takeExcept(ValueExcept)} and {@link Value#select(Value[])}.
 */
public interface FunctionValue extends Applicable {

  /**
   * Apply this function to multiple arguments.
   *
   * <p>All functions in TLA+ are unary.  When a function is applied to multiple arguments
   * as in <code>f[1, 2]</code>, it is just syntactic sugar for applying the function to a
   * tuple of those arguments (e.g. <code>f[&lt;&lt;1, 2&gt;&gt;]</code>).  Therefore, the
   * default implementation of this method calls {@link #apply(Value, int)} with <code>args</code>
   * wrapped in a {@link TupleValue}.  If <code>args.length == 1</code>, it does not create
   * a tuple and just passes <code>args[0]</code> instead.
   *
   * @param args the arguments
   * @param control the {@link EvalControl} mode
   * @return the apply result
   * @throws EvalException if evaluation fails
   * @throws util.Assert.TLCRuntimeException if the argument is not in the function's domain
   */
  @Override
  default Value apply(Value[] args, int control) throws EvalException {
    return args.length == 1
            ? apply(args[0], control)
            : apply(new TupleValue(args), control);
  }

  /**
   * Apply this function to an argument with the given {@link EvalControl}.
   *
   * @param arg the argument
   * @param control the {@link EvalControl} mode
   * @return the apply result
   * @throws EvalException if evaluation fails
   * @throws util.Assert.TLCRuntimeException if the argument is not in the function's domain
   */
  @Override
  Value apply(Value arg, int control) throws EvalException;

  /**
   * Compute the domain of this function.
   *
   * @return the domain of this function
   * @throws EvalException if evaluation fails
   */
  @Override
  Value getDomain() throws EvalException;

  /**
   * Apply this function to an argument.
   *
   * <p>This method is very similar to {@link #apply(Value, int)} but with two critical
   * differences:
   * <ol>
   *     <li>Evaluation control is assumed to be {@link EvalControl#Clear}</li>
   *     <li>Returns null instead of throwing an exception when the argument is not in the function's domain</li>
   * </ol>
   *
   * @param arg the argument
   * @return the apply result or null if the argument is not in this function's domain
   * @throws EvalException if evaluation fails
   */
  @Override
  Value select(Value arg) throws EvalException;

}
