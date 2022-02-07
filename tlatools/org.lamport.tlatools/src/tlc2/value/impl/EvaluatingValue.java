/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tlc2.value.impl;

import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.reflect.Method;

import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.OpDefNode;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.BuiltInOPs;
import tlc2.tool.FingerprintException;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.IValue;
import tlc2.value.Values;
import util.Assert;
import util.Assert.TLCRuntimeException;
import util.WrongInvocationException;

public class EvaluatingValue extends OpValue implements Applicable {
  protected final MethodHandle mh;
  protected final Method md;
  protected final int minLevel;
  protected final int priority;
  protected final OpDefNode opDef;

  protected EvaluatingValue(final MethodHandle mh, final Method md, final int minLevel, final int priority, final OpDefNode opDef) {
	  this.mh = mh;
	  this.md = md;
	  this.minLevel = minLevel;
      this.priority = priority;
	  this.opDef = opDef;
  }
  
  /* Constructor */
	public EvaluatingValue(final Method md, final int minLevel, final int priority, final OpDefNode opDef) {
		this.md = md;
		this.minLevel = minLevel;
		this.priority = priority;
		this.opDef = opDef;
		if (BuiltInOPs.getOpCode(opDef.getName()) != 0) {
			Assert.fail(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE, new String[] { this.md.toString(),
					"@Evaluation fallback to pure TLA+ definition only works for user-defined operators." });
		}
		try {
			this.mh = MethodHandles.publicLookup().unreflect(md).asFixedArity();
		} catch (IllegalAccessException e) {
			throw new TLCRuntimeException(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE, MP.getMessage(
					EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE, new String[] { md.toString(), e.getMessage() }));
		}
	}

	@Override
	public Value eval(final Tool tool, final ExprOrOpArgNode[] args, final Context c, final TLCState s0,
			final TLCState s1, final int control, final CostModel cm) {
		try {
			final Object invoke = this.mh.invoke(tool, args, c, s0, s1, control, cm);
			if (invoke == null) {
				// Fall back to pure (TLA+) operator definition if the Java module override returned null.
				return tool.evalPure(opDef, args, c, s0, s1, control, cm);
			}
			return (Value) invoke;
		} catch (Throwable e) {
            Assert.fail(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE, new String[]{this.md.toString(), e.getMessage()});
            return null; // make compiler happy
		}
	}

  public final byte getKind() { return METHODVALUE; }

  public final int compareTo(Object obj) {
    try {
      Assert.fail("Attempted to compare operator " + this.toString() +
      " with value:\n" + obj == null ? "null" : Values.ppr(obj.toString()), getSource());
      return 0;       // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean equals(Object obj) {
    try {
      Assert.fail("Attempted to check equality of operator " + this.toString() +
      " with value:\n" + obj == null ? "null" : Values.ppr(obj.toString()), getSource());
      return false;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean member(Value elem) {
    try {
      Assert.fail("Attempted to check if the value:\n" + elem == null ? "null" : Values.ppr(elem.toString()) +
      "\nis an element of operator " + this.toString(), getSource());
      return false;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean isFinite() {
    try {
      Assert.fail("Attempted to check if the operator " + this.toString() +
      " is a finite set.", getSource());
      return false;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value apply(Value arg, int control) {
    try {
      throw new WrongInvocationException("It is a TLC bug: Should use the other apply method.");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value apply(Value[] args, int control) {
	    try {
	        throw new WrongInvocationException("It is a TLC bug: Should use the other apply method.");
	      }
	      catch (RuntimeException | OutOfMemoryError e) {
	        if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
	        else { throw e; }
	      }
  }

  public final Value select(Value arg) {
    try {
      throw new WrongInvocationException("It is a TLC bug: Attempted to call MethodValue.select().");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value takeExcept(ValueExcept ex) {
    try {
      Assert.fail("Attempted to appy EXCEPT construct to the operator " +
      this.toString() + ".", getSource());
      return null;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value takeExcept(ValueExcept[] exs) {
    try {
      Assert.fail("Attempted to apply EXCEPT construct to the operator " +
      this.toString() + ".", getSource());
      return null;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value getDomain() {
    try {
      Assert.fail("Attempted to compute the domain of the operator " +
      this.toString() + ".", getSource());
      return SetEnumValue.EmptySet;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final int size() {
    try {
      Assert.fail("Attempted to compute the number of elements in the operator " +
      this.toString() + ".", getSource());
      return 0;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* Should never normalize an operator. */
  public final boolean isNormalized() {
    try {
      throw new WrongInvocationException("It is a TLC bug: Attempted to normalize an operator.");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value normalize() {
    try {
      throw new WrongInvocationException("It is a TLC bug: Attempted to normalize an operator.");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean isDefined() { return true; }

  public final IValue deepCopy() { return this; }

  public final boolean assignable(Value val) {
    try {
      throw new WrongInvocationException("It is a TLC bug: Attempted to initialize an operator.");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* String representation of the value.  */
  public final StringBuffer toString(StringBuffer sb, int offset, boolean ignored) {
    try {
      return sb.append("<Java Method: " + this.md + ">");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public int getMinLevel() {
	  return minLevel;
  }

  public OpDefNode getOpDef() {
	  return this.opDef;
  }
}
