// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Mon 30 Apr 2007 at 13:21:00 PST by lamport
//      modified on Fri Sep 22 13:18:45 PDT 2000 by yuanyu

package tlc2.value.impl;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.EvalControl;
import tlc2.tool.EvalException;
import tlc2.tool.FingerprintException;
import tlc2.tool.impl.Tool;
import tlc2.value.IValue;
import tlc2.value.Values;
import util.Assert;
import util.Assert.TLCRuntimeException;
import util.WrongInvocationException;

public class MethodValue extends OpValue implements Applicable {

	public static Value get(final Method md) {
		// Call from e.g. STRING (see tlc2.module.Strings.STRING()), which has no operator
		// definition.
		return get(md, 0);
	}
	
	public static Value get(final Method md, int minLevel) {
		final MethodValue mv = new MethodValue(md, minLevel);
		// Eagerly evaluate the constant operator if possible (zero arity) to only
		// evaluate once at startup and not during state exploration.
		final int acnt = md.getParameterTypes().length;
    	final boolean isConstant = (acnt == 0) && Modifier.isFinal(md.getModifiers());
    	return isConstant ? mv.apply(Tool.EmptyArgs, EvalControl.Clear) : mv;
	}
	
  private final MethodHandle mh;
  private final Method md;
  private final int minLevel;

  /* Constructor */
	private MethodValue(final Method md, final int minLevel) {
		this.md = md;
		this.minLevel = minLevel;
		try {
			final int parameterCount = this.md.getParameterCount();
			if (parameterCount > 0) {
				// With more than one argument, we want to setup the method handle to use a
				// spreader which essentially converts the Value[] into something that is
				// accepted by the method handle. Without a spreader, passing a Value[] to
				// MethodHandle#invoke does not work. Instead one has to use MethodHandle#invokeWithArguments.
				// MethodHandle#invokeWithArguments internally creates a spreader on the fly
				// which turns out to be costly (for the spec MongoRepl of the performance
				// tests it resulted in a 20% performance drop).
				this.mh = MethodHandles.publicLookup().unreflect(md).asSpreader(IValue[].class, parameterCount);
			} else {
				this.mh = MethodHandles.publicLookup().unreflect(md); 
			}
		} catch (IllegalAccessException e) {
			throw new TLCRuntimeException(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE, MP.getMessage(
					EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE, new String[] { md.toString(), e.getMessage() }));
		}
	}

  @Override
  public final byte getKind() { return METHODVALUE; }

  @Override
  public final IValue initialize() {
	  this.deepNormalize();
	  // Do not call fingerprint as a MethodValue has no fingerprint.
	  return this;
  }
  
  @Override
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

  @Override
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

  @Override
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

  @Override
  public final Value apply(Value arg, int control) {
    try {
      throw new WrongInvocationException("It is a TLC bug: Should use the other apply method.");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value apply(Value[] args, int control) {
    try {
      Value res = null;
      try
      {
    	  if (args.length == 0) {
    		  res = (Value) this.mh.invokeExact();
    	  } else {
    		  res = (Value) this.mh.invoke(args);
    	  }
      } catch (Throwable e)
      {
          if (e instanceof InvocationTargetException)
          {
              Throwable targetException = ((InvocationTargetException)e).getTargetException();
              throw new EvalException(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE, new String[]{this.md.toString(), targetException.getMessage()});
          } else if (e instanceof NullPointerException) {
              throw new EvalException(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE, new String[]{this.md.toString(), e.getMessage()});
          } else if (e instanceof EvalException) {
        	  // Do not wrap an EvalException below.
        	  throw (EvalException) e;
          } else
          {
              String message = e.getMessage();
              if (message == null) {
				  // Try to pass some information along (i.e. the full stack-trace) in cases where
				  // message is null.
		          final StringWriter sw = new StringWriter();
            	  e.printStackTrace(new PrintWriter(sw));
            	  message = sw.toString();
              }
			Assert.fail(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE, new String[]{this.md.toString(), message});
          }
      }
      return res;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value select(Value arg) {
    try {
      throw new WrongInvocationException("It is a TLC bug: Attempted to call MethodValue.select().");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
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

  @Override
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

  @Override
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

  @Override
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
  @Override
  public final boolean isNormalized() {
    try {
      throw new WrongInvocationException("It is a TLC bug: Attempted to normalize an operator.");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value normalize() {
    try {
      throw new WrongInvocationException("It is a TLC bug: Attempted to normalize an operator.");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean isDefined() { return true; }

  @Override
  public final IValue deepCopy() { return this; }

  @Override
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
  @Override
  public final StringBuffer toString(StringBuffer sb, int offset, boolean ignored) {
    try {
      return sb.append("<Java Method: " + this.md + ">");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }
  
  public final int getMinLevel() {
	  return minLevel;
  }
}
