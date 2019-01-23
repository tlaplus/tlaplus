// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Mon 30 Apr 2007 at 13:21:00 PST by lamport
//      modified on Fri Sep 22 13:18:45 PDT 2000 by yuanyu

package tlc2.value.impl;

import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.EvalException;
import tlc2.tool.FingerprintException;
import tlc2.value.IValue;
import tlc2.value.ValueExcept;
import tlc2.value.Values;
import util.Assert;
import util.Assert.TLCRuntimeException;
import util.WrongInvocationException;

public class MethodValue extends OpValue implements Applicable {
  private final MethodHandle mh;
  private final Method md;

  /* Constructor */
	public MethodValue(final Method md) {
		this.md = md;
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

  public final byte getKind() { return METHODVALUE; }

  public final int compareTo(Object obj) {
    try {
      Assert.fail("Attempted to compare operator " + this.toString() +
      " with value:\n" + obj == null ? "null" : Values.ppr(obj.toString()));
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
      " with value:\n" + obj == null ? "null" : Values.ppr(obj.toString()));
      return false;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean member(IValue elem) {
    try {
      Assert.fail("Attempted to check if the value:\n" + elem == null ? "null" : Values.ppr(elem.toString()) +
      "\nis an element of operator " + this.toString());
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
      " is a finite set.");
      return false;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final IValue apply(IValue arg, int control) {
    try {
      throw new WrongInvocationException("It is a TLC bug: Should use the other apply method.");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final IValue apply(IValue[] args, int control) {
    try {
      IValue res = null;
      try
      {
    	  if (args.length == 0) {
    		  res = (IValue) this.mh.invokeExact();
    	  } else {
    		  res = (IValue) this.mh.invoke(args);
    	  }
      } catch (Throwable e)
      {
          if (e instanceof InvocationTargetException)
          {
              Throwable targetException = ((InvocationTargetException)e).getTargetException();
              throw new EvalException(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE, new String[]{this.md.toString(), targetException.getMessage()});
          } else if (e instanceof NullPointerException) {
              throw new EvalException(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE, new String[]{this.md.toString(), e.getMessage()});
          } else
          {
              Assert.fail(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE, new String[]{this.md.toString(), e.getMessage()});
          }
      }
      return res;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final IValue select(IValue arg) {
    try {
      throw new WrongInvocationException("It is a TLC bug: Attempted to call MethodValue.select().");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final IValue takeExcept(ValueExcept ex) {
    try {
      Assert.fail("Attempted to appy EXCEPT construct to the operator " +
      this.toString() + ".");
      return null;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final IValue takeExcept(ValueExcept[] exs) {
    try {
      Assert.fail("Attempted to apply EXCEPT construct to the operator " +
      this.toString() + ".");
      return null;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final IValue getDomain() {
    try {
      Assert.fail("Attempted to compute the domain of the operator " +
      this.toString() + ".");
      return EmptySet;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final int size() {
    try {
      Assert.fail("Attempted to compute the number of elements in the operator " +
      this.toString() + ".");
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

  public final IValue normalize() {
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

  public final boolean assignable(IValue val) {
    try {
      throw new WrongInvocationException("It is a TLC bug: Attempted to initialize an operator.");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* String representation of the value.  */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    try {
      return sb.append("<Java Method: " + this.md + ">");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

}
