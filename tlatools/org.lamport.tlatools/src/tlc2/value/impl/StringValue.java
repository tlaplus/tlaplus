// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Sat 23 February 2008 at 10:19:41 PST by lamport
//      modified on Fri Aug 10 15:06:37 PDT 2001 by yuanyu

package tlc2.value.impl;

import java.io.IOException;
import java.util.Map;
import java.util.Random;

import tlc2.tool.FingerprintException;
import tlc2.tool.coverage.CostModel;
import tlc2.util.FP64;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import tlc2.value.IValueInputStream;
import tlc2.value.IValueOutputStream;
import tlc2.value.Values;
import util.Assert;
import util.UniqueString;

public class StringValue extends Value {
  public final UniqueString val;

  /* Constructor */
  public StringValue(String str) {
    // SZ 11.04.2009: changed the access method to equivalent
    this.val = UniqueString.uniqueStringOf(str);
  }

  public StringValue(UniqueString var) {
    this.val = var;
  }

  public StringValue(UniqueString var, CostModel cm) {
	  this(var);
	  this.cm = cm;
  }

  @Override
  public final byte getKind() { return STRINGVALUE; }

  public final UniqueString getVal() { return this.val; }

  @Override
  public final int compareTo(Object obj) {
    try {
      if (obj instanceof StringValue) {
        return this.val.compareTo(((StringValue)obj).val);
      }
      if (!(obj instanceof ModelValue)) {
        Assert.fail("Attempted to compare string " + Values.ppr(this.toString()) +
        " with non-string:\n" + Values.ppr(obj.toString()), getSource());
      }
      return ((ModelValue) obj).modelValueCompareTo(this);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean equals(Object obj) {
    try {
      if (obj instanceof StringValue) {
        return this.val.equals(((StringValue)obj).getVal());
      }
      if (!(obj instanceof ModelValue)) {
        Assert.fail("Attempted to check equality of string " + Values.ppr(this.toString()) +
        " with non-string:\n" + Values.ppr(obj.toString()), getSource());
      }
      return ((ModelValue) obj).modelValueEquals(this) ;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean member(Value elem) {
    try {
      Assert.fail("Attempted to check if the value:\n" + Values.ppr(elem.toString()) +
      "\nis an element of the string " + Values.ppr(this.toString()), getSource());
      return false;     // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean isFinite() {
    try {
      Assert.fail("Attempted to check if the string " + Values.ppr(this.toString()) +
      " is a finite set.", getSource());
      return false;     // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value takeExcept(ValueExcept ex) {
    try {
      if (ex.idx < ex.path.length) {
        Assert.fail("Attempted to apply EXCEPT construct to the string " +
        Values.ppr(this.toString()) + ".", getSource());
      }
      return ex.value;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value takeExcept(ValueExcept[] exs) {
    try {
      if (exs.length != 0) {
        Assert.fail("Attempted to apply EXCEPT construct to the string " +
        Values.ppr(this.toString()) + ".", getSource());
      }
      return this;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final int size() {
    try {
      Assert.fail("Attempted to compute the number of elements in the string " +
      Values.ppr(this.toString()) + ".", getSource());
      return 0;       // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public boolean mutates() {
	  // finalized after construction.
	  return false;
  }

  @Override
  public final boolean isNormalized() { return true; }

  @Override
  public final Value normalize() { /*SKIP*/return this; }

  @Override
  public final boolean isDefined() { return true; }

  @Override
  public final IValue deepCopy() { return this; }

  @Override
  public final boolean assignable(Value val) {
    try {
      return ((val instanceof StringValue) &&
        this.equals(val));
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final int length() {
    try {
      return this.val.length();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

	@Override
	public void write(IValueOutputStream vos) throws IOException {
		final int index = vos.put(this);
		if (index == -1) {
			vos.writeByte(STRINGVALUE);
			val.write(vos.getOutputStream());
		} else {
			vos.writeByte(DUMMYVALUE);
			vos.writeNat(index);
		}
	}

  /* The fingerprint method */
  @Override
  public final long fingerPrint(long fp) {
    try {
      fp = FP64.Extend(fp, STRINGVALUE) ;
      fp = FP64.Extend(fp, this.val.length()) ;
      fp = FP64.Extend(fp, this.val.toString());
      return fp;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final IValue permute(IMVPerm perm) { return this; }

  /*************************************************************************
  * toString() modified 23 Aug 2007 by LL to call PrintVersion so strings  *
  * with special characters are printed properly.                          *
  *************************************************************************/
  final String PrintVersion(String str) {
    try {
      StringBuffer buf = new StringBuffer(str.length()) ;
      for (int i = 0 ; i < str.length() ; i++) {
        switch (str.charAt(i)) {
          case '\"' :
            buf.append("\\\"") ;
            break ;
          case '\\' :
            buf.append("\\\\") ;
            break ;
          case '\t' :
            buf.append("\\t") ;
            break ;
          case '\n' :
            buf.append("\\n") ;
            break ;
          case '\f' :
            buf.append("\\f") ;
            break ;
          case '\r' :
            buf.append("\\r") ;
            break ;
          default :
            buf.append(str.charAt(i)) ;
            break ;
         } // switch
       }// for
      return buf.toString();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
   }

  	@Override
	public TLCVariable toTLCVariable(final TLCVariable variable, Random rnd) {
		final TLCVariable stringVar = super.toTLCVariable(variable, rnd);
		// Replace the quoted string from super.toTLCVariable(..) with an unquoted one.
		// In the variable view of the debugger, we don't want quotes.
		stringVar.setValue(toUnquotedString());
		return stringVar;
	}

  /* The string representation of the value. */
  @Override
  public StringBuffer toString(StringBuffer sb, int offset, boolean swallow) {
    try {
      return sb.append("\"" + PrintVersion(this.val.toString()) + "\"");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* Same as toString. */
  @Override
  public final String toUnquotedString() {
	  return PrintVersion(this.val.toString());
  }

	public static IValue createFrom(final IValueInputStream vos) throws IOException {
		final UniqueString str = UniqueString.read(vos.getInputStream());
		final IValue res = new StringValue(str);
		final int index = vos.getIndex();
		vos.assign(res, index);
		return res;
	}
	
	public static IValue createFrom(final IValueInputStream vos, final Map<String, UniqueString> tbl) throws IOException {
		final UniqueString str = UniqueString.read(vos.getInputStream(), tbl);
		final IValue res = new StringValue(str);
		final int index = vos.getIndex();
		vos.assign(res, index);
		return res;
	}
}
