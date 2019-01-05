// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Mon 30 Apr 2007 at 15:30:13 PST by lamport
//      modified on Wed Dec  5 23:18:07 PST 2001 by yuanyu

package tlc2.value;

import java.io.IOException;
import java.io.Serializable;

import tla2sany.semantic.SemanticNode;
import tlc2.TLCGlobals;
import tlc2.pprint.PrettyPrint;
import tlc2.tool.FingerprintException;
import tlc2.util.FP64;
import util.Assert;
import util.WrongInvocationException;

public abstract class Value implements ValueConstants, Serializable {
  /**
   * For each kind of value, we introduce a subclass of Value.
   * All the subclasses are given in this value package.
   */

  /**
   * This method returns the value kind: an integer that represents
   * the kind of this value. See the interface ValueConstants.java.
   */
  public abstract byte getKind();

  public String getKindString() {
    try {
      return ValueImage[this.getKind()];
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* This method compares this with val.  */
  public abstract int compareTo(Object val);

  /* This method returns true iff elem is a member of this. */
  public abstract boolean member(Value elem);

  /* This method returns a new value after taking the except. */
  public abstract Value takeExcept(ValueExcept ex);

  /* This method returns a new value after taking the excepts. */
  public abstract Value takeExcept(ValueExcept[] exs);

  public void write(ValueOutputStream vos) throws IOException {
		throw new WrongInvocationException("ValueOutputStream: Can not pickle the value\n" +
			    Value.ppr(toString()));
  }
  
  /**
   * These methods allow storage and retrieval of the SemanticNode used to create the Value,
   * which is helpful for FingerprintException.
   */
  private transient SemanticNode source = null;

  public void setSource(final SemanticNode semanticNode) {
    source = semanticNode;
  }

  public SemanticNode getSource() {
    return source;
  }
  
  public boolean hasSource() {
	  return source != null;
  }

  /**
   * This method normalizes (destructively) the representation of
   * the value. It is essential for equality comparison.
   */
  public abstract boolean isNormalized();
  public abstract Value normalize();

  public final boolean isEmpty() {
    try {

      switch (this.getKind()) {
        case SETENUMVALUE:
          {
            SetEnumValue set = (SetEnumValue)this;
            return set.elems.size() == 0;
          }
        case INTERVALVALUE:
          {
            IntervalValue intv = (IntervalValue)this;
            return intv.size() == 0;
          }
        case SETCAPVALUE:
          {
            SetCapValue cap = (SetCapValue)this;
            return cap.elements().nextElement() == null;
          }
        case SETCUPVALUE:
          {
            SetCupValue cup = (SetCupValue)this;
            return cup.elements().nextElement() == null;
          }
        case SETDIFFVALUE:
          {
            SetDiffValue diff = (SetDiffValue)this;
            return diff.elements().nextElement() == null;
          }
        case SETOFFCNSVALUE:
          {
            SetOfFcnsValue fcns = (SetOfFcnsValue)this;
            return fcns.elements().nextElement() == null;
          }
        case SETOFRCDSVALUE:
          {
            SetOfRcdsValue srv = (SetOfRcdsValue)this;
            return srv.elements().nextElement() == null;
          }
        case SETOFTUPLESVALUE:
          {
            SetOfTuplesValue stv = (SetOfTuplesValue)this;
            return stv.elements().nextElement() == null;
          }
        case SUBSETVALUE:
          {
            // SUBSET S is never empty.  (It always contains {}.)
            return false;
          }
        case UNIONVALUE:
          {
            UnionValue uv = (UnionValue)this;
            return uv.elements().nextElement() == null;
          }
        case SETPREDVALUE:
          {
            SetPredValue spv = (SetPredValue)this;
            return spv.elements().nextElement() == null;
          }
        default:
          Assert.fail("Shouldn't call isEmpty() on value " + Value.ppr(this.toString()));
          return false;
      }

    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* Fully normalize this (composite) value. */
  public void deepNormalize() {
  }

  /* This method returns the fingerprint of this value. */
  public long fingerPrint(long fp) {
    try {
      Assert.fail("TLC has found a state in which the value of a variable contains " +
      Value.ppr(this.toString())); // SZ Feb 24, 2009: changed to static access
      return 0;      // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /**
   * This method returns the value permuted by the permutation. It
   * returns this if nothing is permuted.
   */
  public Value permute(MVPerm perm) {
    try {
      Assert.fail("TLC has found a state in which the value of a variable contains " +
      Value.ppr(this.toString())); // SZ Feb 24, 2009: changed to static access
      return null;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* This method returns true iff the value is finite. */
  public abstract boolean isFinite();

  /* This method returns the size of the value.  */
  public abstract int size();

  /* This method returns true iff the value is fully defined. */
  public abstract boolean isDefined();

  /* This method makes a real deep copy of this.  */
  public abstract Value deepCopy();

  /* This method returns true iff val can be assigned to this. */
  public abstract boolean assignable(Value val);

  /* This method returns the hash code of this value. */
  public final int hashCode() {
    try {
      long fp = this.fingerPrint(FP64.New());
      int high = (int)(fp >> 32);
      int low = (int)fp;
      return high ^ low;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public static boolean expand = true;

  /**
   * This method selects the component of this value. The component is
   * specified by path.
   */
  public final Value select(Value[] path) {
    try {
      Value result = this;
      for (int i = 0; i < path.length; i++) {
        if (!(result instanceof Applicable)) {
          Assert.fail("Attempted to apply EXCEPT construct to the value " +
                ppr(result.toString()) + ".");
        }
        Value elem = path[i];
        result = ((Applicable)result).select(elem);
        if (result == null) return null;
      }
      return result;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* Convert val into a SetEnumValue.  Returns null if not possible. */
  public SetEnumValue toSetEnum() {
	  return null;
  }

  /*
   * This method converts a value to a function value. It returns
   * null if the conversion fails.
   */
  public FcnRcdValue toFcnRcd() {
	  return null;
  }

  /*
   * This method converts a value to a function value. It returns
   * null if the conversion fails.
   */
  public RecordValue toRcd() {
	  return null;
  }

  /*
   * This method converts a value to a tuple value. It returns
   * null if the conversion fails.
   */
  public TupleValue toTuple() {
	  return null;
  }
  
  public static Value getValue(SemanticNode expr) {
    return (Value)expr.getToolObject(TLCGlobals.ToolId);
  }

  /**
   * This abstract method returns a string representation of this
   * value. Each subclass must provide its own implementation.
   */
  public abstract StringBuffer toString(StringBuffer sb, int offset);

  /* The string representation of this value */
  public final String toString() {
    try {
      StringBuffer sb = new StringBuffer();
      return this.toString(sb, 0).toString();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final String toString(String delim) {
    try {
      StringBuffer sb = new StringBuffer();
      sb = this.toString(sb, 0);
      sb.append(delim);
      return sb.toString();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public static String ppr(String s) {
    return PrettyPrint.mypp(s, 80) ;
  }
  public static String ppr(Value v) {
	  if (v == null) {
		  return "null";
	  }
	 return PrettyPrint.mypp(v.toString(), 80) ;
  }
}
