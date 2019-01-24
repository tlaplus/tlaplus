// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Mon 30 Apr 2007 at 15:30:13 PST by lamport
//      modified on Wed Dec  5 23:18:07 PST 2001 by yuanyu

package tlc2.value.impl;

import java.io.IOException;
import java.io.Serializable;

import tla2sany.semantic.SemanticNode;
import tlc2.TLCGlobals;
import tlc2.tool.FingerprintException;
import tlc2.tool.coverage.CostModel;
import tlc2.util.FP64;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import tlc2.value.ValueConstants;
import tlc2.value.ValueExcept;
import tlc2.value.ValueOutputStream;
import tlc2.value.Values;
import util.Assert;
import util.WrongInvocationException;

public abstract class Value implements ValueConstants, Serializable, IValue {

	  private static final String[] ValueImage = {
	    "a Boolean value",                     // "BoolValue",
	    "an integer",                          // "IntValue",
	    "a real",                              // "RealValue",
	    "a string",                            // "StringValue",
	    "a record",                            // "RecordValue",
	    "a set of the form {e1, ... ,eN}",     // "SetEnumValue",
	    "a set of the form {x \\in S : expr}", // "SetPredValue",
	    "a tuple",                             // "TupleValue",
	    "a function of the form  [x \\in S |-> expr]",           // "FcnLambdaValue",
	    "a function  of the form (d1 :> e1 @@ ... @@ dN :> eN)", // "FcnRcdValue",
	    "an operator",                                // "OpLambdaValue",
	    "a constant operator",                        // "OpRcdValue",
	    "a java method",                              // "MethodValue",    
	    "a set of the form [S -> T]",                 // "SetOfFcnsValue",
	    "a set of the form [d1 : S1, ... , dN : SN]", // "SetOfRcdsValue",
	    "a cartesian product",                        // "SetOfTuplesValue",
	    "a set of the form SUBSET S",                 // "SubsetValue",
	    "a set of the form S \\ T",                   // "SetDiffValue",
	    "a set of the form S \\cap T",                // "SetCapValue",
	    "a set of the form S \\cup T",                // "SetCupValue",
	    "a set of the form UNION  S",                 // "UnionValue",
	    "a model value",                              // "ModelValue",
	    "a special set constant",                     // "UserValue",
	    "a set of the form i..j",                     // "IntervalValue",
	    "an undefined value",                         // "UndefValue",
	    "a value represented in lazy form",           // "LazyValue",
	    "a dummy for not-a-value",                    // "DummyValue",    
	  };
	  
	/**
	 * @see See note on performance in CostModelCreator.
	 */
	protected static final boolean coverage = TLCGlobals.isCoverageEnabled();
  /**
   * For each kind of value, we introduce a subclass of Value.
   * All the subclasses are given in this value package.
   */

  /**
   * This method returns the value kind: an integer that represents
   * the kind of this value. See the interface ValueConstants.java.
   */
  @Override
public abstract byte getKind();

  @Override
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
  @Override
public abstract int compareTo(Object val);

  /* This method returns true iff elem is a member of this. */
  @Override
public abstract boolean member(IValue elem);

  /* This method returns a new value after taking the except. */
  @Override
public abstract IValue takeExcept(ValueExcept ex);

  /* This method returns a new value after taking the excepts. */
  @Override
public abstract IValue takeExcept(ValueExcept[] exs);

  @Override
public void write(ValueOutputStream vos) throws IOException {
		throw new WrongInvocationException("ValueOutputStream: Can not pickle the value\n" +
			    Values.ppr(toString()));
  }

  public transient CostModel cm = CostModel.DO_NOT_RECORD;
  
  @Override
public IValue setCostModel(CostModel cm) {
	  this.cm = cm;
	  return this;
  }
  
  @Override
public CostModel getCostModel() {
	  return this.cm;
  }
  
  /**
   * These methods allow storage and retrieval of the SemanticNode used to create the Value,
   * which is helpful for FingerprintException.
   */
  private transient SemanticNode source = null;

  @Override
public void setSource(final SemanticNode semanticNode) {
    source = semanticNode;
  }

  @Override
public SemanticNode getSource() {
    return source;
  }
  
  @Override
public boolean hasSource() {
	  return source != null;
  }

  /**
   * This method normalizes (destructively) the representation of
   * the value. It is essential for equality comparison.
   */
  @Override
public abstract boolean isNormalized();
  @Override
public abstract IValue normalize();

  @Override
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
          Assert.fail("Shouldn't call isEmpty() on value " + Values.ppr(this.toString()));
          return false;
      }

    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* Fully normalize this (composite) value. */
  @Override
public void deepNormalize() {
  }

  /* This method returns the fingerprint of this value. */
  @Override
public long fingerPrint(long fp) {
    try {
      Assert.fail("TLC has found a state in which the value of a variable contains " +
      Values.ppr(this.toString())); // SZ Feb 24, 2009: changed to static access
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
  @Override
public IValue permute(IMVPerm perm) {
    try {
      Assert.fail("TLC has found a state in which the value of a variable contains " +
      Values.ppr(this.toString())); // SZ Feb 24, 2009: changed to static access
      return null;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* This method returns true iff the value is finite. */
  @Override
public abstract boolean isFinite();

  /* This method returns the size of the value.  */
  @Override
public abstract int size();

  /* This method returns true iff the value is fully defined. */
  @Override
public abstract boolean isDefined();

  /* This method makes a real deep copy of this.  */
  @Override
public abstract IValue deepCopy();

  /* This method returns true iff val can be assigned to this. */
  @Override
public abstract boolean assignable(IValue val);

  /* This method returns the hash code of this value. */
  @Override
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

  /**
   * This method selects the component of this value. The component is
   * specified by path.
   */
  @Override
public final IValue select(IValue[] path) {
    try {
      IValue result = this;
      for (int i = 0; i < path.length; i++) {
        if (!(result instanceof Applicable)) {
          Assert.fail("Attempted to apply EXCEPT construct to the value " +
                Values.ppr(result.toString()) + ".");
        }
        IValue elem = path[i];
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
  @Override
public IValue toSetEnum() {
	  return null;
  }

  /*
   * This method converts a value to a function value. It returns
   * null if the conversion fails.
   */
  @Override
public IValue toFcnRcd() {
	  return null;
  }

  /*
   * This method converts a value to a function value. It returns
   * null if the conversion fails.
   */
  @Override
public IValue toRcd() {
	  return null;
  }

  /*
   * This method converts a value to a tuple value. It returns
   * null if the conversion fails.
   */
  @Override
public IValue toTuple() {
	  return null;
  }
  
  /**
   * This abstract method returns a string representation of this
   * value. Each subclass must provide its own implementation.
   */
  @Override
public abstract StringBuffer toString(StringBuffer sb, int offset);

  /* The string representation of this value */
  @Override
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

  @Override
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
}
