// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Mon 30 Apr 2007 at 15:30:13 PST by lamport
//      modified on Wed Dec  5 23:18:07 PST 2001 by yuanyu

package tlc2.value.impl;

import java.io.IOException;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.stream.Collectors;

import tla2sany.semantic.SemanticNode;
import tlc2.TLCGlobals;
import tlc2.tool.FingerprintException;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.util.FP64;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import tlc2.value.IValueOutputStream;
import tlc2.value.ValueConstants;
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

  /* This method returns true iff elem is a member of this. */
  public abstract boolean member(Value elem);
  
  /* This method returns a new value after taking the except. */
  public abstract Value takeExcept(ValueExcept ex);

  /* This method returns a new value after taking the excepts. */
  public abstract Value takeExcept(ValueExcept[] exs);

  /* This method returns true iff val can be assigned to this. */
  abstract boolean assignable(Value val);
  
  public abstract Value normalize();

  @Override
  public void write(IValueOutputStream vos) throws IOException {
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
  
  public boolean hasData() {
	  return false;
  }
  
  public Object getData() {
	  return null;
  }
  
  public Object setData(final Object obj) {
		throw new WrongInvocationException("Value: Can not set data\n" +
			    Values.ppr(toString()));
  }

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
          Assert.fail("Shouldn't call isEmpty() on value " + Values.ppr(this.toString()), getSource());
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
      Values.ppr(this.toString()), getSource()); // SZ Feb 24, 2009: changed to static access
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
      Values.ppr(this.toString()), getSource()); // SZ Feb 24, 2009: changed to static access
      return null;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

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
  public final Value select(Value[] path) {
    try {
      Value result = this;
      for (int i = 0; i < path.length; i++) {
        if (!(result instanceof Applicable)) {
          Assert.fail("Attempted to apply EXCEPT construct to the value " +
                Values.ppr(result.toString()) + ".", getSource());
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
  public Value toSetEnum() {
	  return null;
  }

  /*
   * This method converts a value to a function value. It returns
   * null if the conversion fails.
   */
  public Value toFcnRcd() {
	  return null;
  }

  /*
   * This method converts a value to a function value. It returns
   * null if the conversion fails.
   */
  public Value toRcd() {
	  return null;
  }

  /*
   * This method converts a value to a tuple value. It returns
   * null if the conversion fails.
   */
  public Value toTuple() {
	  return null;
  }
  
  public TLCState toState() {
	  return null;
  }
  
  /* The string representation of this value */
  @Override
  public final String toString() {
	  return toStringImpl("", true);
  }
  
  /* Same as toString except that nested exceptions won't be silently discarded */
  public final String toStringUnchecked() {
	  return toStringImpl("", false);
  }

  /* Same as toString. */
  @Override
  public String toUnquotedString() {
	  return toString();
  }

  @Override
  public final String toString(final String delim) {
	  return toStringImpl(delim, true);
  }

  public final String toStringUnchecked(final String delim) {
	  return toStringImpl(delim, false);
  }
  
  private final String toStringImpl(final String delim, final boolean checked) {
    try {
        final StringBuffer sb = this.toString(new StringBuffer(), 0, checked);
        sb.append(delim);
        return sb.toString();
      }
      catch (RuntimeException | OutOfMemoryError e) {
        if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
        else { throw e; }
      }
  }
  
	public TLCVariable toTLCVariable(final TLCVariable variable, Random rnd) {
		variable.setInstance(this);
		// TODO: Use Value#getKindString instead?
//		if (hasSource()) {
//			variable.setType(String.format("%s at %s", getTypeString(), getSource()));
//		} else {
			variable.setType(getTypeString());
//		}
		variable.setValue(toString());
		if (this instanceof Enumerable || this instanceof FcnRcdValue || this instanceof RecordValue
				|| this instanceof TupleValue) {
			// Atomic values such as IntValue throw an exception on #isFinite.
			if (this.isFinite()) {
				variable.setVariablesReference(rnd.nextInt(Integer.MAX_VALUE - 1) + 1);
			}
		}
		return variable;
	}

	public String getTypeString() {
		return String.format("%s: %s", getClass().getSimpleName(), getKindString());
	}

	public List<TLCVariable> getTLCVariables(TLCVariable var, Random rnd) {
		if (this instanceof Enumerable && this.isFinite()) {
			Enumerable e = (Enumerable) this;
			return e.elements().all().stream().map(value -> value.toTLCVariable(var.newInstance(value, rnd), rnd))
					.collect(Collectors.toList());
		}
		return new ArrayList<>(0);
	}
}
