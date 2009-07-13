// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:30:13 PST by lamport
//      modified on Wed Dec  5 23:18:07 PST 2001 by yuanyu

package tlc2.value;

import java.io.Serializable;

import tla2sany.semantic.SemanticNode;
import tlc2.TLCGlobals;
import tlc2.pprint.PrettyPrint;
import tlc2.util.FP64;
import util.Assert;

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

  public String getKindString() { return ValueImage[this.getKind()]; }

  /* This method compares this with val.  */
  public abstract int compareTo(Object val);
  
  /* This method returns true iff elem is a member of this. */
  public abstract boolean member(Value elem);

  /* This method returns a new value after taking the except. */
  public abstract Value takeExcept(ValueExcept ex);

  /* This method returns a new value after taking the excepts. */
  public abstract Value takeExcept(ValueExcept[] exs);

  /**
   * This method normalizes (destructively) the representation of
   * the value. It is essential for equality comparison.
   */
  public abstract boolean isNormalized();
  public abstract void normalize();

  /* Fully normalize this (composite) value. */
  public final void deepNormalize() {
    switch (this.getKind()) {
    case RECORDVALUE:
      {
	RecordValue rcd = (RecordValue)this;
	for (int i = 0; i < rcd.values.length; i++) {
	  rcd.values[i].deepNormalize();
	}
	rcd.normalize();
	break;
      }
    case FCNRCDVALUE:
      {
	FcnRcdValue fcn = (FcnRcdValue)this;
	for (int i = 0; i < fcn.values.length; i++) {
	  fcn.values[i].deepNormalize();
	}
	fcn.normalize();
	break;
      }
    case SETENUMVALUE:
      {
	SetEnumValue set = (SetEnumValue)this;
	for (int i = 0; i < set.elems.size(); i++) {
	  set.elems.elementAt(i).deepNormalize();
	}
	set.normalize();
	break;
      }
    case TUPLEVALUE:
      {
	TupleValue tv = (TupleValue)this;
	for (int i = 0; i < tv.elems.length; i++) {
	  tv.elems[i].deepNormalize();
	}
	break;
      }
    case SETCAPVALUE:
      {
	SetCapValue cap = (SetCapValue)this;
	cap.set1.deepNormalize();
	cap.set2.deepNormalize();
	if (cap.capSet == null) {
	  cap.capSet = DummyEnum;
	}
	else if (cap.capSet != DummyEnum) {
	  cap.capSet.deepNormalize();
	}
	break;
      }
    case SETCUPVALUE:
      {
	SetCupValue cup = (SetCupValue)this;
	cup.set1.deepNormalize();
	cup.set2.deepNormalize();
	if (cup.cupSet == null) {
	  cup.cupSet = DummyEnum;
	}
	else if (cup.cupSet != DummyEnum) {
	  cup.cupSet.deepNormalize();
	}
	break;
      }
    case SETDIFFVALUE:
      {
	SetDiffValue diff = (SetDiffValue)this;
	diff.set1.deepNormalize();
	diff.set2.deepNormalize();
	if (diff.diffSet == null) {
	  diff.diffSet = DummyEnum;
	}
	else if (diff.diffSet != DummyEnum) {
	  diff.diffSet.deepNormalize();
	}
	break;
      }
    case SETOFFCNSVALUE:
      {
	SetOfFcnsValue fcns = (SetOfFcnsValue)this;
	fcns.domain.deepNormalize();
	fcns.range.deepNormalize();
	if (fcns.fcnSet == null) {
	  fcns.fcnSet = DummyEnum;
	}
	else if (fcns.fcnSet != DummyEnum) {
	  fcns.fcnSet.deepNormalize();
	}
	break;
      }
    case SETOFRCDSVALUE:
      {
	SetOfRcdsValue srv = (SetOfRcdsValue)this;
	for (int i = 0; i < srv.values.length; i++) {
	  srv.values[i].deepNormalize();
	}
	if (srv.rcdSet == null) {
	  srv.rcdSet = DummyEnum;
	}
	else if (srv.rcdSet != DummyEnum) {
	  srv.rcdSet.deepNormalize();
	}
	break;
      }
    case SETOFTUPLESVALUE:
      {
	SetOfTuplesValue stv = (SetOfTuplesValue)this;
	for (int i = 0; i < stv.sets.length; i++) {
	  stv.sets[i].deepNormalize();
	}
	if (stv.tupleSet == null) {
	  stv.tupleSet = DummyEnum;
	}
	else if (stv.tupleSet != DummyEnum) {
	  stv.tupleSet.deepNormalize();
	}
	break;
      }
    case SUBSETVALUE:
      {
	SubsetValue pset = (SubsetValue)this;
	pset.set.deepNormalize();
	if (pset.pset == null) {
	  pset.pset = DummyEnum;
	}
	else if (pset.pset != DummyEnum) {
	  pset.pset.deepNormalize();
	}
	break;
      }
    case UNIONVALUE:
      {
	UnionValue uv = (UnionValue)this;
	if (uv.realSet == null) {
	  uv.realSet = DummyEnum;
	}
	else if (uv.realSet != DummyEnum) {
	  uv.realSet.deepNormalize();
	}
	break;
      }
    case SETPREDVALUE:
      {
	SetPredValue spv = (SetPredValue)this;
	spv.inVal.deepNormalize();
	break;
      }
    case FCNLAMBDAVALUE:
      {
	FcnLambdaValue flv = (FcnLambdaValue)this;
	if (flv.fcnRcd == null) {
	  if (flv.excepts != null) {
	    for (int i = 0; i < flv.excepts.length; i++) {
	      flv.excepts[i].value.deepNormalize();
	      for (int j = 0; j < flv.excepts[i].path.length; j++) {
		flv.excepts[i].path[j].deepNormalize();
	      }
	    }
	  }
	  Value[] paramDoms = flv.params.domains;
	  for (int i = 0; i < paramDoms.length; i++) {
	    paramDoms[i].deepNormalize();
	  }
	}
	else {
	  flv.fcnRcd.deepNormalize();
	}
      }
    default:
      break;
    }
  }
  
  /* This method returns the fingerprint of this value. */
  public long fingerPrint(long fp) {
    Assert.fail("TLC has found a state in which the value of a variable contains " +
		Value.ppr(this.toString())); // SZ Feb 24, 2009: changed to static access
    return 0;      // make compiler happy
  }

  /**
   * This method returns the value permuted by the permutation. It
   * returns this if nothing is permuted.
   */
  public Value permute(MVPerm perm) {
    Assert.fail("TLC has found a state in which the value of a variable contains " +
		Value.ppr(this.toString())); // SZ Feb 24, 2009: changed to static access
    return null;   // make compiler happy
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
    long fp = this.fingerPrint(FP64.New());
    int high = (int)(fp >> 32);
    int low = (int)fp;
    return high ^ low;
  }

  public static boolean expand = true;
  
  /**
   * This method selects the component of this value. The component is
   * specified by path.
   */
  public final Value select(Value[] path) {
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
    StringBuffer sb = new StringBuffer();
    return this.toString(sb, 0).toString();
  }

  public static String ppr(String s) {
    return PrettyPrint.mypp(s, 80) ;
  }
}
