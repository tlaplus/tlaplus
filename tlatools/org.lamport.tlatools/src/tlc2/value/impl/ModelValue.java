// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Sat 23 February 2008 at 10:32:25 PST by lamport
//      modified on Fri Aug 10 15:07:47 PDT 2001 by yuanyu

/***************************************************************************
* Change to model values made by LL on 23 Feb 2008:                        *
* ------                                                                   *
* A model value whose name is "x_str" for any character x and string str   *
* is said to have TYPE 'x'.  Otherwise, it is said to be untyped.  It is   *
* an error to test if a typed model value is equal to any value except a   *
* model value that is either untyped or has the same type.  (As before,    *
* an untyped model value is unequal to any value except itself.)           *
*                                                                          *
* This was implemented by adding a `type' field to a ModelValue object     *
* and making changes to the following classes:                             *
*                                                                          *
*    changed member method                                                 *
*       module/Integers.java                                               *
*       module/Naturals.java                                               *
*       module/Sequences.java                                              *
*       module/Strings.java                                                *
*       value/IntervalValue.java  CHECK THIS with mv \notin 1..2           *
*       value/SetOfFcnsValue.java                                          *
*       value/SetOfRcdsValue.java                                          *
*       value/SetOfTuplesValue.java                                        *
*       value/StringValue.java                                             *
*    changed equals method                                                 *
*       value/BoolValue.java                                               *
*       value/FcnRcdValue.java                                             *
*       value/IntValue.java                                                *
*       value/RecordValue.java                                             *
*       value/SetEnumValue.java                                            *
***************************************************************************/

package tlc2.value.impl;

import java.io.IOException;
import java.util.Enumeration;
import java.util.Hashtable;

import tlc2.tool.FingerprintException;
import tlc2.util.FP64;
import tlc2.value.IMVPerm;
import tlc2.value.IModelValue;
import tlc2.value.IValue;
import tlc2.value.IValueOutputStream;
import tlc2.value.Values;
import util.Assert;
import util.UniqueString;

public class ModelValue extends Value implements IModelValue {

    /**
     * A method to reset the model values
     * All callers should make sure that the model value class has been initialized
     */
    public static void init()
    {
       count = 0;
       mvTable = new Hashtable<String, ModelValue>();
       mvs = null;
    }

    /**
     * Workround to the static usage
     */
    static
    {
        init();
    }

  private static int count;
  private static Hashtable<String, ModelValue> mvTable;
  // SZ Mar 9, 2009: public accessed field, this will cause troubles
  public static ModelValue[] mvs;

  public UniqueString val;
  public int index;
  public char type;  // type = 0 means untyped.

  /* Constructor */
  private ModelValue(String val) {
    // SZ 11.04.2009: changed access method
    this.val = UniqueString.uniqueStringOf(val);
    this.index = count++;
    if (   (val.length() > 2)
        && (val.charAt(1) == '_')) {
      this.type = val.charAt(0) ;
      }
     else { this.type = 0 ; }
  }

  /* Make str a new model value, if it is not one yet.  */
  public static Value make(String str) {
    ModelValue mv = (ModelValue)mvTable.get(str);
    if (mv != null) return mv;
    mv = new ModelValue(str);
    mvTable.put(str, mv);
    return mv;
  }

  public static Value add(String str) {
	    ModelValue mv = (ModelValue)mvTable.get(str);
	    if (mv != null) return mv;
	    mv = new ModelValue(str);
	    mvTable.put(str, mv);
	    // Contrary to the make method above, this method can be invoked
      // *after* setValues below has been called from Spec. Thus, we
      // re-create mvs here.  However, this will only work if add is
      // called by SpecProcessor as part of constant processing.  add
      // cannot be called from the initial predicate, let alone the
      // next-state relation.  Except bogus behavior such as 
      // FingerprintException, NullPointers, ... or serialization
      // and deserialization in the StateQueue to fail.
	    setValues();
	    return mv;
	}

  /* Collect all the model values defined thus far. */
  public static void setValues() {
    mvs = new ModelValue[mvTable.size()];
    Enumeration Enum = mvTable.elements();
    while (Enum.hasMoreElements()) {
      ModelValue mv = (ModelValue)Enum.nextElement();
      mvs[mv.index] = mv;
    }
  }

  @Override
  public final byte getKind() { return MODELVALUE; }

	/*
	 * #### Typed Model Values
	 * 
	 * One way that TLC finds bugs is by reporting an error if it tries to compare
	 * two incomparable values&mdash;for example, a string and a set. The use of
	 * model values can cause TLC to miss bugs because it will compare a model value
	 * to any value without complaining (finding it unequal to anything but itself).
	 * Typed model values have been introduced to solve this problem.
	 * 
	 * For any character &tau;, a model value whose name begins with the
	 * two-character string "&tau;\_" is defined to have type &tau;. For example,
	 * the model value _x\_1_ has type _x_. Any other model value is untyped. TLC
	 * treats untyped model values as before, being willing to compare them to
	 * anything. However it reports an error if it tries to compare a typed model
	 * value to anything other than a model value of the same type or an untyped
	 * model value. Thus, TLC will find the model value _x_1_ unequal to the model
	 * values _x_ab2_ and _none_, but will report an error if it tries to compare
	 * _x\_1_ to _a\_1_.
	 */

  @Override
  public final int compareTo(Object obj) {
    try {
		if (this.type == 0) {
			if (obj instanceof ModelValue) {
				return this.val.compareTo(((ModelValue) obj).val);
			} else {
				return -1;
			}
		}
		if (obj instanceof ModelValue) {
			ModelValue mobj = (ModelValue) obj;
			if ((mobj.type == this.type) || (mobj.type == 0)) {
				return this.val.compareTo(((ModelValue) obj).val);
			} else {
				Assert.fail("Attempted to compare the differently-typed model values "
						+ Values.ppr(this.toString()) + " and " + Values.ppr(mobj.toString()), getSource());
			}
		}
		Assert.fail("Attempted to compare the typed model value " + Values.ppr(this.toString())
				+ " and non-model value\n" + Values.ppr(obj.toString()), getSource());
		return -1; // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean equals(Object obj) {
    try {
      if (this.type == 0) {
        return (obj instanceof ModelValue &&
          this.val.equals(((ModelValue)obj).val));
       }
      if (obj instanceof ModelValue) {
        ModelValue mobj = (ModelValue) obj ;
        if (   (mobj.type == this.type)
            || (mobj.type == 0) ) {
          return mobj.val == this.val ;
          }
         else {
          Assert.fail("Attempted to check equality "
                      + "of the differently-typed model values "
                        + Values.ppr(this.toString()) + " and "
                        + Values.ppr(mobj.toString()), getSource());
          }
      }
      Assert.fail("Attempted to check equality of typed model value "
                   + Values.ppr(this.toString()) + " and non-model value\n"
                   + Values.ppr(obj.toString()), getSource()) ;
      return false;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final int modelValueCompareTo(final Object obj){
	    try {
	      if (this.type != 0) {
	      Assert.fail("Attempted to compare the typed model value "
	                   + Values.ppr(this.toString()) + " and the non-model value\n"
	                   + Values.ppr(obj.toString()), getSource()) ;

	       }
	      return 1 ;
	    }
	    catch (RuntimeException | OutOfMemoryError e) {
	      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
	      else { throw e; }
	    }
  }
  
  /*************************************************************************
  * The following two methods are used used to check if this model value   *
  * equal to or a member of non-model value obj.  They return false if     *
  * this model value is untyped and raise an exception if it is typed.     *
  *************************************************************************/
  public final boolean modelValueEquals(Object obj){
    try {
      if (this.type != 0) {
      Assert.fail("Attempted to check equality of the typed model value "
                   + Values.ppr(this.toString()) + " and the non-model value\n"
                   + Values.ppr(obj.toString()), getSource()) ;

       }
      return false ;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean modelValueMember(Object obj){
    try {
      if (this.type != 0) {
      Assert.fail("Attempted to check if the typed model value "
                   + Values.ppr(this.toString())
                   + " is an element of\n"
                   + Values.ppr(obj.toString()), getSource()) ;

       }
      return false ;
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
      "\nis an element of the model value " + Values.ppr(this.toString()), getSource());
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
      Assert.fail("Attempted to check if the model value " + Values.ppr(this.toString()) +
      " is a finite set.", getSource());
      return false;   // make compiler happy
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
        Assert.fail("Attempted to apply EXCEPT construct to the model value " +
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
        Assert.fail("Attempted to apply EXCEPT construct to the model value " +
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
      Assert.fail("Attempted to compute the number of elements in the model value " +
      Values.ppr(this.toString()) + ".", getSource());
      return 0;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public boolean mutates() {
	  return false;
  }

  @Override
  public final boolean isNormalized() { return true; }

  @Override
  public final Value normalize() { /*nop*/return this; }

  @Override
  public final boolean isDefined() { return true; }

  @Override
  public final IValue deepCopy() { return this; }

  @Override
  public final boolean assignable(Value val) {
    try {
      return ((val instanceof ModelValue) &&
        this.val.equals(((ModelValue)val).val));
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

	@Override
	public void write(IValueOutputStream vos) throws IOException {
		vos.writeByte(MODELVALUE);
		vos.writeShort((short) index);
	}

  /* The fingerprint methods */
  @Override
  public final long fingerPrint(long fp) {
    try {
      return this.val.fingerPrint(FP64.Extend(fp, MODELVALUE));
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final IValue permute(IMVPerm perm) {
    try {
      IValue res = perm.get(this);
      if (res == null) return this;
      return res;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* The string representation. */
  @Override
  public final StringBuffer toString(StringBuffer sb, int offset, boolean ignored) {
    try {
      return sb.append(this.val);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

	// The presence of this field is justified by a small number of ModelValue
	// instances being created overall.
	private Object data;

	@Override
	public boolean hasData() {
		return data != null;
	}

	@Override
	public Object getData() {
		return data;
	}

	@Override
	public Object setData(final Object obj) {
		this.data = obj;
		return obj;
	}
}
