// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Sat 23 February 2008 at 10:32:25 PST by lamport
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

package tlc2.value;

import java.util.Enumeration;
import java.util.Hashtable;

import tlc2.util.FP64;
import util.Assert;
import util.UniqueString;

public class ModelValue extends Value {
    
    /**
     * A method to reset the model values
     * All callers should make sure that the model value class has been initialized
     */
    public static void init()
    {
       count = 0;
       mvTable = new Hashtable();
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
  private static Hashtable mvTable;
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
     else { this.type = 0 ; } ;
  }

  /* Make str a new model value, if it is not one yet.  */
  public static ModelValue make(String str) {
    ModelValue mv = (ModelValue)mvTable.get(str);
    if (mv != null) return mv;
    mv = new ModelValue(str);
    mvTable.put(str, mv);
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

  public final byte getKind() { return MODELVALUE; }

  public final int compareTo(Object obj) {
    if (obj instanceof ModelValue) {
      return this.val.compareTo(((ModelValue)obj).val);
    }
    return -1;
  }

  public final boolean equals(Object obj) {
    if (this.type == 0) {
      return (obj instanceof ModelValue &&
	      this.val.equals(((ModelValue)obj).val));
     };
    if (obj instanceof ModelValue) {
      ModelValue mobj = (ModelValue) obj ;
      if (   (mobj.type == this.type) 
          || (mobj.type == 0) ) { 
        return mobj.val == this.val ;
        } 
       else {
        Assert.fail("Attempted to check equality "
                    + "of the differently-typed model values "
                      + ppr(this.toString()) + " and " 
                      + ppr(mobj.toString()));
        } ;
     } ;
    Assert.fail("Attempted to check equality of typed model value "
                 + ppr(this.toString()) + " and non-model value\n"
                 + ppr(obj.toString())) ;
    return false;   // make compiler happy
  }

  /*************************************************************************
  * The following two methods are used used to check if this model value   *
  * equal to or a member of non-model value obj.  They return false if     *
  * this model value is untyped and raise an exception if it is typed.     *
  *************************************************************************/
  public final boolean modelValueEquals(Object obj){
    if (this.type != 0) {
    Assert.fail("Attempted to check equality of the typed model value "
                 + ppr(this.toString()) + " and the non-model value\n"
                 + ppr(obj.toString())) ;

     } ;
    return false ;    
  }

  public final boolean modelValueMember(Object obj){
    if (this.type != 0) {
    Assert.fail("Attempted to check if the typed model value "
                 + ppr(this.toString()) 
                 + " is an element of\n"
                 + ppr(obj.toString())) ;

     } ;
    return false ;    
  }

  public final boolean member(Value elem) {
    Assert.fail("Attempted to check if the value:\n" + ppr(elem.toString()) +
		"\nis an element of the model value " + ppr(this.toString()));
    return false;   // make compiler happy
  }

  public final boolean isFinite() {
    Assert.fail("Attempted to check if the model value " + ppr(this.toString()) +
		" is a finite set.");
    return false;   // make compiler happy
  }
  
  public final Value takeExcept(ValueExcept ex) {
    if (ex.idx < ex.path.length) {
      Assert.fail("Attempted to apply EXCEPT construct to the model value " +
		  ppr(this.toString()) + ".");
    }
    return ex.value;
  }
  
  public final Value takeExcept(ValueExcept[] exs) {
    if (exs.length != 0) {
      Assert.fail("Attempted to apply EXCEPT construct to the model value " +
		  ppr(this.toString()) + ".");
    }
    return this;
  }

  public final int size() {
    Assert.fail("Attempted to compute the number of elements in the model value " +
		ppr(this.toString()) + ".");
    return 0;   // make compiler happy
  }

  public final boolean isNormalized() { return true; }

  public final void normalize() { /*nop*/ }

  public final boolean isDefined() { return true; }

  public final Value deepCopy() { return this; }

  public final boolean assignable(Value val) {
    return ((val instanceof ModelValue) &&
	    this.val.equals(((ModelValue)val).val));
  }

  /* The fingerprint methods */
  public final long fingerPrint(long fp) {
    return this.val.fingerPrint(FP64.Extend(fp, MODELVALUE));
  }

  public final Value permute(MVPerm perm) {
    Value res = perm.get(this);
    if (res == null) return this;
    return res;
  }

  /* The string representation. */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    return sb.append(this.val);
  }


}
