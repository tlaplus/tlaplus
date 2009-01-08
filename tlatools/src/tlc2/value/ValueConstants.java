// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:21:10 PST by lamport
//      modified on Tue Aug 15 16:45:14 PDT 2000 by yuanyu

package tlc2.value;

import util.UniqueString;

public interface ValueConstants {

  /* Type code for values. */
  public final byte BOOLVALUE        = 0;
  public final byte INTVALUE         = BOOLVALUE + 1;
  public final byte REALVALUE        = INTVALUE + 1;  
  public final byte STRINGVALUE      = REALVALUE + 1;
  public final byte RECORDVALUE      = STRINGVALUE + 1;
  public final byte SETENUMVALUE     = RECORDVALUE + 1;
  public final byte SETPREDVALUE     = SETENUMVALUE + 1;
  public final byte TUPLEVALUE       = SETPREDVALUE + 1;
  public final byte FCNLAMBDAVALUE   = TUPLEVALUE + 1;
  public final byte FCNRCDVALUE      = FCNLAMBDAVALUE + 1;
  public final byte OPLAMBDAVALUE    = FCNRCDVALUE + 1;
  public final byte OPRCDVALUE       = OPLAMBDAVALUE + 1;
  public final byte METHODVALUE      = OPRCDVALUE + 1;
  public final byte SETOFFCNSVALUE   = METHODVALUE + 1;
  public final byte SETOFRCDSVALUE   = SETOFFCNSVALUE + 1;
  public final byte SETOFTUPLESVALUE = SETOFRCDSVALUE + 1;
  public final byte SUBSETVALUE      = SETOFTUPLESVALUE + 1;
  public final byte SETDIFFVALUE     = SUBSETVALUE + 1;
  public final byte SETCAPVALUE      = SETDIFFVALUE + 1;
  public final byte SETCUPVALUE      = SETCAPVALUE + 1;
  public final byte UNIONVALUE       = SETCUPVALUE + 1;
  public final byte MODELVALUE       = UNIONVALUE + 1;
  public final byte USERVALUE        = MODELVALUE + 1;
  public final byte INTERVALVALUE    = USERVALUE + 1;
  public final byte UNDEFVALUE       = INTERVALVALUE + 1;
  public final byte LAZYVALUE        = UNDEFVALUE + 1;
  public final byte DUMMYVALUE       = LAZYVALUE + 1;  

  public final String[] ValueImage = {
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

  /* Value constants. */
  public final BoolValue ValTrue  = new BoolValue(true);
  public final BoolValue ValFalse = new BoolValue(false);
  public final IntValue ValZero   = IntValue.gen(0);
  public final IntValue ValOne    = IntValue.gen(1);
  public final IntValue ValNegOne = IntValue.gen(-1);
  public final Value EmptySet = new SetEnumValue(new ValueVec(0), true);
  public final Value EmptyFcn = new FcnRcdValue(new Value[0], new Value[0], true);
  public final TupleValue EmptyTuple = new TupleValue(new Value[0]);
  public final RecordValue EmptyRcd = new RecordValue(new UniqueString[0], new Value[0], true);
  public final UndefValue ValUndef = new UndefValue();
  public final SetEnumValue DummyEnum = new SetEnumValue((ValueVec)null, true);

}
