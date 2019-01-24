// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:21:10 PST by lamport
//      modified on Tue Aug 15 16:45:14 PDT 2000 by yuanyu

package tlc2.value;

import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.TupleValue;

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

  public final IntValue ValZero   = IntValue.gen(0);
  public final IntValue ValOne    = IntValue.gen(1);
  public final IntValue ValNegOne = IntValue.gen(-1);
  public final IValue EmptyFcn = new FcnRcdValue(new IValue[0], new IValue[0], true);
  public final ITupleValue EmptyTuple = new TupleValue(new IValue[0]);

}
