// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:21:10 PST by lamport
//      modified on Tue Aug 15 16:45:14 PDT 2000 by yuanyu

package tlc2.value;

public interface ValueConstants {

  /* Type code for values. */
  byte BOOLVALUE        = 0;
  byte INTVALUE         = BOOLVALUE + 1;
  byte REALVALUE        = INTVALUE + 1;
  byte STRINGVALUE      = REALVALUE + 1;
  byte RECORDVALUE      = STRINGVALUE + 1;
  byte SETENUMVALUE     = RECORDVALUE + 1;
  byte SETPREDVALUE     = SETENUMVALUE + 1;
  byte TUPLEVALUE       = SETPREDVALUE + 1;
  byte FCNLAMBDAVALUE   = TUPLEVALUE + 1;
  byte FCNRCDVALUE      = FCNLAMBDAVALUE + 1;
  byte OPLAMBDAVALUE    = FCNRCDVALUE + 1;
  byte OPRCDVALUE       = OPLAMBDAVALUE + 1;
  byte METHODVALUE      = OPRCDVALUE + 1;
  byte SETOFFCNSVALUE   = METHODVALUE + 1;
  byte SETOFRCDSVALUE   = SETOFFCNSVALUE + 1;
  byte SETOFTUPLESVALUE = SETOFRCDSVALUE + 1;
  byte SUBSETVALUE      = SETOFTUPLESVALUE + 1;
  byte SETDIFFVALUE     = SUBSETVALUE + 1;
  byte SETCAPVALUE      = SETDIFFVALUE + 1;
  byte SETCUPVALUE      = SETCAPVALUE + 1;
  byte UNIONVALUE       = SETCUPVALUE + 1;
  byte MODELVALUE       = UNIONVALUE + 1;
  byte USERVALUE        = MODELVALUE + 1;
  byte INTERVALVALUE    = USERVALUE + 1;
  byte UNDEFVALUE       = INTERVALVALUE + 1;
  byte LAZYVALUE        = UNDEFVALUE + 1;
  byte DUMMYVALUE       = LAZYVALUE + 1;

}
