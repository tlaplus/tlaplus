// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at  9:27:06 PST by lamport 
//      modified on Fri Jan  4 22:46:57 PST 2002 by yuanyu 

package tlc2.tool;

public class EvalControl {

  public static final int KeepLazy = 1;
  public static final int Primed = 2;
  public static final int Enabled = 4;

  public static final int Clear = 0;
  
  public static boolean isKeepLazy(int control) {
    return (control & KeepLazy) > 0;
  }

  public static int setKeepLazy(int control) {
    return control | KeepLazy;
  }

  public static boolean isPrimed(int control) {
    return (control & Primed) > 0;
  }
    
  public static int setPrimed(int control) {
    return control | Primed;
  }
    
  public static boolean isEnabled(int control) {
    return (control & Enabled) > 0;
  }

}
