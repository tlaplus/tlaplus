// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.utilities;

import util.ToolIO;

public class Assert {

  public final static void assertion(boolean b) {
    if (!b) {
      ToolIO.err.println("assertion failed:");
      Throwable e = new Throwable();
      e.printStackTrace();
      System.exit(1);
    }
  }

  public final static void fail(String msg) {
    ToolIO.err.println("Error: " + msg);
    Throwable e = new Throwable();
    e.printStackTrace();
    System.exit(1);
  }
  
}
