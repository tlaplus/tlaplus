// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.utilities;

import util.ToolIO;

/**
 * Implementation of assertion
 * @author Simon Zambrovski
 * @version $Id$
 */
public class Assert {

  // fishy way to exit the program
  public final static void assertion(boolean b) {
    if (!b) {
      ToolIO.err.println("assertion failed:");
      System.exit(1);
    }
  }

// SZ Jul 13, 2009: method not used
//  public final static void fail(String msg) {
//    ToolIO.err.println("Error: " + msg);
//    System.exit(1);
//  }
  
}
