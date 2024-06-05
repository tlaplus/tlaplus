// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

package tla2sany;

/**
 * SANY is a shell class to call the main driver method of SANY
 */

public class SANY {

  public static final void main(String[] args) {
    int ret = tla2sany.drivers.SANY.SANYmain(args);
    System.exit(ret);
  }
  
}
