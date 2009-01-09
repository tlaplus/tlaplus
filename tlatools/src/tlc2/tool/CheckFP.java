// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

package tlc2.tool;

import java.io.IOException;

import tlc2.util.BufferedRandomAccessFile;

public class CheckFP {
  /*
   * Andrei Broder told us that
   *  1. We are probably in trouble if any two fingerprints have the
   *     same high order 56 bits.
   *  2. With a lot of hand waving, the probability of collision is
   *     about the max of 1/|fi - fj|.
   * This program does these sanity checkings.
   */
  public static void main(String args[]) {
    try {
      BufferedRandomAccessFile raf = new BufferedRandomAccessFile(args[0], "r");
      long fileLen = raf.length();
      long dis = Long.MAX_VALUE;
      int cnt = 0;
      long x = raf.readLong();
      while (raf.getFilePointer() < fileLen) {
	long y = raf.readLong();
	if ((x >> 8) == (y >> 8))
	  System.err.println("bad: " + x + " and " + y);
	dis = Math.min(dis, y-x);
	x = y;
	cnt++;
	if ((cnt & 0xFFFF) == 0)
	  System.err.println("the number of states checked: " + cnt);
      }
      System.err.println("the number of states checked: " + cnt);
      System.err.println("the probability of collision: " + 1.0/dis);
    }
    catch (IOException e) {
      System.err.println("Error: " + e.getMessage());
      System.exit(1);
    }
  }

}
