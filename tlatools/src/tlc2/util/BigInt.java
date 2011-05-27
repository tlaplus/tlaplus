// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tlc2.util;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.math.BigInteger;
import java.util.Random;


public class BigInt extends BigInteger implements Cloneable, ExternalSortable {

  public final static BigInt BigZero = new BigInt("0");
  public final static BigInt BigOne = new BigInt("1");
  public final static BigInt BigTwo = new BigInt("2");

  public BigInt(String val) { super(val); }
  
  public BigInt(byte[] val) { super(val); }

  public BigInt(int numBits, Random rnd) { super(numBits, rnd); }

  /* Returns the fingerprint of this. */
  public final long fingerPrint() {
    return FP64.New(this.toByteArray());
  }

  /**
    * Returns true iff x is a BigInt whose value is equal to this.value.
    * This method is provided so that BigInts can be used as hash keys.
    */
  public final boolean equals(Object x) {
    return ((x instanceof BigInt) && super.equals(x));
  }

  public final void write(OutputStream out) throws IOException {
    ByteUtils.writeSizeBigInt(out, this);
  }
    
  public final BigInt read(InputStream in) throws IOException {
    return ByteUtils.readSizeBigInt(in);
  }

}
