// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tlc2.util;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.math.BigInteger;
import java.util.Random;


public class BigInt extends BigInteger implements Cloneable, ExternalSortable {

    public static final BigInt BigZero = new BigInt("0");
    public static final BigInt BigOne = new BigInt("1");
    public static final BigInt BigTwo = new BigInt("2");
    private static final long serialVersionUID = 612839568056678260L;

    public BigInt(final String val) {
        super(val);
    }

    public BigInt(final byte[] val) {
        super(val);
    }

    public BigInt(final int numBits, final Random rnd) {
        super(numBits, rnd);
    }

    /* Returns the fingerprint of this. */
    public final long fingerPrint() {
        return FP64.New(this.toByteArray());
    }

    /**
     * Returns true iff x is a BigInt whose value is equal to this.value.
     * This method is provided so that BigInts can be used as hash keys.
     */
    @Override
    public final boolean equals(final Object x) {
        return ((x instanceof BigInt) && super.equals(x));
    }

    @Override
    public final void write(final OutputStream out) throws IOException {
        ByteUtils.writeSizeBigInt(out, this);
    }

    @Override
    public final BigInt read(final InputStream in) throws IOException {
        return ByteUtils.readSizeBigInt(in);
    }

}
