// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tlc2.util;

import tlc2.output.EC;
import util.Assert;

import java.math.BigInteger;

public class Combinatorics {

    public static final int MAXCHOOSENUM = 62;
    public static final int CHOOSETABLESIZE = (MAXCHOOSENUM - 3) * (MAXCHOOSENUM - 4) / 2 + MAXCHOOSENUM - 3;
    public static final long[] CHOOSETABLE = new long[CHOOSETABLESIZE];
    private static final long[] SUMCHOOSETABLE = new long[CHOOSETABLESIZE];

    static {
        int i, n, m;
        long sum;

        n = 4;
        m = 2;
        sum = 5;
        for (i = 0; i < CHOOSETABLESIZE; i++) {
            CHOOSETABLE[i] = choose(n - 1, m) + choose(n - 1, m - 1);
            sum += CHOOSETABLE[i];
            SUMCHOOSETABLE[i] = sum;
            if (n == m + 2) {
                n++;
                m = 2;
                sum = 1L + n;
            } else
                m++;
        }
    }

    public static long choose(final int n, final int m) {
        if (n < 0 || m < 0) {
            Assert.check(((m >= 0) && (n >= 0) && (n >= m)), EC.TLC_CHOOSE_ARGUMENTS_WRONG, "choose");
        }
        if (m == 0 || m == n) {
            return 1;
        } else if (m == 1 || m == n - 1) {
            return n;
        } else if (n == 0 || m > n) {
            // Cannot choose from zero elements or more elements than present.
            return 0;
        } else {
            final int j = choosePairToInt(n, m);
            if (j < CHOOSETABLESIZE) {
                return CHOOSETABLE[j];
            }
            return binomial(n, m); // calculate on demand
        }
    }

    public static long sumChoose(final int n, final int m) {
        Assert.check(((m >= 0) && (n >= 0) && (n >= m)), EC.TLC_CHOOSE_ARGUMENTS_WRONG, "sumChoose");
        if (m == 0) {
            return 1;
        } else if (m == n) {
            return ((long) 1 << n);
        } else if (m == 1) {
            return n;
        } else if (m == n - 1) {
            return ((long) 2 << n) - n;
        } else {
            final int j = choosePairToInt(n, m);
            if (j < CHOOSETABLESIZE) {
                return SUMCHOOSETABLE[j];
            }
            Assert.fail(EC.TLC_CHOOSE_UPPER_BOUND, String.valueOf(MAXCHOOSENUM));
            // make the compiler happy
            return Long.MIN_VALUE;
        }
    }

    public static int choosePairToInt(final int n, final int m) {
        return ((n - 3) * (n - 4)) / 2 + m - 2;
    }

    public static BigInteger toNum(final BigInteger[] B, final BigInteger[] N, final int len) {
        Assert.check((B.length >= len) && (len > 0), EC.SYSTEM_INDEX_ERROR);

        BigInteger num = N[len - 1];
        for (int i = len - 2; i >= 0; i--) {
            num = num.multiply(B[i]).add(N[i]);
        }
        return num;
    }

    public static BigInteger toNum(final BigInteger[] B, final BigInteger[] N) {
        return toNum(B, N, B.length);
    }

    public static BigInteger[] toSeq(final BigInteger[] B, final BigInteger n, final int len) {
        Assert.check((B.length >= len) && (len != 0), EC.SYSTEM_INDEX_ERROR);

        final BigInteger[] nlist = new BigInteger[len];
        BigInteger num = n;
        BigInteger base = B[0];
        nlist[0] = num.remainder(base);
        for (int i = 1; i < len; i++) {
            num = num.divide(base);
            base = B[i];
            nlist[i] = num.remainder(base);
        }
        return nlist;
    }

    public static BigInteger[] toSeq(final BigInteger[] B, final BigInteger n) {
        return toSeq(B, n, B.length);
    }

    public static BigInteger fact(final int n) {
        BigInteger result = BigInt.BigOne;

        for (int i = n; i > 1; i--)
            result = result.multiply(BigInteger.valueOf(i));
        return result;
    }

    public static BigInteger bigChoose(final int n, final int m) {
        if (n < MAXCHOOSENUM && m < MAXCHOOSENUM) {
            return BigInteger.valueOf(choose(n, m));
        }

        BigInteger binomial = BigInteger.ONE;
        for (int i = 1, j = n; i <= m; i++, j--) {
            final BigInteger bj = BigInteger.valueOf(j);
            final BigInteger bi = BigInteger.valueOf(i);
            binomial = binomial.multiply(bj).divide(bi);
        }
        return binomial;
    }

    public static BigInteger slowBigChoose(final int n, final int m) {
        final BigInteger num = fact(n);
        final BigInteger denom = fact(n - m).multiply(fact(m));

        return num.divide(denom);
    }

    public static BigInteger bigSumChoose(final int n, final int m) {
        BigInteger result;

        if ((n / 2) >= m) {
            result = BigInt.BigZero;
            for (int i = 0; i <= m; i++)
                result = result.add(bigChoose(n, i));
        } else {
            result = BigInt.BigOne;
            result = result.shiftLeft(n);
            for (int i = m + 1; i <= n; i++)
                result = result.subtract(bigChoose(n, i));
        }
        return result;
    }

    public static String print(final BigInteger[] A) {
        final StringBuilder sb = new StringBuilder();
        for (final BigInteger bigInteger : A) {
            sb.append(bigInteger.toString());
            sb.append(", ");
        }
        return new String(sb);
    }

    // https://blog.plover.com/math/choose.html
    public static long binomial(final int n, int k) {
        if (k > n) {
            return 0;
        }
        if (k > n - k) {
            // Optimize to n choose n - k.
            k = n - k;
        }

        long binomial = 1L;
        for (int i = 1, m = n; i <= k; i++, m--) {
            binomial = binomial * m / i;
        }
        return binomial;
    }

    public static long[] pascalTableUpTo(final int maxN, final int maxK) {
        if (maxN > MAXCHOOSENUM) {
            final long[] ppt = new long[((maxN - MAXCHOOSENUM) * (maxK - 1))];
            int idx = 0;

            // Initialize first "row" of extension table from existing triangle.
            int i = MAXCHOOSENUM + 1;
            for (int j = 2; j <= maxK; j++) {
                ppt[idx++] = choose(i, j);
            }
            // Subsequent rows initialize from previous row.
            final int k = maxK - 1;
            for (int j = 1; j < (maxN - MAXCHOOSENUM); j++) {
                for (int l = 0; l < k; l++) {
                    if (l == 0) {
                        ppt[idx] = i++ + ppt[idx - k];
                    } else {
                        ppt[idx] = ppt[idx - k] + ppt[idx - k - 1];
                    }
                    idx++;
                }
            }
            return ppt;
        }
        return new long[0];
    }


// SZ Jul 14, 2009: Dead code. not used.

}
