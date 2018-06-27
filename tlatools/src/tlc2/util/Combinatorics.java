// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tlc2.util;

import java.math.BigInteger;

import tlc2.output.EC;
import util.Assert;

public class Combinatorics {

  public static final int MAXCHOOSENUM = 62;
	public static final int CHOOSETABLESIZE = (MAXCHOOSENUM - 3) * (MAXCHOOSENUM - 4) / 2 + MAXCHOOSENUM - 3;
	public static long[] CHOOSETABLE = new long[CHOOSETABLESIZE];
  private static long[] SUMCHOOSETABLE = new long[CHOOSETABLESIZE];

  public static long choose(int n, int m) {
		if (n < 0 || m < 0) {
    Assert.check(((m >= 0) && (n >= 0) && (n >= m)), EC.TLC_CHOOSE_ARGUMENTS_WRONG, "choose");
		}
		if (m == 0 || m == n) {
      return (long)1;
		} else if (m == 1 || m == n - 1) {
      return (long)n;
		} else if (n == 0 || m > n) {
			// Cannot choose from zero elements or more elements than present.
			return 0;
		} else {
      int j = choosePairToInt(n, m);
      if (j < CHOOSETABLESIZE) {
	return CHOOSETABLE[j];
      }
			return binomial(n, m); // calculate on demand
    }
  }

	public static long sumChoose(int n, int m) {
      Assert.check(((m>=0) && (n>=0) && (n>=m)), EC.TLC_CHOOSE_ARGUMENTS_WRONG, "sumChoose");
		if (m == 0) {
          return (long)1;
		} else if (m == n) {
          return ((long)1 << n);
		} else if (m == 1) {
          return (long)n;
		} else if (m == n - 1) {
          return ((long)2 << n) - n;
		} else {
          int j = choosePairToInt(n,m);
			if (j < CHOOSETABLESIZE) {
              return SUMCHOOSETABLE[j];
          }
          Assert.fail(EC.TLC_CHOOSE_UPPER_BOUND, String.valueOf(MAXCHOOSENUM));
          // make the compiler happy
          return Long.MIN_VALUE;
      }
  }
	     
	public static int choosePairToInt(int n, int m) {
    return ((n-3)*(n-4))/2 + m -2;
  }

  static {
    int i, n, m;
    long sum;
    
    n = 4;
    m = 2;
    sum = 5;
    for (i = 0; i < CHOOSETABLESIZE; i++) {
      CHOOSETABLE[i] = choose(n-1,m)+choose(n-1,m-1);
      sum += CHOOSETABLE[i];
      SUMCHOOSETABLE[i] = sum;
      if (n == m+2) {
	n++;
	m = 2;
	sum = 1+n;
			} else
	m++;
    }
  }

  public static BigInteger toNum(BigInteger[] B, BigInteger[] N, int len) {
    Assert.check((B.length >= len) && (len > 0), EC.SYSTEM_INDEX_ERROR);

    BigInteger num = N[len-1];
    for (int i = len-2; i >= 0; i--) {
      num = num.multiply(B[i]).add(N[i]);
    }
    return num;
  }
  
  public static BigInteger toNum(BigInteger[] B, BigInteger[] N) {
    return toNum(B, N, B.length);
  }

  public static BigInteger[] toSeq(BigInteger[] B, BigInteger n, int len) {
    Assert.check((B.length >= len) && (len != 0), EC.SYSTEM_INDEX_ERROR);

    BigInteger[] nlist = new BigInteger[len];
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
  
  public static BigInteger[] toSeq(BigInteger[] B, BigInteger n) {
    return toSeq(B, n, B.length);
  }

  public static BigInteger fact(int n) {
    BigInteger result = BigInt.BigOne;

    for (int i = n; i > 1; i--)
      result = result.multiply(BigInteger.valueOf(i));
    return result;
  }

  public static BigInteger bigChoose(int n, int m) {
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
	
	public static BigInteger slowBigChoose(int n, int m) {
    BigInteger num = fact(n);
    BigInteger denom = fact(n - m).multiply(fact(m));

    return num.divide(denom);
  }

  public static BigInteger bigSumChoose(int n, int m) {
    BigInteger result;

    if ((n/2) >= m) {
      result = BigInt.BigZero;
      for (int i = 0; i <= m; i++) 
	result = result.add(bigChoose(n, i));
		} else {
      result = BigInt.BigOne;
      result = result.shiftLeft(n);
      for (int i = m+1; i <= n; i++) 
	result = result.subtract(bigChoose(n, i));
    }
    return result;
  }

  public static String print (BigInteger[] A) {
    StringBuffer sb = new StringBuffer();
    for (int i=0; i<A.length; i++) {
      sb.append(A[i].toString());
      sb.append(", ");
    }
    return new String(sb);
  }

	// https://blog.plover.com/math/choose.html
	public static final long binomial(int n, int k) {
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
//  public static void main(String argv[]) {
//    int i,j;
//    BigInteger b;
//    // Date d1,d2;
//    // SZ Feb 24, 2009: not used
//    BigInteger [] A = new BigInteger[16];
//    BigInteger [] B = new BigInteger[16];
//    BigInteger [] C;
//    Random r = new Random();
//
//    
//    for (i=0; i<8; i++) {
//      B[2*i] = BigInteger.valueOf(1048576);
//      B[2*i+1] = BigInteger.valueOf(1024);
//    }
//
//    
//    for (j = 0; j < 200; j++) {
//      for (i = 0; i < 8; i++) {
//	A[2*i] = new BigInteger(20, r);
//	A[2*i+1] = new BigInteger(10, r);
//      }
//      ToolIO.out.println("A is "+print(A));
//      b = toNum(B, A);
//      C = toSeq(B, b);
//      ToolIO.out.println("C is "+print(C));
//      for (i = 0; i < 16; i++)
//	if (!C[i].equals(A[i]))
//	    ToolIO.out.println("***********Error***********");
//      ToolIO.out.println("b is " + b);
//    }      
//  }

}
