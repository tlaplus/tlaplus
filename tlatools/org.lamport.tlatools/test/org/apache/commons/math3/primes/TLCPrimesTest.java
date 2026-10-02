package org.apache.commons.math3.primes;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.junit.Test;

public class TLCPrimesTest {

	@Test
	public void testAgreesWithPrimesOnInt() {
		for (int n = 2; n < 100_000; n++) {
			assertAgrees(n);
		}
		for (long n = Integer.MAX_VALUE - 100_000; n <= Integer.MAX_VALUE; n++) {
			assertAgrees((int) n);
		}
	}

	@Test
	public void testBeyondInt() {
		// 2^31 + 1 = 3 * 715827883
		assertEquals(List.of(3L, 715827883L), TLCPrimes.primeFactors(2147483649L));
		// 2^31 + 2 = 2 * 5^2 * 13 * 41 * 61 * 1321
		assertEquals(List.of(2L, 5L, 5L, 13L, 41L, 61L, 1321L), TLCPrimes.primeFactors(2147483650L));
		// A semi prime of two primes beyond SmallPrimes.PRIMES_LAST.
		assertEquals(List.of(3673L, 3677L), TLCPrimes.primeFactors(3673L * 3677L));
		for (long n = TLCPrimes.MAX_FACTORIZABLE - 100_000; n <= TLCPrimes.MAX_FACTORIZABLE; n++) {
			assertFactorization(n);
		}
	}

	@Test(expected = MathIllegalArgumentException.class)
	public void testTooSmall() {
		TLCPrimes.primeFactors(1);
	}

	@Test(expected = MathIllegalArgumentException.class)
	public void testTooLarge() {
		TLCPrimes.primeFactors(TLCPrimes.MAX_FACTORIZABLE + 1);
	}

	private static void assertAgrees(final int n) {
		final List<Long> expected = new ArrayList<>();
		for (Integer p : Primes.primeFactors(n)) {
			expected.add((long) p);
		}
		assertEquals(expected, TLCPrimes.primeFactors(n));
	}

	private static void assertFactorization(final long n) {
		long product = 1;
		long previous = 1;
		for (Long p : TLCPrimes.primeFactors(n)) {
			assertTrue(n + ": " + p + " is not prime", BigInteger.valueOf(p).isProbablePrime(64));
			assertTrue(n + ": factors out of order", previous <= p);
			previous = p;
			product *= p;
		}
		assertEquals(n, product);
	}
}
