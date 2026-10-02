/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.commons.math3.primes;

import java.util.ArrayList;
import java.util.List;

import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.util.TLCFastMath;

/**
 * {@link Primes#primeFactors(int)} and {@link SmallPrimes#trialDivision(int)}
 * for <code>long</code> up to {@link #MAX_FACTORIZABLE}.
 */
public class TLCPrimes {

    /**
     * The cube of {@link SmallPrimes#PRIMES_LAST}. Without its factors in
     * {@link SmallPrimes#PRIMES}, a number up to this bound is either a prime or
     * a semi prime, as {@link #boundedTrialDivision(long, long, List)} requires.
     */
    public static final long MAX_FACTORIZABLE =
            (long) SmallPrimes.PRIMES_LAST * SmallPrimes.PRIMES_LAST * SmallPrimes.PRIMES_LAST;

    /**
     * Hide utility class.
     */
    private TLCPrimes() {
    }

    /**
     * Prime factors decomposition
     *
     * @param n number to factorize: must be &ge; 2 and &le; {@link #MAX_FACTORIZABLE}
     * @return list of prime factors of n
     * @throws MathIllegalArgumentException if n &lt; 2 or n &gt; {@link #MAX_FACTORIZABLE}.
     */
    public static List<Long> primeFactors(long n) {

        if (n < 2) {
            throw new MathIllegalArgumentException(LocalizedFormats.NUMBER_TOO_SMALL, n, 2);
        }
        if (n > MAX_FACTORIZABLE) {
            throw new MathIllegalArgumentException(LocalizedFormats.NUMBER_TOO_LARGE, n, MAX_FACTORIZABLE);
        }
        return trialDivision(n);

    }

    /**
     * Extract small factors.
     * @param n the number to factor, must be &gt; 0.
     * @param factors the list where to add the factors.
     * @return the part of n which remains to be factored, it is either a prime or a semi-prime
     */
    static long smallTrialDivision(long n, final List<Long> factors) {
        for (int p : SmallPrimes.PRIMES) {
            while (0 == n % p) {
                n /= p;
                factors.add((long) p);
            }
        }
        return n;
    }

    /**
     * Extract factors in the range <code>PRIME_LAST+2</code> to <code>maxFactors</code>.
     * @param n the number to factorize, must be >= PRIME_LAST+2 and must not contain any factor below PRIME_LAST+2
     * @param maxFactor the upper bound of trial division: if it is reached, the method gives up and returns n.
     * @param factors the list where to add the factors.
     * @return  n or 1 if factorization is completed.
     */
    static long boundedTrialDivision(long n, long maxFactor, List<Long> factors) {
        long f = SmallPrimes.PRIMES_LAST + 2;
        // no check is done about n >= f
        while (f <= maxFactor) {
            if (0 == n % f) {
                n /= f;
                factors.add(f);
                break;
            }
            f += 4;
            if (0 == n % f) {
                n /= f;
                factors.add(f);
                break;
            }
            f += 2;
        }
        if (n != 1) {
            factors.add(n);
        }
        return n;
    }

    /**
     * Factorization by trial division.
     * @param n the number to factor
     * @return the list of prime factors of n
     */
    static List<Long> trialDivision(long n) {
        final List<Long> factors = new ArrayList<Long>(32);
        n = smallTrialDivision(n, factors);
        if (1 == n) {
            return factors;
        }
        // here we are sure that n is either a prime or a semi prime
        final long bound = (long) TLCFastMath.sqrt(n);
        boundedTrialDivision(n, bound, factors);
        return factors;
    }
}
