/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved.
 *
 * The MIT License (MIT)
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tlc2.util;

import static org.junit.Assert.assertEquals;

import java.math.BigInteger;

import org.junit.Test;

public class CombinatoricsTest {
	@Test
	public void testChoose() {
		for (int n = 0; n < Combinatorics.MAXCHOOSENUM; n++) {
			for (int k = 0; k < Combinatorics.MAXCHOOSENUM; k++) {
				long choose = Combinatorics.choose(n, k);
				long binomial = Combinatorics.binomial(n, k);
				assertEquals(String.format("n=%s, k=%s", n, k), choose, binomial);
			}
		}
	}
	@Test
	public void testChooseBigChoose() {
		for (int n = 0; n < Combinatorics.MAXCHOOSENUM + 1; n++) {
			for (int k = 0; k < Combinatorics.MAXCHOOSENUM + 1; k++) {
				long choose = Combinatorics.choose(n, k);
				long bigChoose = Combinatorics.bigChoose(n, k).longValueExact();
				assertEquals(String.format("n=%s, k=%s", n, k), choose, bigChoose);
			}
		}
	}
	@Test
	public void testSlowChooseBigChoose() {
		for (int n = Combinatorics.MAXCHOOSENUM + 1; n < Combinatorics.MAXCHOOSENUM << 2; n++) {
			for (int k = Combinatorics.MAXCHOOSENUM + 1; k < Combinatorics.MAXCHOOSENUM << 2; k++) {
				BigInteger slowBigChoose = Combinatorics.slowBigChoose(n, k);
				BigInteger bigChoose = Combinatorics.bigChoose(n, k);
				assertEquals(String.format("n=%s, k=%s", n, k), slowBigChoose, bigChoose);
			}
		}
	}
	@Test
	public void testBigChoose50c1() {
		final BigInteger bigChoose = Combinatorics.bigChoose(50, 1);
		assertEquals(6, bigChoose.bitLength());
		assertEquals(50L, bigChoose.longValueExact());
	}
	@Test
	public void testBigChoose50c10() {
		final BigInteger bigChoose = Combinatorics.bigChoose(50, 10);
		assertEquals(34, bigChoose.bitLength());
		assertEquals(10272278170L, bigChoose.longValueExact());
	}
	@Test
	public void testBigChoose50c20() {
		final BigInteger bigChoose = Combinatorics.bigChoose(50, 20);
		assertEquals(46, bigChoose.bitLength());
		assertEquals(47129212243960L, bigChoose.longValueExact());
	}
	@Test
	public void testBigChoose50c30() {
		final BigInteger bigChoose = Combinatorics.bigChoose(50, 30);
		assertEquals(46, bigChoose.bitLength());
		assertEquals(47129212243960L, bigChoose.longValueExact());
	}
	@Test
	public void testBigChoose400c1() {
		final BigInteger bigChoose = Combinatorics.bigChoose(400, 1);
		assertEquals(9, bigChoose.bitLength());
		assertEquals(400L, bigChoose.longValueExact());
	}
	@Test
	public void testBigChoose400c50() {
		final BigInteger bigChoose = Combinatorics.bigChoose(400, 50);
		assertEquals(214, bigChoose.bitLength());
		assertEquals(
				"17035900270730601418919867558071677342938596450600561760371485120",
				bigChoose.toString());
	}
	@Test
	public void testBigChoose400c100() {
		final BigInteger bigChoose = Combinatorics.bigChoose(400, 100);
		assertEquals(321, bigChoose.bitLength());
		assertEquals(
				"2241854791554337561923210387201698554845411177476295990399942258896013007429693894018935107174320",
				bigChoose.toString());
	}
	@Test
	public void testBigChoose400c200() {
		final BigInteger bigChoose = Combinatorics.bigChoose(400, 200);
		assertEquals(396, bigChoose.bitLength());
		assertEquals(
				"102952500135414432972975880320401986757210925381077648234849059575923332372651958598336595518976492951564048597506774120",
				bigChoose.toString());
	}
}
