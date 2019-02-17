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
package tlc2.value.impl;

import org.openjdk.jmh.annotations.Benchmark;
import org.openjdk.jmh.annotations.Scope;
import org.openjdk.jmh.annotations.State;

import tlc2.TLCGlobals;
import tlc2.util.FP64;
import tlc2.value.RandomEnumerableValues;
import tlc2.value.impl.Enumerable;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.IntervalValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.SetOfFcnsValue;
import tlc2.value.impl.SubsetValue;

@State(Scope.Benchmark)
public class RandomizationBenchmark {

	private static final Enumerable enum016;
	private static final Enumerable enum032;
	private static final Enumerable enum064;
	private static final Enumerable enum128;
	private static final Enumerable enum256;
	private static final Enumerable enum512;
	private static final Enumerable enum1024;
	private static final Enumerable enum2048;
	private static final Enumerable enum4096;
	private static final Enumerable enum8192;
	private static final Enumerable enum16384;
	private static final Enumerable enum32768;
	private static final Enumerable enumTLCBound;
	
	private static final Enumerable interval16;
	private static final Enumerable interval20;
	private static final Enumerable interval24;
	private static final Enumerable interval28;
	private static final Enumerable interval31;

	private static final int twoPow12 = (int) (Math.pow(2, 12) - 1);
	private static final int twoPow08 = (int) (Math.pow(2, 8) - 1);
	private static final int twoPow16 = (int) (Math.pow(2, 16) - 1);
	private static final Enumerable fcns008x008; // 2^24
	private static final Enumerable fcns011x011; // ~2^31
	private static final Enumerable fcns016x008;
	private static final Enumerable fcns016x016; // ~2^65
	private static final Enumerable fcns032x016;
	private static final Enumerable fcns032x032; // ~2^150
	private static final Enumerable fcns048x048; // ~2^268

	private static final SubsetValue subset2pow24; // 2^24
	private static final SubsetValue subset2pow31; // ~2^31
	private static final SubsetValue subset2pow65; // ~2^65
	private static final SubsetValue subset2pow150; // ~2^150
	private static final SubsetValue subset2pow268; // ~2^268
	
	private static ValueVec getValues(int from, int to) {
		final ValueVec vec = new ValueVec(to - from);
		for (int i = from; i <= to; i++) {
			vec.addElement(IntValue.gen(i));
		}
		return vec;
	}

	static {
		RandomEnumerableValues.setSeed(15041980L);
		RandomEnumerableValues.reset();

		FP64.Init();

		enum016 = new SetEnumValue(getValues(1, 16), true);
		enum032 = new SetEnumValue(getValues(1, 32), true);
		enum064 = new SetEnumValue(getValues(1, 64), true);
		enum128 = new SetEnumValue(getValues(1, 128), true);
		enum256 = new SetEnumValue(getValues(1, 256), true);
		enum512 = new SetEnumValue(getValues(1, 512), true);
		enum1024 = new SetEnumValue(getValues(1, 1024), true);
		enum2048 = new SetEnumValue(getValues(1, 2048), true);
		enum4096 = new SetEnumValue(getValues(1, 4096), true);
		enum8192 = new SetEnumValue(getValues(1, 8192), true);
		enum16384 = new SetEnumValue(getValues(1, 16384), true);
		enum32768 = new SetEnumValue(getValues(1, 32768), true);
		enumTLCBound = new SetEnumValue(getValues(1, TLCGlobals.setBound), true);

		interval16 = new IntervalValue(0, 2 << 16);
		interval20 = new IntervalValue(0, 2 << 20);
		interval24 = new IntervalValue(0, 2 << 24);
		interval28 = new IntervalValue(0, 2 << 28);
		interval31 = new IntervalValue(0, Integer.MAX_VALUE); // maximum possible value for internal ValueVec
		
		fcns008x008 = new SetOfFcnsValue(new SetEnumValue(getValues(1, 8), true),
				new SetEnumValue(getValues(1, 8), true));
		fcns011x011 = new SetOfFcnsValue(new SetEnumValue(getValues(1, 11), true),
				new SetEnumValue(getValues(1, 11), true));
		fcns016x008 = new SetOfFcnsValue(new SetEnumValue(getValues(1, 16), true),
				new SetEnumValue(getValues(1, 8), true));
		fcns016x016 = new SetOfFcnsValue(new SetEnumValue(getValues(1, 16), true),
				new SetEnumValue(getValues(1, 16), true));
		fcns032x016 = new SetOfFcnsValue(new SetEnumValue(getValues(1, 32), true),
				new SetEnumValue(getValues(1, 16), true));
		fcns032x032 = new SetOfFcnsValue(new SetEnumValue(getValues(1, 32), true),
				new SetEnumValue(getValues(1, 32), true));
		fcns048x048 = new SetOfFcnsValue(new SetEnumValue(getValues(1, 48), true),
				new SetEnumValue(getValues(1, 48), true));
		
		subset2pow24 = new SubsetValue(new IntervalValue(1, 24));
		subset2pow31 = new SubsetValue(new IntervalValue(1, 31));
		subset2pow65 = new SubsetValue(new IntervalValue(1, 65));
		subset2pow150 = new SubsetValue(new IntervalValue(1, 150));
		subset2pow268 = new SubsetValue(new IntervalValue(1, 268));
	}
	
	/* exact */
	
	@Benchmark
	public Enumerable randomSetOfSubsetExact024k008() {
		return subset2pow24.getRandomSetOfSubsets(twoPow08, 10);
	}

	@Benchmark
	public Enumerable randomSetOfSubsetExact024k012() {
		return subset2pow24.getRandomSetOfSubsets(twoPow12, 10);
	}

	@Benchmark
	public Enumerable randomSetOfSubsetExact024k016() {
		return subset2pow24.getRandomSetOfSubsets(twoPow16, 10);
	}

	@Benchmark
	public Enumerable randomSetOfSubsetExact031k008() {
		return subset2pow31.getRandomSetOfSubsets(twoPow08, 10);
	}

	@Benchmark
	public Enumerable randomSetOfSubsetExact031k012() {
		return subset2pow31.getRandomSetOfSubsets(twoPow12, 10);
	}

	@Benchmark
	public Enumerable randomSetOfSubsetExact031k016() {
		return subset2pow31.getRandomSetOfSubsets(twoPow16, 10);
	}

	@Benchmark
	public Enumerable randomSetOfSubsetExact65k008() {
		return subset2pow65.getRandomSetOfSubsets(twoPow08, 10);
	}

	@Benchmark
	public Enumerable randomSetOfSubsetExact065k012() {
		return subset2pow65.getRandomSetOfSubsets(twoPow12, 10);
	}

	@Benchmark
	public Enumerable randomSetOfSubsetExact065k016() {
		return subset2pow65.getRandomSetOfSubsets(twoPow16, 10);
	}

	@Benchmark
	public Enumerable randomSetOfSubsetExact150k008() {
		return subset2pow150.getRandomSetOfSubsets(twoPow08, 10);
	}

	@Benchmark
	public Enumerable randomSetOfSubsetExact150k012() {
		return subset2pow150.getRandomSetOfSubsets(twoPow12, 10);
	}

	@Benchmark
	public Enumerable randomSetOfSubsetExact150k016() {
		return subset2pow150.getRandomSetOfSubsets(twoPow16, 10);
	}

	@Benchmark
	public Enumerable randomSetOfSubsetExact268k008() {
		return subset2pow268.getRandomSetOfSubsets(twoPow08, 10);
	}

	@Benchmark
	public Enumerable randomSetOfSubsetExact268k012() {
		return subset2pow268.getRandomSetOfSubsets(twoPow12, 10);
	}

	@Benchmark
	public Enumerable randomSetOfSubsetExact268k016() {
		return subset2pow268.getRandomSetOfSubsets(twoPow16, 10);
	}
	
	/* probabilistic */
	
	@Benchmark
	public Enumerable randomSetOfSubset024k008() {
		return subset2pow24.getRandomSetOfSubsets(twoPow08, .1d);
	}

	@Benchmark
	public Enumerable randomSetOfSubset024k012() {
		return subset2pow24.getRandomSetOfSubsets(twoPow12, .1d);
	}

	@Benchmark
	public Enumerable randomSetOfSubset024k016() {
		return subset2pow24.getRandomSetOfSubsets(twoPow16, .1d);
	}

	@Benchmark
	public Enumerable randomSetOfSubset031k008() {
		return subset2pow31.getRandomSetOfSubsets(twoPow08, .1d);
	}

	@Benchmark
	public Enumerable randomSetOfSubset031k012() {
		return subset2pow31.getRandomSetOfSubsets(twoPow12, .1d);
	}

	@Benchmark
	public Enumerable randomSetOfSubset031k016() {
		return subset2pow31.getRandomSetOfSubsets(twoPow16, .1d);
	}

	@Benchmark
	public Enumerable randomSetOfSubset065k008() {
		return subset2pow65.getRandomSetOfSubsets(twoPow08, .1d);
	}

	@Benchmark
	public Enumerable randomSetOfSubset065k012() {
		return subset2pow65.getRandomSetOfSubsets(twoPow12, .1d);
	}

	@Benchmark
	public Enumerable randomSetOfSubset065k016() {
		return subset2pow65.getRandomSetOfSubsets(twoPow16, .1d);
	}

	@Benchmark
	public Enumerable randomSetOfSubset150k008() {
		return subset2pow150.getRandomSetOfSubsets(twoPow08, .1d);
	}

	@Benchmark
	public Enumerable randomSetOfSubset150k012() {
		return subset2pow150.getRandomSetOfSubsets(twoPow12, .1d);
	}

	@Benchmark
	public Enumerable randomSetOfSubset150k016() {
		return subset2pow150.getRandomSetOfSubsets(twoPow16, .1d);
	}

	@Benchmark
	public Enumerable randomSetOfSubset268k008() {
		return subset2pow268.getRandomSetOfSubsets(twoPow08, .1d);
	}

	@Benchmark
	public Enumerable randomSetOfSubset268k012() {
		return subset2pow268.getRandomSetOfSubsets(twoPow12, .1d);
	}

	@Benchmark
	public Enumerable randomSetOfSubset268k016() {
		return subset2pow268.getRandomSetOfSubsets(twoPow16, .1d);
	}
	
	/* IntervalValue */
	
	@Benchmark
	public Enumerable randomInterval016setBound() {
		return interval16.getRandomSubset(TLCGlobals.setBound);
	}
	
	@Benchmark
	public Enumerable randomInterval020setBound() {
		return interval20.getRandomSubset(TLCGlobals.setBound);
	}
	
	@Benchmark
	public Enumerable randomInterval024setBound() {
		return interval24.getRandomSubset(TLCGlobals.setBound);
	}
	
	@Benchmark
	public Enumerable randomInterval028setBound() {
		return interval28.getRandomSubset(TLCGlobals.setBound);
	}
	
	@Benchmark
	public Enumerable randomInterval031setBound() {
		return interval31.getRandomSubset(TLCGlobals.setBound);
	}
	
	@Benchmark
	public Enumerable randomIntervalt016all() {
		return interval16.getRandomSubset(interval16.size() - 1);
	}
	
	@Benchmark
	public Enumerable randomInterval020all() {
		return interval20.getRandomSubset(interval20.size() - 1);
	}
	
	@Benchmark
	public Enumerable randomInterval024all() {
		return interval24.getRandomSubset(interval24.size() - 1);
	}
	
	@Benchmark
	public Enumerable randomIntervalt016half() {
		return interval16.getRandomSubset(interval16.size() / 2);
	}
	
	@Benchmark
	public Enumerable randomInterval020half() {
		return interval20.getRandomSubset(interval20.size() / 2);
	}
	
	@Benchmark
	public Enumerable randomInterval024half() {
		return interval24.getRandomSubset(interval24.size() / 2);
	}
	
	/* SetEnumValue */
	
	@Benchmark
	public Enumerable randomSubset016() {
		return enum016.getRandomSubset(enum016.size() - 1);
	}

	@Benchmark
	public Enumerable randomSubset032() {
		return enum032.getRandomSubset(enum032.size() - 1);
	}

	@Benchmark
	public Enumerable randomSubset064() {
		return enum064.getRandomSubset(enum064.size() - 1);
	}

	@Benchmark
	public Enumerable randomSubset128() {
		return enum128.getRandomSubset(enum128.size() - 1);
	}

	@Benchmark
	public Enumerable randomSubset256() {
		return enum256.getRandomSubset(enum256.size() - 1);
	}

	@Benchmark
	public Enumerable randomSubset512() {
		return enum512.getRandomSubset(enum512.size() - 1);
	}

	@Benchmark
	public Enumerable randomSubset1024() {
		return enum1024.getRandomSubset(enum1024.size() - 1);
	}

	@Benchmark
	public Enumerable randomSubset2048() {
		return enum2048.getRandomSubset(enum2048.size() - 1);
	}

	@Benchmark
	public Enumerable randomSubset4096() {
		return enum4096.getRandomSubset(enum4096.size() - 1);
	}

	@Benchmark
	public Enumerable randomSubset8192() {
		return enum8192.getRandomSubset(enum8192.size() - 1);
	}

	@Benchmark
	public Enumerable randomSubset16384() {
		return enum16384.getRandomSubset(enum16384.size() - 1);
	}

	@Benchmark
	public Enumerable randomSubset32768() {
		return enum32768.getRandomSubset(enum32768.size() - 1);
	}

	@Benchmark
	public Enumerable randomSubsetTLCBound() {
		return enumTLCBound.getRandomSubset(enumTLCBound.size() - 1);
	}
	
	/* randomSubset with SetOfFcns */

	@Benchmark
	public Enumerable randomSubsetFcns008x008p16() {
		return fcns008x008.getRandomSubset(twoPow16);
	}

	@Benchmark
	public Enumerable randomSubsetFcns008x008p08() {
		return fcns008x008.getRandomSubset(twoPow08);
	}

	@Benchmark
	public Enumerable randomSubsetFcns008x008p12() {
		return fcns008x008.getRandomSubset(twoPow12);
	}

	@Benchmark
	public Enumerable randomSubsetFcns011x011p16() {
		return fcns008x008.getRandomSubset(twoPow16);
	}

	@Benchmark
	public Enumerable randomSubsetFcns011x011p08() {
		return fcns011x011.getRandomSubset(twoPow08);
	}

	@Benchmark
	public Enumerable randomSubsetFcns011x011p12() {
		return fcns011x011.getRandomSubset(twoPow12);
	}
	
	@Benchmark
	public Enumerable randomSubsetFcns016x008p16() {
		return fcns011x011.getRandomSubset(twoPow16);
	}

	@Benchmark
	public Enumerable randomSubsetFcns016x008p08() {
		return fcns016x008.getRandomSubset(twoPow08);
	}

	@Benchmark
	public Enumerable randomSubsetFcns016x008p12() {
		return fcns016x008.getRandomSubset(twoPow12);
	}

	@Benchmark
	public Enumerable randomSubsetFcns016x016p16() {
		return fcns016x016.getRandomSubset(twoPow16);
	}

	@Benchmark
	public Enumerable randomSubsetFcns016x016p08() {
		return fcns016x016.getRandomSubset(twoPow08);
	}

	@Benchmark
	public Enumerable randomSubsetFcns016x016p12() {
		return fcns016x016.getRandomSubset(twoPow12);
	}

	@Benchmark
	public Enumerable randomSubsetFcns032x016p16() {
		return fcns032x016.getRandomSubset(twoPow16);
	}

	@Benchmark
	public Enumerable randomSubsetFcns032x016p08() {
		return fcns032x016.getRandomSubset(twoPow08);
	}

	@Benchmark
	public Enumerable randomSubsetFcns032x016p12() {
		return fcns032x016.getRandomSubset(twoPow12);
	}

	@Benchmark
	public Enumerable randomSubsetFcns032x032p16() {
		return fcns032x032.getRandomSubset(twoPow16);
	}

	@Benchmark
	public Enumerable randomSubsetFcns032x032p08() {
		return fcns032x032.getRandomSubset(twoPow08);
	}

	@Benchmark
	public Enumerable randomSubsetFcns032x032p12() {
		return fcns032x032.getRandomSubset(twoPow12);
	}

	@Benchmark
	public Enumerable randomSubsetFcns048x048p16() {
		return fcns048x048.getRandomSubset(twoPow16);
	}

	@Benchmark
	public Enumerable randomSubsetFcns048x048p08() {
		return fcns048x048.getRandomSubset(twoPow08);
	}

	@Benchmark
	public Enumerable randomSubsetFcns048x048p12() {
		return fcns048x048.getRandomSubset(twoPow12);
	}
}
