// Copyright (c) 2016 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;
import static tlc2.tool.fp.OffHeapDiskFPSet.EMPTY;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.junit.Assume;
import org.junit.Before;
import org.junit.Test;

import tlc2.tool.fp.LongArrays.LongComparator;
import tlc2.tool.fp.OffHeapDiskFPSet.Indexer;

public class LongArraysTest {
	
	@Before
	public void setup() {
		Assume.assumeTrue(LongArray.isSupported());
	}

	@Test
	public void testEmpty1() {
		doTest(new long[] {0L}, 1L, 0, new OffHeapDiskFPSet.Indexer(0, 1));
	}
	
	@Test
	public void testEmpty2() {
		final long[] expected = {0L, 0L, 0L, 0L};
		doTest(expected, 1L, 2, new OffHeapDiskFPSet.Indexer(expected.length, 1));
	}
	
	@Test
	public void testBasic1() {
		final long[] expected = {5L, 8L, 1L, 7L, 0L, 3L};
		final LongArray array = new LongArray(expected);
		LongArrays.sort(array);
		
		// This amounts to a regular/basic insertion sort because there are no
		// sentinels in the array. doTest fails for this array, because the
		// indices calculated by the indexer are invalid.
		for (int i = 1; i < array.size(); i++) {
			assertTrue(array.get(i - 1L) < array.get(i));
		}
	}

	@Test
	public void testBasic2() {
		final long[] expected = {
			74236458333421747L,
			9185197375878056627L,
			9017810141411942826L,
			481170446028802552L,
			587723185270146839L,
			764880467681476738L,
			1028380228728529428L,
			1246117495100367611L,
			1353681884824400499L,
			1963327988900916594L,
			2157942654452711468L,
			2211701751588391467L,
			2197266581704230150L,
			2391118405386569995L,
			2754416910109403115L,
			3528296600587602855L,
			3766154305485605955L,
			4172091881329434331L,
			4273360576593753745L,
			4338054185482857322L,
			4487790251341705673L,
			4760603841378765728L,
			4897534821030901381L,
			5057347369431494228L,
			5185984701076703188L,
			5255556356599253415L,
			4911921657882287345L,
			5512811886280168498L,
			5627022814159167180L,
			5630009759945037387L,
			5592096823142754761L,
			5880489878946290534L,
			6796173646113527960L,
			6887096685265647763L,
			6946033094922439935L,
			7100083311060830826L,
			7575172208974668528L,
			8240485391672917634L,
			8572429495433200993L,
			8804495173596718076L,
			8771524479740786626L,
			8986659781390119011L,
			9136953010061430590L,
			9195197379878056627L
		};

		final LongArray array = new LongArray(expected);
		LongArrays.sort(array);
		
		// This amounts to a regular/basic insertion sort because there are no
		// sentinels in the array. doTest fails for this array, because the
		// indices calculated by the indexer are invalid.
		for (int i = 1; i < array.size(); i++) {
			assertTrue(array.get(i - 1L) < array.get(i));
		}
	}

	@Test
	public void test0() {
		final long[] expected = {
			22102288204167208L,
			225160948165161873L,
			0L,
			1638602644344629957L,
			1644442600000000000L,
			0L
		};

		doTest(expected, 1L, 3, new OffHeapDiskFPSet.Indexer(expected.length, 1));
	}
	
	@Test
	public void test1() {
		final long[] expected = {
			22102288204167208L,
			225160948165161873L,
			0L,
			0L,
			810435887525385357L,
			0L,
			0L,
			0L,
			1638602644344629957L,
			0L,
			0L,
			2068351286375637679L,
			0L,
			2528370576879701538L,
			2453870502940122045L,
			0L,
			3145830401686811393L,
			3192897355035876677L,
			3527505876050247287L,
			0L,
			0L,
			0L,
			0L,
			4563398963865761585L,
			0L,
			4858869653769863593L,
			5180223017321191209L,
			0L,
			0L,
			5635076245116608576L,
			5649139415351271641L,
			0L,
			0L,
			0L,
			6703691584433488410L,
			0L,
			7143040549630863225L,
			7205281130519852628L,
			7012967342342885117L,
			7709106021212022085L,
			7908712604546919197L,
			7246110956693059329L,
			0L,
			0L,
			0L,
			8781691546738212390L,
			8897195185152846807L,
			0L
		};

		doTest(expected);
	}

	@Test
	public void test2() {
		final long[] expected = {
			0L,
			0L,
			22102288204167208L,
			225160948165161873L,
			810435887525385357L,
			0L,
			0L,
			0L,
			1638602644344629957L,
			0L,
			0L,
			2068351286375637679L,
			0L,
			2528370576879701538L,
			2453870502940122045L,
			0L,
			3145830401686811393L,
			3192897355035876677L,
			3527505876050247287L,
			0L,
			0L,
			0L,
			0L,
			4563398963865761585L,
			0L,
			4858869653769863593L,
			5180223017321191209L,
			0L,
			0L,
			5635076245116608576L,
			5649139415351271641L,
			0L,
			0L,
			0L,
			6703691584433488410L,
			0L,
			7143040549630863225L,
			7205281130519852628L,
			7012967342342885117L,
			7709106021212022085L,
			7908712604546919197L,
			7246110956693059329L,
			0L,
			0L,
			0L,
			8781691546738212390L,
			8897195185152846807L,
			0L
		};

		doTest(expected);
	}

	@Test
	public void test3() {
		final long[] expected = {
			9183932681676589496L,
			0L,
			0L,
			329728050397015749L,
			436139026681109109L,
			556905678415593173L,
			0L,
			796460649423573389L,
			797798112015065380L,
			0L,
			0L,
			0L,
			0L,
			0L,
			0L,
			1632374027957690827L,
			1756811852021281877L,
			0L,
			1881448932687659007L,
			0L,
			0L,
			0L,
			2342821865031748924L,
			0L,
			0L,
			0L,
			2736147834640710575L,
			2864022862265935958L,
			2773542629236699928L,
			2957298868366608281L,
			0L,
			3330257111892751888L,
			3295675356431597478L,
			3395836867027940583L,
			3681469222400184316L,
			3754947896063147473L,
			3698681814958844261L,
			3951382885893085878L,
			0L,
			4188454649677385650L,
			4129247165607948084L,
			4365409305525871332L,
			4526757821913904014L,
			4254202026550171921L,
			4557871951994955815L,
			4806497834029622101L,
			0L,
			0L,
			0L,
			5236202638577037427L,
			0L,
			0L,
			0L,
			0L,
			0L,
			5936146187640212534L,
			0L,
			6127434886073515781L,
			0L,
			0L,
			0L,
			6547025209145878563L,
			0L,
			0L,
			0L,
			6931928829149329960L,
			0L,
			0L,
			7244186580741581738L,
			0L,
			0L,
			7634041392899269082L,
			7590982629575593986L,
			0L,
			7954723745221262664L,
			0L,
			8156105620374757718L,
			8305398393196381769L,
			8318253237689249492L,
			8487954051864981042L,
			8411933954485687818L,
			0L,
			0L,
			0L,
			0L,
			0L,
			9175849669163144218L
		};
		
		doTest(expected);
	}
	
	@Test
	public void test4() {
		final long[] expected = {
			9136953010061430590L,
			74236458333421747L,
			0L,
			0L,
			481170446028802552L,
			587723185270146839L,
			0L,
			764880467681476738L,
			0L,
			0L,
			1028380228728529428L,
			0L,
			1246117495100367611L,
			1353681884824400499L,
			0L,
			0L,
			0L,
			0L,
			1963327988900916594L,
			0L,
			2157942654452711468L,
			2211701751588391467L,
			2197266581704230150L,
			2391118405386569995L,
			0L,
			0L,
			2754416910109403115L,
			0L,
			0L,
			0L,
			0L,
			0L,
			0L,
			3528296600587602855L,
			0L,
			3766154305485605955L,
			0L,
			0L,
			0L,
			4172091881329434331L,
			4273360576593753745L,
			4338054185482857322L,
			4487790251341705673L,
			0L,
			4760603841378765728L,
			0L,
			4897534821030901381L,
			5057347369431494228L,
			5185984701076703188L,
			5255556356599253415L,
			4911921657882287345L,
			5512811886280168498L,
			5627022814159167180L,
			5630009759945037387L,
			5592096823142754761L,
			5880489878946290534L,
			0L,
			0L,
			0L,
			0L,
			0L,
			0L,
			0L,
			6796173646113527960L,
			6887096685265647763L,
			6946033094922439935L,
			7100083311060830826L,
			0L,
			0L,
			0L,
			0L,
			7575172208974668528L,
			0L,
			0L,
			0L,
			0L,
			0L,
			8240485391672917634L,
			0L,
			0L,
			8572429495433200993L,
			0L,
			8804495173596718076L,
			8771524479740786626L,
			8986659781390119011L,
			9017810141411942826L,
			9195197379878056627L
		};
		
		doTest(expected);
	}

	@Test
	public void test5() {
		final long[] expected = {
			9185197375878056627L,
			74236458333421747L,
			9017810141411942826L,
			0L,
			481170446028802552L,
			587723185270146839L,
			0L,
			764880467681476738L,
			0L,
			0L,
			1028380228728529428L,
			0L,
			1246117495100367611L,
			1353681884824400499L,
			0L,
			0L,
			0L,
			0L,
			1963327988900916594L,
			0L,
			2157942654452711468L,
			2211701751588391467L,
			2197266581704230150L,
			2391118405386569995L,
			0L,
			0L,
			2754416910109403115L,
			0L,
			0L,
			0L,
			0L,
			0L,
			0L,
			3528296600587602855L,
			0L,
			3766154305485605955L,
			0L,
			0L,
			0L,
			4172091881329434331L,
			4273360576593753745L,
			4338054185482857322L,
			4487790251341705673L,
			0L,
			4760603841378765728L,
			0L,
			4897534821030901381L,
			5057347369431494228L,
			5185984701076703188L,
			5255556356599253415L,
			4911921657882287345L,
			5512811886280168498L,
			5627022814159167180L,
			5630009759945037387L,
			5592096823142754761L,
			5880489878946290534L,
			0L,
			0L,
			0L,
			0L,
			0L,
			0L,
			0L,
			6796173646113527960L,
			6887096685265647763L,
			6946033094922439935L,
			7100083311060830826L,
			0L,
			0L,
			0L,
			0L,
			7575172208974668528L,
			0L,
			0L,
			0L,
			0L,
			0L,
			8240485391672917634L,
			0L,
			0L,
			8572429495433200993L,
			0L,
			8804495173596718076L,
			8771524479740786626L,
			8986659781390119011L,
			9136953010061430590L,
			9195197379878056627L
		};
		
		doTest(expected);
	}
	
	@Test
	public void test6() {
		final long[] expected = {
			1L,
			9185197375878056627L,
			9017810141411942826L,
			0L,
			481170446028802552L,
			587723185270146839L,
			0L,
			764880467681476738L,
			0L,
			0L,
			1028380228728529428L,
			0L,
			1246117495100367611L,
			1353681884824400499L,
			0L,
			0L,
			0L,
			0L,
			1963327988900916594L,
			0L,
			2157942654452711468L,
			2211701751588391467L,
			2197266581704230150L,
			2391118405386569995L,
			0L,
			0L,
			2754416910109403115L,
			0L,
			0L,
			0L,
			0L,
			0L,
			0L,
			3528296600587602855L,
			0L,
			3766154305485605955L,
			0L,
			0L,
			0L,
			4172091881329434331L,
			4273360576593753745L,
			4338054185482857322L,
			4487790251341705673L,
			0L,
			4760603841378765728L,
			0L,
			4897534821030901381L,
			5057347369431494228L,
			5185984701076703188L,
			5255556356599253415L,
			4911921657882287345L,
			5512811886280168498L,
			5627022814159167180L,
			5630009759945037387L,
			5592096823142754761L,
			5880489878946290534L,
			0L,
			0L,
			0L,
			0L,
			0L,
			0L,
			0L,
			6796173646113527960L,
			6887096685265647763L,
			6946033094922439935L,
			7100083311060830826L,
			0L,
			0L,
			0L,
			0L,
			7575172208974668528L,
			0L,
			0L,
			0L,
			0L,
			0L,
			8240485391672917634L,
			0L,
			0L,
			8572429495433200993L,
			0L,
			8804495173596718076L,
			8771524479740786626L,
			8986659781390119011L,
			9136953010061430590L,
			9195197379878056627L
		};
		
		doTest(expected);
	}
	
	@Test
	public void test7() {
		final long[] expected = {
			1L,
			0L,
			4L,
			0L,
			6L,
			0L,
			0L,
			0L,
			0L,
			0L,
			13L
		};
		
		doTest(expected, 1, 0, new OffHeapDiskFPSet.Indexer(expected.length, 1, 13));
	}
	
	@Test
	public void test8() {
		final long[] expected = {
			1L,
			11L,
			3L,
			4L,
			5L,
			6L,
			7L,
			8L,
			9L,
			10L,
			12L
		};
		
		final OffHeapDiskFPSet.Indexer indexer = new OffHeapDiskFPSet.Indexer(expected.length, 1, 12);
		final LongArray array = new LongArray(expected);
		final LongComparator comparator = getComparator(indexer);
		LongArrays.sort(array, 0, array.size() - 1L + 3, comparator);
		verify(expected, 3, indexer, array);

	}
	
	@Test
	public void test9a() {
		final long[] expected = {
			12L,
			1L,
			0L,
			0L,
			0L,
			11L
		};
		
		doTest(expected, 1, 2, new OffHeapDiskFPSet.Indexer(expected.length, 1, 13));
	}
	
	@Test
	public void test9b() {
		final long[] expected = {
			11L,
			1L,
			0L,
			0L,
			0L,
			12L
		};
		
		doTest(expected, 1, 2, new OffHeapDiskFPSet.Indexer(expected.length, 1, 13));
	}
	
	@Test
	public void test9c() {
		final long[] expected = {
			1L,
			12L,
			0L,
			0L,
			0L,
			11L
		};
		
		doTest(expected, 1, 3, new OffHeapDiskFPSet.Indexer(expected.length, 1, 13));
	}
	
	private void doTest(final long[] expected) {
		final Indexer indexer = new OffHeapDiskFPSet.Indexer(expected.length, 1);
		for (int i = 1; i < (expected.length / 2); i++) {
			doTest(expected, i, 2, indexer);
		}
	}
	
	private void doTest(final long[] expected, final long partitions, final int reprobe, final Indexer indexer) {
		final LongArray array = new LongArray(expected);
		final LongComparator comparator = getComparator(indexer);
		final long length = expected.length / partitions;
		
		// Sort each disjunct partition.
		for (long i = 0; i < partitions; i++) {
			final long start = i * length;
			final long end = i + 1L == partitions ? array.size() - 1L: start + length;
			LongArrays.sort(array, start, end, comparator);
		}
		// Stitch the disjunct partitions together. Only need if more than one
		// partition, but done with one partition anyway to see that it causes
		// no harm.
		for (long i = 0; i < partitions; i++) {
			final long end = getEnd(partitions, array, length, i);
			LongArrays.sort(array, end - reprobe, end + reprobe, comparator);
		}
		
		verify(expected, reprobe, indexer, array);
	}

	private long getEnd(final long partitions, final LongArray array, final long length, long idx) {
		return idx + 1L == partitions ? array.size() - 1L: (idx + 1L) * length;
	}

	private static LongComparator getComparator(final Indexer indexer) {
		return new LongComparator() {
			public int compare(final long fpA, final long posA, final long fpB, final long posB) {
				// Elements not in Nat \ {0} remain at their current
				// position.
				if (fpA <= EMPTY || fpB <= EMPTY) {
					return 0;
				}
				
				final boolean wrappedA = indexer.getIdx(fpA) > posA;
				final boolean wrappedB = indexer.getIdx(fpB) > posB;
				
				if (wrappedA == wrappedB && posA > posB) {
					return fpA < fpB ? -1 : 1;
				} else if ((wrappedA ^ wrappedB)) {
					if (posA < posB && fpA < fpB) {
						// Swap fpB, which is at the end of array a, with fpA.
						// fpA is less than fpB. fpB was inserted into array a
						// before fpA.
						return -1;
					}
					if (posA > posB && fpA > fpB) {
						return -1;
					}
				}
				return 0;
			}
		};
	}

	private void verify(final long[] expected, final int reprobe, final Indexer indexer, final LongArray array) {
		// Verify that negative and EMPTY elements remain at their position.
		// Lets call them sentinels.
		int sentinel = 0;
		OUTER: for (int j = 0; j < expected.length; j++) {
			final long l = expected[j];
			if (l == EMPTY) {
				// EMPTY remain at their original positions.
				assertEquals(EMPTY, array.get(j));
				sentinel++;
			} else if (l < EMPTY) {
				// Negative remain at their original positions.
				assertEquals(l, array.get(j));
				sentinel++;
			} else {
				// Verify that all non-sentinels are still
				// array members.
				for (int k = 0; k < array.size(); k++) {
					if (array.get(k) == l) {
						continue OUTER;
					}
				}
				fail(String.format("long %s not found.", l));
			}
		}
		
		// Verify elements stayed within their lookup range.
		for (int pos = 0; pos < array.size(); pos++) {
			final long l = array.get(pos);
			if (l <= EMPTY) {
				continue;
			}
			final long idx = indexer.getIdx(l);
			assertTrue(String.format("%s, pos: %s, idx: %s, r: %s (was at: %s)", l, pos, idx, reprobe,
					Arrays.asList(expected).indexOf(l)), isInRange(idx, reprobe, pos, array.size()));
		}
		
		// Verify that non-sentinels are sorted is ascending order. Take
		// care of wrapped elements too. A) First find the first non-sentinel,
		// non-wrapped element.
		long pos = 0;
		final List<Long> seen = new ArrayList<Long>(expected.length);
		while (pos < array.size()) {
			long e = array.get(pos);
			if (e <= EMPTY || indexer.getIdx(e) > pos) {
				// Either sentinel or wrapped.
				pos++;
				continue;
			}
			seen.add(e);
			pos++;
			break;
		}
		// B) Collect all elements into seen but skip those at the beginning that
		// wrapped, and those that didn't wrap at the end (array.size + reprobe).
		for (; pos < array.size() + reprobe; pos++) {
			long actual = array.get(pos % array.size());
			if (actual <= EMPTY) {
				continue;
			}
			final long idx = indexer.getIdx(actual);
			if (pos < array.size() && idx > pos) {
				// When not wrapped, ignore elements belonging to the end that wrapped.
				continue;
			}
			if (pos > array.size() - 1L && idx + reprobe < pos) {
				// When wrapped, ignore elements at beginning which do not
				// belong to the end.
				continue;
			}
			seen.add(actual);
		}
		// C) Verify that all elements are sorted.
		for (int i = 1; i < seen.size(); i++) {
			final long lo = seen.get(i - 1);
			final long hi = seen.get(i);
			assertTrue(String.format("%s > %s", lo, hi), lo < hi);
		}
		// D) Verify we saw all expected elements.
		assertEquals(expected.length - sentinel, seen.size());
	}
	
	@Test
	public void testIsInRange() {
		assertTrue(isInRange(0, 0, 0, 4));

		assertFalse(isInRange(0, 0, 1, 4));
		assertFalse(isInRange(0, 0, 2, 4));
		assertFalse(isInRange(0, 0, 3, 4));
		assertFalse(isInRange(0, 0, 4, 4));

		assertTrue(isInRange(0, 1, 1, 4));
		assertFalse(isInRange(0, 1, 2, 4));
		assertTrue(isInRange(0, 2, 2, 4));
		assertFalse(isInRange(0, 2, 3, 4));
		assertTrue(isInRange(0, 3, 3, 4));
		assertFalse(isInRange(0, 3, 4, 4));
		
		assertTrue(isInRange(3, 0, 3, 4));
		assertTrue(isInRange(3, 1, 0, 4));
		assertTrue(isInRange(3, 2, 1, 4));
		assertFalse(isInRange(3, 2, 2, 4));
	}

	private static boolean isInRange(long idx, int reprobe, int pos, long size) {
		if (idx + reprobe >= size && pos < idx) {
			return pos <= (idx + reprobe) % size;
		} else {
			return idx <= pos && pos <= idx + reprobe;
		}
	}
}
