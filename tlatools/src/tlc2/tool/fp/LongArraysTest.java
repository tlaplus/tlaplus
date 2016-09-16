// Copyright (c) 2016 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;
import static tlc2.tool.fp.OffHeapDiskFPSet.EMPTY;

import org.junit.Test;

import tlc2.tool.fp.LongArrays.LongComparator;
import tlc2.tool.fp.LongArrays.PivotSelector;

public class LongArraysTest {

	@Test
	public void test1() {
		final long[] expected = new long[48];
		int i = 0;
		expected[i++] = 22102288204167208L;
		expected[i++] = 225160948165161873L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 810435887525385357L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 1638602644344629957L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 2068351286375637679L;
		expected[i++] = 0L;
		expected[i++] = 2528370576879701538L;
		expected[i++] = 2453870502940122045L;
		expected[i++] = 0L;
		expected[i++] = 3145830401686811393L;
		expected[i++] = 3192897355035876677L;
		expected[i++] = 3527505876050247287L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 4563398963865761585L;
		expected[i++] = 0L;
		expected[i++] = 4858869653769863593L;
		expected[i++] = 5180223017321191209L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 5635076245116608576L;
		expected[i++] = 5649139415351271641L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 6703691584433488410L;
		expected[i++] = 0L;
		expected[i++] = 7143040549630863225L;
		expected[i++] = 7205281130519852628L;
		expected[i++] = 7012967342342885117L;
		expected[i++] = 7709106021212022085L;
		expected[i++] = 7908712604546919197L;
		expected[i++] = 7246110956693059329L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 8781691546738212390L;
		expected[i++] = 8897195185152846807L;
		expected[i++] = 0L;

		doTest(expected);
	}

	@Test
	public void test2() {
		final long[] expected = new long[48];
		int i = 0;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 22102288204167208L;
		expected[i++] = 225160948165161873L;
		expected[i++] = 810435887525385357L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 1638602644344629957L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 2068351286375637679L;
		expected[i++] = 0L;
		expected[i++] = 2528370576879701538L;
		expected[i++] = 2453870502940122045L;
		expected[i++] = 0L;
		expected[i++] = 3145830401686811393L;
		expected[i++] = 3192897355035876677L;
		expected[i++] = 3527505876050247287L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 4563398963865761585L;
		expected[i++] = 0L;
		expected[i++] = 4858869653769863593L;
		expected[i++] = 5180223017321191209L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 5635076245116608576L;
		expected[i++] = 5649139415351271641L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 6703691584433488410L;
		expected[i++] = 0L;
		expected[i++] = 7143040549630863225L;
		expected[i++] = 7205281130519852628L;
		expected[i++] = 7012967342342885117L;
		expected[i++] = 7709106021212022085L;
		expected[i++] = 7908712604546919197L;
		expected[i++] = 7246110956693059329L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 8781691546738212390L;
		expected[i++] = 8897195185152846807L;
		expected[i++] = 0L;

		doTest(expected);
	}

	@Test
	public void test3() {
		final long[] expected = new long[87];
		int i = 0;
		expected[i++] = 9183932681676589496L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 329728050397015749L;
		expected[i++] = 436139026681109109L;
		expected[i++] = 556905678415593173L;
		expected[i++] = 0L;
		expected[i++] = 796460649423573389L;
		expected[i++] = 797798112015065380L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 1632374027957690827L;
		expected[i++] = 1756811852021281877L;
		expected[i++] = 0L;
		expected[i++] = 1881448932687659007L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 2342821865031748924L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 2736147834640710575L;
		expected[i++] = 2864022862265935958L;
		expected[i++] = 2773542629236699928L;
		expected[i++] = 2957298868366608281L;
		expected[i++] = 0L;
		expected[i++] = 3330257111892751888L;
		expected[i++] = 3295675356431597478L;
		expected[i++] = 3395836867027940583L;
		expected[i++] = 3681469222400184316L;
		expected[i++] = 3754947896063147473L;
		expected[i++] = 3698681814958844261L;
		expected[i++] = 3951382885893085878L;
		expected[i++] = 0L;
		expected[i++] = 4188454649677385650L;
		expected[i++] = 4129247165607948084L;
		expected[i++] = 4365409305525871332L;
		expected[i++] = 4526757821913904014L;
		expected[i++] = 4254202026550171921L;
		expected[i++] = 4557871951994955815L;
		expected[i++] = 4806497834029622101L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 5236202638577037427L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 5936146187640212534L;
		expected[i++] = 0L;
		expected[i++] = 6127434886073515781L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 6547025209145878563L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 6931928829149329960L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 7244186580741581738L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 7634041392899269082L;
		expected[i++] = 7590982629575593986L;
		expected[i++] = 0L;
		expected[i++] = 7954723745221262664L;
		expected[i++] = 0L;
		expected[i++] = 8156105620374757718L;
		expected[i++] = 8305398393196381769L;
		expected[i++] = 8318253237689249492L;
		expected[i++] = 8487954051864981042L;
		expected[i++] = 8411933954485687818L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 9175849669163144218L;
		
		doTest(expected);
	}
	
	@Test
	public void test4() {
		final long[] expected = new long[87];
		int i = 0;
		expected[i++] = 9195197379878056627L;
		expected[i++] = 74236458333421747L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 481170446028802552L;
		expected[i++] = 587723185270146839L;
		expected[i++] = 0L;
		expected[i++] = 764880467681476738L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 1028380228728529428L;
		expected[i++] = 0L;
		expected[i++] = 1246117495100367611L;
		expected[i++] = 1353681884824400499L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 1963327988900916594L;
		expected[i++] = 0L;
		expected[i++] = 2157942654452711468L;
		expected[i++] = 2211701751588391467L;
		expected[i++] = 2197266581704230150L;
		expected[i++] = 2391118405386569995L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 2754416910109403115L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 3528296600587602855L;
		expected[i++] = 0L;
		expected[i++] = 3766154305485605955L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 4172091881329434331L;
		expected[i++] = 4273360576593753745L;
		expected[i++] = 4338054185482857322L;
		expected[i++] = 4487790251341705673L;
		expected[i++] = 0L;
		expected[i++] = 4760603841378765728L;
		expected[i++] = 0L;
		expected[i++] = 4897534821030901381L;
		expected[i++] = 5057347369431494228L;
		expected[i++] = 5185984701076703188L;
		expected[i++] = 5255556356599253415L;
		expected[i++] = 4911921657882287345L;
		expected[i++] = 5512811886280168498L;
		expected[i++] = 5627022814159167180L;
		expected[i++] = 5630009759945037387L;
		expected[i++] = 5592096823142754761L;
		expected[i++] = 5880489878946290534L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 6796173646113527960L;
		expected[i++] = 6887096685265647763L;
		expected[i++] = 6946033094922439935L;
		expected[i++] = 7100083311060830826L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 7575172208974668528L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 8240485391672917634L;
		expected[i++] = 0L;
		expected[i++] = 0L;
		expected[i++] = 8572429495433200993L;
		expected[i++] = 0L;
		expected[i++] = 8804495173596718076L;
		expected[i++] = 8771524479740786626L;
		expected[i++] = 8986659781390119011L;
		expected[i++] = 9136953010061430590L;
		expected[i++] = 9017810141411942826L;		
		
		doTest(expected);
	}

	private void doTest(final long[] expected) {
		final LongArray array = new LongArray(expected.length);
		for (int j = 0; j < expected.length; j++) {
			array.set(j, expected[j]);
		}

		LongArrays.sort(array, 0, array.size() - 1L, new LongComparator() {
			public int compare(long lo, long loPos, long hi, long hiPos) {
				if (lo <= 0 || hi <= 0) {
					return 0;
				} else if (lo < hi) {
					return -1;
				} else {
					return 1;
				}
			}
		}, new PivotSelector() {
			public long getPos(LongArray a, long left, long right) {
				long mid = ((left + right) >>> 1)  % a.size();
				// Select the closest element such that \in Nat \ {0} to mid as pivot.
				for (int i = 0; i < (mid >>> 1); i++) {
					if (a.get(mid + i) > 0) {
						mid = mid + i;
						break;
					}
					if (a.get(mid - i) > 0) {
						mid = mid - i;
						break;
					}
				}
				return mid;
			}
		});

		OUTER: for (int j = 0; j < expected.length; j++) {
			final long l = expected[j];
			if (l == EMPTY) {
				assertEquals(EMPTY, array.get(j));
			} else if (l < EMPTY) {
				assertEquals(l, array.get(j));
			} else {
				for (int k = 0; k < array.size(); k++) {
					if (array.get(k) == l) {
						continue OUTER;
					}
				}
				fail(String.format("long %s not found.", l));
			}
		}
	}
}