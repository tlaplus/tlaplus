package tlc2.module;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class ConstantContextTLCCacheTest extends ModelCheckerTestCase {
	public ConstantContextTLCCacheTest() {
		super("ConstantContextTLCCache");
	}
	
	@Test
	public void test() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "2", "1", "0"));
		assertFalse(recorder.recorded(EC.GENERAL));
	}
}
