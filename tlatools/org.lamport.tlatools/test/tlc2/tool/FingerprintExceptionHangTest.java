// Copyright (c) 2023, Oracle and/or its affiliates.

package tlc2.tool;

import org.junit.Test;
import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * Regression test for an infinite loop in {@link FingerprintException#asTrace()}.
 */
public class FingerprintExceptionHangTest extends ModelCheckerTestCase {

    public FingerprintExceptionHangTest() {
        super("FingerprintExceptionHang", EC.ExitStatus.FAILURE_SPEC_EVAL);
    }

    @Test
    public void testSpec() {
        assertTrue(recorder.recorded(EC.TLC_FINISHED));
        assertFalse(recorder.recorded(EC.GENERAL));

        String arg1 = "0. Line 16, column 5 to line 16, column 46 in FingerprintExceptionHang\n" +
                "1. Line 16, column 20 to line 16, column 46 in FingerprintExceptionHang\n" +
                "2. Line 16, column 30 to line 16, column 45 in FingerprintExceptionHang\n\n";
        String arg2 = "Attempted to compare integer 1 with non-integer:\n{}";
        assertTrue(recorder.recordedWithStringValues(EC.TLC_FINGERPRINT_EXCEPTION, arg1, arg2));
    }
}
