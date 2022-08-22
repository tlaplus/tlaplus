// Copyright (c) 2022, Oracle and/or its affiliates.

package tlc2.tool;

import org.junit.Test;
import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

import static org.junit.Assert.assertTrue;

public class ConstantOperatorConfigurationTest extends ModelCheckerTestCase {

    public ConstantOperatorConfigurationTest() {
        super("ConstantOperatorConfiguration", "", EC.ExitStatus.VIOLATION_SAFETY);
    }

    @Test
    public void testSpec() {
        assertTrue(recorder.recorded(EC.TLC_FINISHED));
        assertTrue(recorder.recordedWithStringValue(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR, "Inv"));
    }

}
