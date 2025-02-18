// Copyright (c) 2025, Oracle and/or its affiliates.
package tlc2.tool;

import org.junit.Assert;
import org.junit.Test;
import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class Github1145Test extends ModelCheckerTestCase {

    public Github1145Test() {
        super("Github1145", new String[] {}, EC.ExitStatus.SUCCESS);
    }

    @Test
    public void testSpec() {
        Assert.assertTrue(recorder.recorded(EC.TLC_FINISHED));
    }

}
