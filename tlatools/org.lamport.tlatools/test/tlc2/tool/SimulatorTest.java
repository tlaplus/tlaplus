package tlc2.tool;

import org.junit.Test;

import tlc2.debug.StandaloneConstExpressionDebugger;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.impl.DebugTool;
import tlc2.util.RandomGenerator;
import util.Assert;
import util.SimpleFilenameToStream;

import java.io.IOException;
import java.util.HashMap;

import static org.junit.Assert.assertTrue;

public class SimulatorTest extends CommonTestCase {

    @Test
    public void testPrintBehaviorShouldPrintErrorState() throws IOException {
        MP.setRecorder(recorder);
        Simulator simulator = new Simulator(new DebugTool(BASE_PATH + "Github726", BASE_PATH + "Github726", new SimpleFilenameToStream(),
                new HashMap<>(), new StandaloneConstExpressionDebugger()), null,
                "", false, -1, 0, null,
                new RandomGenerator(0), 0, new SimpleFilenameToStream(), 0);
        simulator.printBehavior(new Assert.TLCRuntimeException("TestException"), TLCStateMut.Empty.createEmpty(), new StateVec(0));
        assertTrue(recorder.recorded(EC.TLC_ERROR_STATE));
    }

}
