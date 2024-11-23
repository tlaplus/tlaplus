package tlc2.tool;

import static org.junit.Assert.assertTrue;

import java.io.IOException;
import java.util.HashMap;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.impl.FastTool;
import tlc2.util.RandomGenerator;
import util.Assert;
import util.SimpleFilenameToStream;

public class SimulatorTest extends CommonTestCase {

    @Test
    public void testPrintBehaviorShouldPrintErrorState() throws IOException {
        MP.setRecorder(recorder);
        Simulator simulator = new Simulator(new FastTool(BASE_PATH + "Github726", BASE_PATH + "Github726", new SimpleFilenameToStream(),
                new HashMap<>()), null,
                "", false, -1, 0, null,
                new RandomGenerator(0), 0, new SimpleFilenameToStream(), 0);
        final StateVec stateVec = new StateVec(1);
        stateVec.addElement(TLCStateMut.Empty.createEmpty());
		simulator.printBehavior(new Assert.TLCRuntimeException("TestException"), stateVec);
        assertTrue(recorder.recorded(EC.TLC_ERROR_STATE));
    }

}
