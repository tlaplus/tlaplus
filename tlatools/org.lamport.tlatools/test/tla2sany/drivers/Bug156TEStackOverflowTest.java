package tla2sany.drivers;

import org.junit.Before;
import org.junit.Test;
import tla2sany.modanalyzer.SpecObj;
import util.SimpleFilenameToStream;
import util.ToolIO;

/**
 * @see <a href="../../general/bugzilla/index.html">Bug #156 </a>
 */
public class Bug156TEStackOverflowTest {

    /**
     *
     */
    @Before
    public void setUp() throws Exception {
        // create a model and initialize
        SpecObj moduleSpec = new SpecObj("test-model/Bug156/TE.tla", new SimpleFilenameToStream());
        var sany = new SANY();
        sany.frontEndInitialize(moduleSpec, ToolIO.out);
    }

    /**
     * Test method for {@link tla2sany.drivers.SANY#frontEndParse(tla2sany.modanalyzer.SpecObj, java.io.PrintStream)}.
     */
    @Test
    public void testFrontEndParse() {
        // uncomment if bug 156 has been fixed
//        try {
//			SANY.frontEndParse(moduleSpec, ToolIO.out);
//		} catch (StackOverflowError e) {
//			fail("StackOverflow must not happen");
//		}
    }
}
