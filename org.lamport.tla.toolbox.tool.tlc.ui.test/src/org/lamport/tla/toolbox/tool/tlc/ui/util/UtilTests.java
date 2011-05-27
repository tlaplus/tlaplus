package org.lamport.tla.toolbox.tool.tlc.ui.util;

import junit.framework.Test;
import junit.framework.TestSuite;

public class UtilTests
{

    public static Test suite()
    {
        TestSuite suite = new TestSuite("Test for org.lamport.tla.toolbox.tool.tlc.ui.util");
        // $JUnit-BEGIN$
        suite.addTestSuite(ParsingToolkitTest.class);
        suite.addTestSuite(FormHelperTest.class);
        suite.addTestSuite(SemanticHelperTest.class);
        // $JUnit-END$
        return suite;
    }

}
