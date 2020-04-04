package org.lamport.tla.toolbox.tool.tlc.output.data;

import junit.framework.Test;
import junit.framework.TestSuite;

public class DataTests
{

    public static Test suite()
    {
        TestSuite suite = new TestSuite("Test for org.lamport.tla.toolbox.tool.tlc.output.data");
        // $JUnit-BEGIN$
        suite.addTestSuite(TLCVariableValueTest.class);
        // $JUnit-END$
        return suite;
    }

}
