package org.lamport.tla.toolbox.tool.tlc;

import junit.framework.Test;
import junit.framework.TestSuite;

import org.lamport.tla.toolbox.tool.tlc.output.data.DataTests;
import org.lamport.tla.toolbox.tool.tlc.ui.util.UtilTests;

public class AllTests
{

    public static Test suite()
    {
        TestSuite suite = new TestSuite("Test for org.lamport.tla.toolbox.tool.tlc");
        // $JUnit-BEGIN$
        suite.addTest(DataTests.suite());
        suite.addTest(UtilTests.suite());
        // $JUnit-END$
        return suite;
    }

}
