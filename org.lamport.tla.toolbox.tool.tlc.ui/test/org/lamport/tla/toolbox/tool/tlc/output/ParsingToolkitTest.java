package org.lamport.tla.toolbox.tool.tlc.output;

import junit.framework.TestCase;

import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.TypedRegion;
import org.lamport.tla.toolbox.tool.tlc.output.PartitionToolkit;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ParsingToolkitTest extends TestCase
{

    /* (non-Javadoc)
     * @see junit.framework.TestCase#setUp()
     */
    protected void setUp() throws Exception
    {
        super.setUp();
    }

    /**
     * Test method for {@link org.lamport.tla.toolbox.tool.tlc.output.ParsingTLCOutputSink#mergePartitions(org.eclipse.jface.text.ITypedRegion[])}.
     */
    public void testMergePartitions()
    {
        assertEquals(new TypedRegion(0, 100, "type"), PartitionToolkit.mergePartitions(new ITypedRegion[] {
                new TypedRegion(0, 10, "type"), new TypedRegion(10, 80, "type"), new TypedRegion(90, 10, "type") }));
    }

    public void testMergePartitions2()
    {
        assertEquals(new TypedRegion(0, 100, "type"), PartitionToolkit
                .mergePartitions(new ITypedRegion[] { new TypedRegion(0, 100, "type") }));
    }

}
