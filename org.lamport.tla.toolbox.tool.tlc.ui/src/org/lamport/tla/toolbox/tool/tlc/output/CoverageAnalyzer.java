package org.lamport.tla.toolbox.tool.tlc.output;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.TypedRegion;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class CoverageAnalyzer
{
    private static final String COVERAGE = LogPartitionTokenScanner.COVERAGE;
    private ITypedRegion start = null;
    private ITypedRegion end = null;
    private ITypedRegion coverage = null;
    private final boolean failOnError;

    /**
     * Constructs the analyzer
     * @param failOnError a flag indicating that the analyzer will fail if the start and end 
     * are not set in the interleaving manner. 
     */
    public CoverageAnalyzer(boolean failOnError)
    {
        this.failOnError = failOnError;
    }

    /**
     * Add start of coverage
     * @param start
     */
    public void addCoverageStart(ITypedRegion start)
    {
        if (failOnError)
        {
            Assert.isTrue(this.start == null || this.start.getOffset() == start.getOffset(), "Assertion error in coverage analyzer. "
                    + "The start of the coverage is detected twice without a end of coverage between them.");
        }
        this.start = start;
    }

    /**
     * Add the end of coverage
     * @param end
     */
    public void addCoverageEnd(ITypedRegion end)
    {
        if (failOnError)
        {
            Assert.isTrue(this.end == null || this.end.getOffset() == end.getOffset(), "Assertion error in coverage analyzer. "
                    + "The end of the coverage is detected twice without a end of coverage between them.");
        }
        this.end = end;
        processCoverage();
    }

    /**
     * Process the calculation of the coverage region
     */
    protected void processCoverage()
    {
        int length = this.end.getOffset() + this.end.getLength() - this.start.getOffset();
        this.coverage = new TypedRegion(this.start.getOffset(), length, CoverageAnalyzer.COVERAGE);

        // reseting the regions
        this.start = null;
        this.end = null;
    }

    /**
     * Retrieves last detected coverage region, or null if no coverage information were available
     * @return
     */
    public ITypedRegion getCoverageRegion()
    {
        return this.coverage;
    }
}
