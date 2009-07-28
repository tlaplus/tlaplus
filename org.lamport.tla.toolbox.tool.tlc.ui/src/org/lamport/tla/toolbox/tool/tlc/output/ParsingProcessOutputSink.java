package org.lamport.tla.toolbox.tool.tlc.output;

import java.util.Vector;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.TypedRegion;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;

/**
 * Parses data coming from the process
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ParsingProcessOutputSink extends CachingTLCOutputSource implements IProcessOutputSink
{
    private int lastPartitionEnd;
    private String processName;
    private CoverageAnalyzer analyzer = new CoverageAnalyzer(true);

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink#appendText(java.lang.String)
     */
    public void appendText(String text)
    {
        try
        {
            document.replace(document.getLength(), 0, text);
            IDocumentPartitioner partitioner = document.getDocumentPartitioner();

            int startOfUnpartitionedText = Math.min(document.getLength(), lastPartitionEnd);

            System.out.println("Parsing from " + startOfUnpartitionedText + " to " + document.getLength());
            ITypedRegion[] regions = partitioner.computePartitioning(startOfUnpartitionedText, document.getLength());

            // iterate partitions from the end to the front, and looking for the last
            // non-default (user-output) partition
            Vector userTempPartitions = new Vector();
            for (int i = 0; i < regions.length; i++)
            {
                // looking for non-default content type
                if (!LogPartitionTokenScanner.DEFAULT_CONTENT_TYPE.equals(regions[i].getType()))
                {
                    // typed partition detected
                    int currentPartitionEnd = regions[i].getOffset() + regions[i].getLength();
                    if (currentPartitionEnd > lastPartitionEnd)
                    {
                        lastPartitionEnd = currentPartitionEnd;
                    }

                    
                    if (LogPartitionTokenScanner.COVERAGE_START.equals(regions[i].getType()))
                    {
                        // just add the partition to the analyzer 
                        analyzer.addCoverageStart(regions[i]);
                    } 
                    
                    
                    if (LogPartitionTokenScanner.COVERAGE_END.equals(regions[i].getType())) 
                    {
                        // if the coverage end is detected, everything between the start and 
                        // the end are not user partitions, but 
                        // coverage information
                        analyzer.addCoverageEnd(regions[i]);
                        
                        ITypedRegion coverage = analyzer.getCoverageRegion();
                        // add the typed coverage region
                        onOutput(coverage);
                        
                        // re-initialize the user partitions
                        userTempPartitions = new Vector();
                    } else
                    {

                        // user partitions found
                        if (userTempPartitions.size() > 1)
                        {
                            int startLine = document.getLineOfOffset(((TypedRegion) userTempPartitions.elementAt(0))
                                    .getOffset());
                            int endLine = document.getLineOfOffset(((TypedRegion) userTempPartitions
                                    .elementAt(userTempPartitions.size() - 1)).getOffset());
                            ITypedRegion mergedPartition = PartitionToolkit
                                    .mergePartitions((ITypedRegion[]) userTempPartitions
                                            .toArray(new TypedRegion[userTempPartitions.size()]));
                            System.out.println("Merged " + userTempPartitions.size() + " user partitions. Lines from "
                                    + startLine + " to " + endLine + ".");
                            onOutput(mergedPartition);
                            PartitionToolkit.printPartition(mergedPartition, document);
                            
                            // re-initialize the user partitions                            
                            userTempPartitions = new Vector();
                        }

                        // the partition after the user partition
                        onOutput(regions[i]);

                    }
                } else
                {
                    // if the partition has no type (default one), it is the user partition...
                    userTempPartitions.add(regions[i]);
                }
            }

        } catch (BadLocationException e)
        {
            TLCUIActivator.logError("Error parsing the TLC output stream for " + this.processName, e);
        }
    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink#initializeSink(java.lang.String, int)
     */
    public void initializeSink(String processName, int sinkType)
    {
        this.processName = processName;
        this.document = new Document();
        FastPartitioner partitioner = new FastPartitioner(new LogPartitionTokenScanner(),
                LogPartitionTokenScanner.CONTENT_TYPES);
        partitioner.connect(document);
        this.document.setDocumentPartitioner(partitioner);
        
        // register the process source
        TLCOutputSourceRegistry.getStatusRegistry().addTLCStatusSource(this, processName);
    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink#processFinished()
     */
    public void processFinished()
    {
        onDone();
    }

}
