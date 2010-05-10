package org.lamport.tla.toolbox.tool.prover.ui.output;

import org.eclipse.core.runtime.IPath;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.DocumentPartitioningChangedEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentPartitioningListener;
import org.eclipse.jface.text.IDocumentPartitioningListenerExtension2;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ObligationStatusMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.TLAPMMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.source.CachingTLAPMOutputSource;
import org.lamport.tla.toolbox.tool.prover.ui.output.source.ITLAPMOutputSource;
import org.lamport.tla.toolbox.tool.prover.ui.output.source.TLAPMOutputSourceRegistry;

import tla2sany.st.Location;

/**
 * Parser for TLAPM output.
 * 
 * On initialization, this class creates a new {@link IDocument}
 * and an {@link TagBasedTLAPMOutputTokenScanner} to partition that document.
 * As TLAPM output streams in, the text is appended to the document, and the
 * token scanner computes the new partitions for the TLAPM output. See the
 * description of {@link TagBasedTLAPMOutputTokenScanner} for what partitions
 * are created, but one type of partition is for obligation (or step) status
 * information. Thus, some of the partitions describe the region of text in the
 * TLAPM output that corresponds to a line with obligation (or step) status
 * information.
 * 
 * In order to learn about these partitions as they are computed, this class has
 * a nested class {@link TLAPMDocumentPartioningListener} for listening
 * to changes in the partitioning of the document containing TLAPM output.
 * When this class receives notification of new partitions, it uses the partitions
 * to create instances of {@link ITLAPMData} to pass to the {@link ITLAPMOutputSource}
 * for this parser.
 * 
 * @author Daniel Ricketts
 *@deprecated
 */
public class TagBasedTLAPMOutputIncrementalParser
{

    /**
     * Document containing output from the TLAPM
     */
    private IDocument document;
    /**
     * Source to which instances of {@link ITLAPMData}
     * are passed by this parser.
     */
    private ITLAPMOutputSource source;
    /**
     * Full file system path to the module whose
     * TLAPM output this parser is parsing.
     */
    private IPath modulePath;

    /**
     * Listens to changes in the partitioning of the document
     * that contains output from the TLAPM.
     * 
     * It uses these partitions to create {@link ITLAPMData} to 
     * pass to the {@link ITLAPMOutputSource} for this parser.
     * 
     * For example, when it encounters a partition corresponding
     * to an obligation status line, it creates an {@link ObligationStatusMessage}
     * object to pass to the source.
     * 
     * @author Daniel Ricketts
     *
     */
    private class TLAPMDocumentPartioningListener implements IDocumentPartitioningListener,
            IDocumentPartitioningListenerExtension2
    {

        public void documentPartitioningChanged(IDocument document)
        {
            // TODO Auto-generated method stub

        }

        /**
         * Converts new partitions to instances of {@link ITLAPMData} to be
         * passed to the {@link ITLAPMOutputSource} for the parser.
         */
        public void documentPartitioningChanged(DocumentPartitioningChangedEvent event)
        {
            IRegion changedRegion = event.getCoverage();

            if (changedRegion != null)
            {
                try
                {
                    ITypedRegion[] partitions = event.getDocument().computePartitioning(changedRegion.getOffset(),
                            changedRegion.getLength());
                    for (int i = 0; i < partitions.length; i++)
                    {
                        if (partitions[i].getType().equals(TagBasedTLAPMOutputTokenScanner.OBLIGATION_STATUS))
                        {
                            // Found an obligation status output line.
                            // System.out.println(event.getDocument().get(partitions[i].getOffset(),
                            // partitions[i].getLength()));

                            // The line of output for the obligation.
                            String obligationOutput = event.getDocument().get(partitions[i].getOffset(),
                                    partitions[i].getLength());

                            // parse into bl, bc, el, ec, status
                            String[] data = obligationOutput.split(":");
                            // IRegion obRegion = DocumentHelper.locationToRegion(document, new Location(null, Integer
                            // .parseInt(data[1]), Integer.parseInt(data[2]), Integer.parseInt(data[3]), Integer
                            // .parseInt(data[4])));

                            // ObligationStatusMessage region = new ObligationStatusMessage(convertStatus(data[5]), new
                            // Location(null,
                            // Integer.parseInt(data[1]), Integer.parseInt(data[2]), Integer.parseInt(data[3]),
                            // Integer.parseInt(data[4])), modulePath);

                            // source.newData(region);
                        }
                    }
                } catch (BadLocationException e)
                {
                    Activator.logError("Error computing TLAPM output partitions.", e);
                }
            }
        }
    }

    /**
     * Creates a new parser for the module given by the full
     * file system path represented by modulePath.
     * 
     * @param modulePath
     */
    public TagBasedTLAPMOutputIncrementalParser(IPath modulePath)
    {
        /*
         * Create the document.
         * 
         * As output streams into this parser, it will
         * be appended to this document. This allows
         * us to use the eclipse framework for document
         * partitioning.
         */
        document = new Document();

        /*
         * Set the partitioner for the document.
         */
        FastPartitioner partitioner = new FastPartitioner(new TagBasedTLAPMOutputTokenScanner(),
                TagBasedTLAPMOutputTokenScanner.CONTENT_TYPES);
        partitioner.connect(document);
        document.setDocumentPartitioner(partitioner);

        /*
         * Add the document partitioning listener that will
         * convert new partitions to new instances of
         * ITLAPMData.
         */
        document.addDocumentPartitioningListener(new TLAPMDocumentPartioningListener());

        /*
         * The source to which ITLAPMData will
         * be passed by the document partitioning listener.
         */
        source = new CachingTLAPMOutputSource(modulePath);

        this.modulePath = modulePath;

        /*
         * Add the source to the registry.
         */
        TLAPMOutputSourceRegistry.getInstance().addSource(source);

    }

    /**
     * Appends text to the document containing the existing TLAPM
     * output.
     * 
     * @param text
     * @throws BadLocationException
     */
    public void addIncrement(String text) throws BadLocationException
    {
        document.replace(document.getLength(), 0, text);
    }

    /**
     * Converts obligation status represented as a string
     * from the output of the TLAPM
     * to one represented by an int. The possible ints
     * are in {@link ObligationStatusMessage}.
     * @param status
     * @return
     */
    private int convertStatus(String status)
    {
        if (status.equals("V"))
        {
            return ObligationStatusMessage.STATUS_VERIFIED;
        }

        if (status.equals("E"))
        {
            return ObligationStatusMessage.STATUS_REJECTED;
        }

        return ObligationStatusMessage.STATUS_UNKNOWN;
    }

    /**
     * Returns a {@link TLAPMMessage} representing the information
     * contained in proverMessage. The String proverMessage
     * should be the String between the tags @!!BEGIN and @!!END.
     * It should not include these tags.
     * 
     * @param proverMessage
     * @return
     */
    private TLAPMMessage parseData(String proverMessage)
    {
        /*
         * The String proverMessage should be of the form
         * 
         * @!!<field-name>:<field-value>
         * @!!<field-name>:<field-value>
         * .
         * .
         * .
         * 
         * Possible field names right now are "loc" (location),
         * "status", and "obl" (obligation). In the future, there
         * might be a message type field, but for now, it is not used.
         */

        return null;
    }

    /**
     * Called when no more text is to be
     * sent to this parser.
     */
    public void onDone()
    {
        source.onDone();
    }

}
