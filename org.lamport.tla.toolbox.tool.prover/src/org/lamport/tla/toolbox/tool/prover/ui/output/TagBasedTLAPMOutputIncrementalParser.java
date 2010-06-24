package org.lamport.tla.toolbox.tool.prover.ui.output;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.BadLocationException;
import org.lamport.tla.toolbox.tool.prover.output.IProverProcessOutputSink;
import org.lamport.tla.toolbox.tool.prover.output.internal.ProverLaunchDescription;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ObligationNumberMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ObligationStatusMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.StepStatusMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.TLAPMMessage;
import org.lamport.tla.toolbox.tool.prover.ui.util.ProverHelper;

/**
 * This class is used to parse raw output from
 * the TLAPM to produce instances of {@link TLAPMMessage}
 * to describe that output. It creates resource markers
 * representing the information from the messages.
 * 
 * The first implementation stored output in a source, but
 * we decided that caching this information is unnecessary.
 * Markers are used instead.
 * 
 * Output from the prover comes in the following generic
 * form:
 * 
 * @!!BEGIN
 * @!!<field-name>:<field-value>
 * @!!<field-name>:<field-value>
 * .
 * .
 * .
 * @!!END
 * 
 * TLAPM output streams into this class through calls of
 * {@link TagBasedTLAPMOutputIncrementalParser#addIncrement(String)},
 * 
 * See {@link TagBasedTLAPMOutputIncrementalParser#addIncrement(String)}
 * for the parsing algorithm.
 * 
 * @author Daniel Ricketts
 *
 */
public class TagBasedTLAPMOutputIncrementalParser implements IProverProcessOutputSink
{

    private StringBuilder currentMessageBuffer;
    // private ITLAPMOutputSource source;
    private IFile moduleFile;
    /**
     * The description of the prover launch.
     * Contains information about
     * the parameters used to launch the prover.
     */
    private ProverLaunchDescription description;
    /**
     * The monitor that can
     * be used to report information about progress.
     * In particular, it should be used to report
     * progress on obligation processing.
     */
    private IProgressMonitor monitor;
    /**
     * Flag indicating that this parser has encountered
     * a start tag but has not yet found its matching
     * end tag.
     */
    private boolean inMessage = false;

    public static final String DELIM = "@!!";
    public static final String START_TAG = DELIM + "BEGIN";
    public static final String END_TAG = DELIM + "END";

    /**
     * Called to stream text into this parser.
     * 
     * This method creates instances of {@link TLAPMMessage} and
     * process them according to their type.  
     * 
     * @param text
     * @throws BadLocationException
     */
    public void appendText(String text)
    {
        // System.out.println("New text : \n" + text);
        /*
         * The following sends each string between a
         * begin and end tag to be parsed into
         * an instance of TLAPMMessage.
         * 
         * Once it encounters a start tag, it appends all new
         * strings sent to this methods to a string builder. Once
         * an end tag is encountered, it sends the current contents
         * of the string builder to TLAPMMessage to be parsed and clears
         * the string builder for the next start tag.
         *    
         */
        String searchText = text;
        while (!searchText.isEmpty())
        {
            if (inMessage)
            {
                int endTagIndex = searchText.indexOf(END_TAG);
                if (endTagIndex != -1)
                {
                    inMessage = false;
                    /*
                     * Everything from the beginning of the search string
                     * to the beginning of the end tag is part of the message.
                     * 
                     * The current message is complete. It can be parsed to a
                     * TLAPMMessage.
                     * 
                     * Continue searching after the end tag for a new message.
                     */
                    currentMessageBuffer.append(searchText.substring(0, endTagIndex));

                    TLAPMMessage data = TLAPMMessage.parseMessage(currentMessageBuffer.toString(), moduleFile
                            .getLocation().removeFileExtension().lastSegment());

                    if (data != null)
                    {

                        /*
                         * Create the appropriate marker for the
                         * message. If the message is step status inform ProverHelper
                         * using ProverHelper.newStepStatusMessage(). If this is a
                         * launch for status checking, then the toolbox does not compute
                         * step statuses itself, so the step status messages must be used
                         * to update status markers. This means that the flag addMarker
                         * in the method newStepStatusMessage should be set to true.
                         * 
                         * If the message is an obligation
                         * status, create an obligation status marker.
                         * 
                         * If the message gives the number of obligations
                         * to be checked, then update the progress monitor
                         * for this parser to indicate this. If the message is an
                         * ObligationStatusMessage that indicates that
                         * the TLAPM is done processing the obligation in any
                         * way, then the monitor will reflect this fact.
                         */

                        if (data instanceof ObligationStatusMessage)
                        {
                            ProverHelper.processObligationMessage((ObligationStatusMessage) data, description
                                    .getLevelNode());

                            if (ProverHelper.isObligationFinished((ObligationStatusMessage) data, description))
                            {
                                monitor.worked(1);
                            }
                        } else if (data instanceof ObligationNumberMessage)
                        {
                            ObligationNumberMessage numMessage = (ObligationNumberMessage) data;
                            monitor.beginTask("Processing Obligations : " + numMessage.getCount() + " total.",
                                    numMessage.getCount());
                        } else if (data instanceof StepStatusMessage)
                        {
                            ProverHelper.newStepStatusMessage((StepStatusMessage) data, description.isStatusCheck());
                        }
                    }

                    searchText = searchText.substring(endTagIndex + END_TAG.length(), searchText.length());
                } else
                {
                    /*
                     * Everything in the search text is part of the message.
                     * Nothing more to search.
                     */
                    currentMessageBuffer.append(searchText);
                    searchText = "";
                }
            } else
            {
                // Matcher matcher = START_TAG_PATTERN.matcher(searchText);
                int startTagIndex = searchText.indexOf(START_TAG);
                if (startTagIndex != -1)
                {
                    inMessage = true;
                    /*
                     * Search the remaining text for an end tag.
                     */
                    searchText = searchText.substring(startTagIndex + START_TAG.length(), searchText.length());

                    currentMessageBuffer = new StringBuilder();
                } else
                {
                    /*
                     * Nothing more to search.
                     */
                    searchText = "";
                }
            }
        }
    }

    /**
     * Constructor taking the path to the module for which there is output, the monitor that can
     * be used to report information about progress, and the description of the prover launch.
     * This contains information about the parameters used to launch the prover.
     * 
     * @param moduleFile
     * @param monitor
     * @param description the description of the prover launch. Contains information about
     * the parameters used to launch the prover.
     */
    public void initializeSink(IFile moduleFile, ProverLaunchDescription description, IProgressMonitor monitor)
    {
        currentMessageBuffer = new StringBuilder();

        this.moduleFile = moduleFile;
        this.monitor = monitor;
        this.description = description;
    }

    /**
     * Called when no more text is to be
     * sent to this parser.
     */
    public void processFinished()
    {
        ProverHelper.compareStepStatusComputations();
    }

}
