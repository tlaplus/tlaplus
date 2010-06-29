package org.lamport.tla.toolbox.tool.prover.ui.output;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.BadLocationException;
import org.lamport.tla.toolbox.tool.prover.job.ProverJob;
import org.lamport.tla.toolbox.tool.prover.output.IProverProcessOutputSink;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ObligationNumberMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ObligationStatusMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.StepStatusMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.TLAPMMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.WarningMessage;
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

    /**
     * The buffer that holds the current string of text out of which
     * messages can be parsed.
     */
    private StringBuilder currentSearchTextBuffer;
    /**
     * The module on which the prover was launched.
     */
    private IFile moduleFile;
    /**
     * The description of the prover launch.
     * Contains information about
     * the parameters used to launch the prover.
     */
    private ProverJob proverJob;
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
     * See the comments within the method for the parsing algorithm.
     * 
     * @param text
     * @throws BadLocationException
     */
    public void appendText(String text)
    {
        /*
         * The following sends each string between a
         * begin and end tag to be parsed into
         * an instance of TLAPMMessage.
         * 
         * Every piece of text to this method is appended to the
         * current search text buffer. This method executes
         * the following algorithm while one of the following
         * conditions is true:
         * 
         * A.) This parser has encountered a start tag without an end
         * tag previously and there is at least one end tag in currentSearchTextBuffer.
         * 
         * B.) This parser has not encountered a start tag without an end
         * tag previously and there is at least one start tag in currentSearchTextBuffer.
         * 
         * The loop:
         * 
         * 1.) If this parser has encountered a start tag without an end
         * tag previously, then there is at least one end tag in the buffer because
         * we are in this loop. Everything from the beginning of currentSearchTextBuffer
         * to the beginning of the first end tag in currentSearchTextBuffer is
         * a message. Parse that into an instance of TLAPMMessage, then remove
         * everything from the beginning of currentSearchTextBuffer to the end
         * of the first end tag. Set the flag indicating that we have NOT encountered
         * a start tag without an end tag.
         * 
         * 2.) If this parser has not encountered a start tag without an end
         * tag previously, then there is at least on start tag in this buffer
         * because we are in this loop. Remove everything from the beginning
         * of currentSearchTextBuffer to the end of the first start tag. Set
         * the flag indicating that we have encountered a start
         * tag without an end tag.
         * 
         * 3.) After either step 1 or step 2 has been completed, search for the next
         * tag. If this parser has previously encountered a start tag without an end
         * tag, search for an end tag. Else search for a start tag.
         * 
         * Note: the boolean inMessage is true iff this parser has previously encountered a
         * start tag without a matching end tag.
         */
        currentSearchTextBuffer.append(text);
        /*
         * tagIndex is the index of the tag we are looking for.
         * If this parser has encountered a start tag without an end
         * tag previously, then we are looking for an end tag. Else, we are looking
         * for a start tag.
         */
        int tagIndex = -1;
        if (inMessage)
        {
            tagIndex = currentSearchTextBuffer.indexOf(END_TAG);
        } else
        {
            tagIndex = currentSearchTextBuffer.indexOf(START_TAG);
        }

        while (tagIndex != -1)
        {
            if (inMessage)
            {
                /* This parser has encountered a start tag without an end
                 * tag previously, then there is at least one end tag in the buffer because
                 * we are in this loop. Everything from the beginning of currentSearchTextBuffer
                 * to the beginning of the first end tag in currentSearchTextBuffer is
                 * a message. Parse that into an instance of TLAPMMessage, then remove
                 * everything from the beginning of currentSearchTextBuffer to the end
                 * of the first end tag. Set the flag indicating that we have NOT encountered
                 * a start tag without an end tag.
                 * 
                 * Process the parsed message as indicated below.
                 */

                TLAPMMessage data = TLAPMMessage.parseMessage(currentSearchTextBuffer.substring(0, tagIndex),
                        moduleFile.getLocation().removeFileExtension().lastSegment());

                currentSearchTextBuffer.replace(0, tagIndex + END_TAG.length(), "");

                inMessage = false;

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
                     * 
                     * If the message is a warning message, call the appropriate
                     * method in prover helper that processes warning messages.
                     */

                    if (data instanceof ObligationStatusMessage)
                    {
                        ProverHelper.processObligationMessage((ObligationStatusMessage) data, proverJob);

                        if (ProverHelper.isObligationFinished((ObligationStatusMessage) data, proverJob))
                        {
                            monitor.worked(1);
                        }
                    } else if (data instanceof ObligationNumberMessage)
                    {
                        ObligationNumberMessage numMessage = (ObligationNumberMessage) data;
                        monitor.beginTask("Processing Obligations : " + numMessage.getCount() + " total.", numMessage
                                .getCount());
                    } else if (data instanceof StepStatusMessage)
                    {
                        ProverHelper.newStepStatusMessage((StepStatusMessage) data, proverJob);
                    } else if (data instanceof WarningMessage)
                    {
                        ProverHelper.processWarningMessage((WarningMessage) data);
                    }
                }

            } else
            {
                /*
                 * This parser has not encountered a start tag without an end
                 * tag previously, so there is at least on start tag in this buffer
                 * because we are in this loop. Remove everything from the beginning
                 * of currentSearchTextBuffer to the end of the first start tag. Set
                 * the flag indicating that we have encountered a start
                 * tag without an end tag.
                 */
                currentSearchTextBuffer.replace(0, tagIndex + START_TAG.length(), "");
                inMessage = true;
            }

            /*
             * tagIndex is the index of the tag we are looking for.
             * If this parser has encountered a start tag without an end
             * tag previously, then we are looking for an end tag. Else, we are looking
             * for a start tag.
             */
            if (inMessage)
            {
                tagIndex = currentSearchTextBuffer.indexOf(END_TAG);
            } else
            {
                tagIndex = currentSearchTextBuffer.indexOf(START_TAG);
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
     * @param proverJob the description of the prover launch. Contains information about
     * the parameters used to launch the prover.
     */
    public void initializeSink(IFile moduleFile, ProverJob proverJob, IProgressMonitor monitor)
    {
        currentSearchTextBuffer = new StringBuilder();

        this.moduleFile = moduleFile;
        this.monitor = monitor;
        this.proverJob = proverJob;
    }

    /**
     * Called when no more text is to be
     * sent to this parser.
     * 
     * If the prover was not launched for status
     * checking, then this method compares the step statuses
     * computed by the toolbox to the step statuses reported
     * by the tlapm. If the prover was launched for status checking,
     * then the toolbox does not compute step status information,
     * so this cannot be done.
     */
    public void processFinished()
    {
        if (!proverJob.isStatusCheck())
        {
            ProverHelper.compareStepStatusComputations(proverJob);
        }
    }

}
