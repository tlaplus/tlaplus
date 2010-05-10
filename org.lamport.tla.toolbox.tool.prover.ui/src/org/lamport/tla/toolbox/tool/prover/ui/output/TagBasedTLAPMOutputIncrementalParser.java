package org.lamport.tla.toolbox.tool.prover.ui.output;

import org.eclipse.core.runtime.IPath;
import org.eclipse.jface.text.BadLocationException;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.TLAPMMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.source.CachingTLAPMOutputSource;
import org.lamport.tla.toolbox.tool.prover.ui.output.source.ITLAPMOutputSource;
import org.lamport.tla.toolbox.tool.prover.ui.output.source.TLAPMOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.prover.ui.status.ProofStepStatus;
import org.lamport.tla.toolbox.tool.prover.ui.status.ProofStepStatusMarkerHelper;

/**
 * This class is used to parse raw output from
 * the TLAPM to produce instances of {@link TLAPMMessage}
 * to describe that output. It stores that output
 * in a {@link ITLAPMOutputSource} which is placed
 * in the {@link TLAPMOutputSourceRegistry}.
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
public class TagBasedTLAPMOutputIncrementalParser
{

    private StringBuilder currentMessageBuffer;
    private ITLAPMOutputSource source;
    private IPath modulePath;
    /**
     * Flag indicating that this parser has encountered
     * a start tag but has not yet found its matching
     * end tag.
     */
    private boolean inMessage = false;

    public static final String DELIM = "@!!";
    public static final String START_TAG = DELIM + "BEGIN";
    public static final String END_TAG = DELIM + "END";

    // public static final Pattern START_TAG_PATTERN = Pattern.compile(START_TAG);
    // public static final Pattern END_TAG_PATTERN = Pattern.compile(END_TAG);

    /**
     * Called to stream text into this parser.
     * 
     * This method creates instances of {@link TLAPMMessage} and
     * sends them to the {@link ITLAPMOutputSource} for this
     * class.
     * 
     * @param text
     * @throws BadLocationException
     */
    public void addIncrement(String text) throws BadLocationException
    {
        System.out.println("New text : \n" + text);
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

                    TLAPMMessage data = TLAPMMessage.parseMessage(currentMessageBuffer.toString(), modulePath
                            .removeFileExtension().lastSegment());

                    if (data != null)
                    {
                        source.newData(data);

                        /*
                         * Determine if the message is
                         * giving the status of a proof step.
                         * If it is, call the appropriate method
                         * to create a marker for that proof step.
                         */
                        ProofStepStatus status = ProofStepStatusMarkerHelper.messageToStatus(data);
                        if (status != null)
                        {
                            ProofStepStatusMarkerHelper.newStepStatus(status);
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
        /*
         * Use a pattern matcher to search for start tags.
         * 
         * while(startTagMatcher.find)
         *    currentMessageBuffer.append(all data between found
         *                                start tag and previous start
         *                                tag (or beginning of text if
         *                                this is the first found start tag))
         *    convert currentMessageBuffer to TLAPMData and send to source
         *    set currentMessageBuffer to an empty buffer
         */

        /*
         * The sub strings that fall between START_TAG's.
         * 
         * If the text is 
         * 
         * "@!!<field-name>:<field-value1>
         * .
         * .
         * .
         * @!!BEGIN
         * @!!<field-name>:<field-value2>
         * .
         * .
         * .
         * @!!BEGIN
         * @!!<field-name>:<field-value3>
         * .
         * ."
         * 
         * then this array has 3 elements:
         * 1.) 
         * "@!!<field-name>:<field-value1>
         * .
         * .
         * ."
         * 
         * 2.) 
         * "@!!<field-name>:<field-value2>
         * .
         * .
         * ."
         * 
         * 3.)
         * @!!<field-name>:<field-value3>
         * .
         * ."
         * 
         * 
         * If text terminates with a start tag, then
         * the last element of messageSegments will be an empty
         */
        // String[] messageSegments = text.split(START_TAG, -1);
        //
        // for (int i = 0; i < messageSegments.length; i++)
        // {
        // currentMessageBuffer.append(messageSegments[i]);
        //
        // if (i != messageSegments.length - 1)
        // {
        // /*
        // * This message currently contained in currentMessageBuffer
        // * should be complete because the input
        // * text contains another start tag after this segment.
        // *
        // * 1.) Generate a TLAPMData for this message.
        // * 2.) Clear the currentMessageBuffer to ready
        // * it for the next message.
        // */
        // TLAPMMessage data = TLAPMMessage.parseMessage(currentMessageBuffer.toString(), modulePath
        // .removeFileExtension().lastSegment());
        // if (data != null)
        // {
        // source.newData(data);
        //
        // /*
        // * Determine if the message is
        // * giving the status of a proof step.
        // * If it is, call the appropriate method
        // * to create a marker for that proof step.
        // */
        // ProofStepStatus status = ProofStepStatusMarkerHelper.messageToStatus(data);
        // if (status != null)
        // {
        // ProofStepStatusMarkerHelper.newStepStatus(status);
        // }
        // }
        //
        // currentMessageBuffer = new StringBuilder();
        // }
        // }
    }

    public TagBasedTLAPMOutputIncrementalParser(IPath modulePath)
    {
        currentMessageBuffer = new StringBuilder();
        source = new CachingTLAPMOutputSource(modulePath);
        this.modulePath = modulePath;

        TLAPMOutputSourceRegistry.getInstance().addSource(source);
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
