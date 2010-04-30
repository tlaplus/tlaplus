package org.lamport.tla.toolbox.tool.prover.ui.output;

import org.eclipse.core.runtime.IPath;
import org.eclipse.jface.text.BadLocationException;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.TLAPMMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.source.CachingTLAPMOutputSource;
import org.lamport.tla.toolbox.tool.prover.ui.output.source.ITLAPMOutputSource;
import org.lamport.tla.toolbox.tool.prover.ui.output.source.TLAPMOutputSourceRegistry;

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
 * {@link TagBasedTLAPMOutputIncrementalParser2#addIncrement(String)},
 * 
 * See {@link TagBasedTLAPMOutputIncrementalParser2#addIncrement(String)}
 * for the parsing algorithm.
 * 
 * @author Daniel Ricketts
 *
 */
public class TagBasedTLAPMOutputIncrementalParser2
{

    private StringBuilder currentMessageBuffer;
    private ITLAPMOutputSource source;
    private IPath modulePath;

    public static final String DELIM = "@!!";
    public static final String START_TAG = DELIM + "BEGIN";
    public static final String END_TAG = DELIM + "END";

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
        String[] messageSegments = text.split(START_TAG, -1);

        for (int i = 0; i < messageSegments.length; i++)
        {
            currentMessageBuffer.append(messageSegments[i]);

            if (i != messageSegments.length - 1)
            {
                /*
                 * This message currently contained in currentMessageBuffer
                 * should be complete because the input
                 * text contains another start tag after this segment.
                 * 
                 * 1.) Generate a TLAPMData for this message.
                 * 2.) Clear the currentMessageBuffer to ready
                 *     it for the next message.
                 */
                TLAPMMessage data = TLAPMMessage.parseMessage(messageSegments[i], modulePath.removeFileExtension()
                        .lastSegment());
                if (data != null)
                {
                    source.newData(data);
                }

                currentMessageBuffer = new StringBuilder();
            }
        }
    }

    public TagBasedTLAPMOutputIncrementalParser2(IPath modulePath)
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
