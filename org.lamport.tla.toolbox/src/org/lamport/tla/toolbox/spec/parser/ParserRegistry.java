package org.lamport.tla.toolbox.spec.parser;

import java.util.Vector;

/**
 * Default parser registry, that is used for the listers interested in parse result changes 
 * @author zambrovski
 * @version $Id$
 */
public class ParserRegistry implements IParserRegistry
{
    private Vector listeners = new Vector();
    private int status = IParseConstants.UNKNOWN;

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.spec.parser.IParserRegistry#addParseResultListener(org.lamport.tla.toolbox.spec.parser.IParseResultListner)
     */
    public void addParseResultListener(IParseResultListner listener)
    {
        if (!listeners.contains(listener))
        {
            listeners.add(listener);
        }
    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.spec.parser.IParserRegistry#parseResultChanged(int)
     */
    public synchronized void parseResultChanged(int parseStatus)
    {
        // only react ro real status changes
        if (status == parseStatus)
        {
            return;
        }

        // MODIFIED status can only replace status that is "greater" (see the constant values)
        // it will not replace UNPARSED and UNKNOWN
        if (parseStatus == IParseConstants.MODIFIED && status < parseStatus)
        {
            return;
        }

        this.status = parseStatus;
        for (int i = 0; i < listeners.size(); i++)
        {
            ((IParseResultListner) listeners.elementAt(i)).parseResultChanged(parseStatus);
        }

    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.spec.parser.IParserRegistry#removeParseResultListener(org.lamport.tla.toolbox.spec.parser.IParseResultListner)
     */
    public void removeParseResultListener(IParseResultListner listener)
    {
        listeners.remove(listener);
    }

}
