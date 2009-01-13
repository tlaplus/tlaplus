package org.lamport.tla.toolbox.spec.parser;

import java.util.Vector;

/**
 * Default parser registry, that is used for the listers interested in parse result changes 
 * @author zambrovski
 */
public class ParserRegistry implements IParserRegistry
{
    private Vector listeners = new Vector();
    
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
    public void parseResultChanged(int parseStatus)
    {
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
