package org.lamport.tla.toolbox.spec.parser;

/**
 * Interface that must be implemented by classes that want
 * to be notified when a new parse result is returned by
 * the parser.
 * 
 * @author Daniel Ricketts
 *
 */
public interface IParseResultListener
{

    /**
     * Called when there is a new parse result broadcasted.
     * 
     * @param parseResult
     */
    public void newParseResult(ParseResult parseResult);

}
