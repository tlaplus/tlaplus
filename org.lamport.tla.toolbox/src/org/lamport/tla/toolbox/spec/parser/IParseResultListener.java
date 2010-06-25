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
     * This method is called when a new {@link ParseResult} is created by
     * a call to SANY. The object parseResult is that new {@link ParseResult}.
     * 
     * @param parseResult
     */
    public void newParseResult(ParseResult parseResult);

}
