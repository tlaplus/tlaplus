package org.lamport.tla.toolbox.spec.parser;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import tla2sany.semantic.ModuleNode;

/**
 * Singleton class for broadcasting new parse results to listeners. Get the
 * instance of this class by calling {@link ParseResultBroadcaster#getParseResultBroadcaster()}.
 * 
 * Classes that want to broadcast the result of parsing of a module should call
 * {@link ParseResultBroadcaster#broadcastParseResult(ParseResult)}.
 * 
 * Classes that want to listen for new parse results should implement
 * {@link IParseResultListener} and should add themselves by calling
 * {@link ParseResultBroadcaster#addParseResultListener(IParseResultListener)} and remove
 * themselves by calling {@link ParseResultBroadcaster#removeParseResultListener(IParseResultListener)}.
 * 
 * Classes can also get the most recent {@link ParseResult} for a given module
 * by calling {@link ParseResultBroadcaster#getParseResult(String)}.
 * 
 * All {@link ParseResult}s are for modules in the currently opened spec.
 * When the spec is closed, all information in this class should be cleared
 * by calling {@link ParseResultBroadcaster#clear()}.
 * 
 * @author Daniel Ricketts
 *
 */
public class ParseResultBroadcaster
{

    private static ParseResultBroadcaster instance;
    private List listeners;
    /*
     * Map from module names to the most recent
     * parse result containing that module.
     */
    private Map parseResults;

    /**
     * This is a singleton class, so the constructor
     * should not be called by clients. Instead, use
     * {@link ParseResultBroadcaster#getParseResultBroadcaster()}.
     */
    private ParseResultBroadcaster()
    {
        listeners = new LinkedList();
        parseResults = new HashMap();
    }

    /**
     * Singleton access method.
     * 
     * @return
     */
    public static ParseResultBroadcaster getParseResultBroadcaster()
    {
        if (instance == null)
        {
            instance = new ParseResultBroadcaster();
        }

        return instance;
    }

    /**
     * Classes that want to broadcast the result of parsing should
     * call this method with an instance of {@link ParseResult}.
     * 
     * @param parseResult
     */
    public void broadcastParseResult(ParseResult parseResult)
    {
        Iterator it = listeners.iterator();
        while (it.hasNext())
        {
            IParseResultListener listener = (IParseResultListener) it.next();
            listener.newParseResult(parseResult);
        }

        // put the parse result in the parse result map
        // as the latest for all of the modules it contains
        ModuleNode[] moduleNodes = parseResult.getSpecObj().getExternalModuleTable().getModuleNodes();
        // for each module node, put an entry into the parse result map
        // with the module name as key and the parse result as the value
        // if there is an existing value for a given module name, this
        // new parse result will replace it
        for (int i = 0; i < moduleNodes.length; i++)
        {
            parseResults.put(moduleNodes[i].getName().toString(), parseResult);
        }
    }

    /**
     * Add an {@link IParseResultListener} that will be notified whenever a class wants
     * to broadcast the result of parsing.
     * 
     * Adding a listener that has already been added will have no effect.
     * 
     * @param parseResultListener
     */
    public void addParseResultListener(IParseResultListener parseResultListener)
    {
        if (!listeners.contains(parseResultListener))
        {
            listeners.add(parseResultListener);
            System.out.println("Added a parse result listener.");
            System.out.println("There are now " + listeners.size() + " listeners.");
        }
    }

    /**
     * Remove an {@link IParseResultListener} from the list of listeners
     * who will be notified of a new parse result.
     * 
     * @param parseResultListener
     */
    public void removeParseResultListener(IParseResultListener parseResultListener)
    {
        boolean removed = listeners.remove(parseResultListener);
        if (removed)
        {
            System.out.println("Removed a parse result listener.");
            System.out.println("There are now " + listeners.size() + " listeners.");
        }
    }

    /**
     * Returns the most recent {@link ParseResult} for the module
     * name (without .tla extension). This method assumes the module
     * is in the currently opened spec.
     */
    public ParseResult getParseResult(String moduleName)
    {
        return (ParseResult) parseResults.get(moduleName);
    }

    /**
     * Clears all information from this broadcaster. The
     * list of listeners and the map of parse results gets
     * cleared.
     */
    public void clear()
    {
        listeners.clear();
        parseResults.clear();
    }
}
