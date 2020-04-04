package org.lamport.tla.toolbox.spec.parser;

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CopyOnWriteArrayList;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IPath;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.tool.SpecEvent;
import org.lamport.tla.toolbox.tool.SpecLifecycleParticipant;
import org.lamport.tla.toolbox.util.ResourceHelper;

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
 * by calling {@link ParseResultBroadcaster#getParseResult(IPath)}.
 * 
 * All {@link ParseResult}s are for those produced while the currently opened spec
 * was open. Note that this includes any {@link ParseResult}s produced for modules
 * saved by TLC.
 * 
 * When the spec is closed, all information in this class should be cleared
 * by calling {@link ParseResultBroadcaster#clear()}.
 * 
 * @author Daniel Ricketts
 *
 */
public class ParseResultBroadcaster
{

    private static ParseResultBroadcaster instance;
    private final List<IParseResultListener> listeners;
    /**
     * Map from {@link IPath} to the most recent
     * {@link ParseResult} containing that module that
     * exists at that full file system path.
     */
    private Map<IPath, ParseResult> parseResults;

    /**
     * This is a singleton class, so the constructor
     * should not be called by clients. Instead, use
     * {@link ParseResultBroadcaster#getParseResultBroadcaster()}.
     */
    private ParseResultBroadcaster()
    {
        listeners = new CopyOnWriteArrayList<IParseResultListener>();
        parseResults = new HashMap<IPath, ParseResult>();
        Activator.getSpecManager().addSpecLifecycleParticipant(new SpecLifecycleParticipant() {
			/* (non-Javadoc)
			 * @see org.lamport.tla.toolbox.tool.SpecLifecycleParticipant#eventOccured(org.lamport.tla.toolbox.tool.SpecEvent)
			 */
			public boolean eventOccured(SpecEvent event) {
				if (event.getType() == SpecEvent.TYPE_CLOSE) {
					/*
					 * We clear any information that the parse result
					 * broadcaster has when the spec is closed because the
					 * parse result broadcasters saves a map of module names
					 * to parse results. These module names are unique
					 * within a spec but not unique globally so information
					 * in the class should not persist across changes of
					 * specs.
					 */
					ParseResultBroadcaster.this.clear();
				}
				return true;
			}
		});
    }

    /**
     * Singleton access method.
     * 
     * @return
     */
    public synchronized static ParseResultBroadcaster getParseResultBroadcaster()
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
     * This will send the {@link ParseResult} to all listeners that have
     * previously been added through a call to the method {@link #addParseResultListener(IParseResultListener)}.
     * 
     * @param parseResult
     */
    public void broadcastParseResult(ParseResult parseResult)
    {
        Iterator<IParseResultListener> it = listeners.iterator();
        while (it.hasNext())
        {
            IParseResultListener listener = it.next();
            listener.newParseResult(parseResult);
        }

        // put the parse result in the parse result map
        // as the latest for all of the modules it contains
        ModuleNode[] moduleNodes = parseResult.getSpecObj().getExternalModuleTable().getModuleNodes();
        // For each module node, put an entry into the parse result map
        // with the full file system path to the module as key
        // and the parse result as the value.
        // If there is an existing value for a given path, this
        // new parse result will replace it.

        /*
         * The following is the path to the directory containing all modules
         * in the array moduleNodes. All parsed modules (except for standard
         * modules) must be in the same directory.
         */
        IPath dirPath = parseResult.getParsedResource().getLocation().removeLastSegments(1);
        for (int i = 0; i < moduleNodes.length; i++)
        {
            parseResults.put(dirPath.append(ResourceHelper.getModuleFileName(moduleNodes[i].getName().toString())),
                    parseResult);
        }
    }

    /**
     * Add an {@link IParseResultListener} that will be notified whenever a new {@link ParseResult}
     * is created by a launch of SANY.
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
        listeners.remove(parseResultListener);
    }

    /**
     * Returns the most recent {@link ParseResult} for the module
     * located at modulePath. This is the full file system path
     * to the module. This can be obtained from an {@link IResource}
     * by calling {@link IResource#getLocation()}.
     * 
     * Note that this can only return {@link ParseResult}s that were created
     * while the currently open spec was open. This includes any
     * {@link ParseResult}s produced for modules
     * saved by TLC. When a spec is closed, all
     * references to {@link ParseResult}s are removed from this class.
     */
    public ParseResult getParseResult(IPath modulePath)
    {
        return parseResults.get(modulePath);
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
