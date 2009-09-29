package org.lamport.tla.toolbox.tool.tlc.output.source;

import java.util.Vector;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITypedRegion;
import org.lamport.tla.toolbox.tool.tlc.output.ITLCOutputListener;

/**
 * TLC output source, caching the output for listeners registered after the source 
 * has received the output 
 *  
 * @author Simon Zambrovski
 * @version $Id$
 */
public class CachingTLCOutputSource implements ITLCOutputSource
{
    private Vector listenerHolders = new Vector();
    private boolean done = false;
    private Vector detectedRegions = new Vector();
    protected IDocument document;
    private String sourceName;
    private int priority;

    /**
     * Constructor of the source for a given name and prio
     * @param name
     * @param priority
     */
    public CachingTLCOutputSource(String name, int priority)
    {
        this.sourceName = name;
        this.priority = priority;
    }

    /**
     * Inform the listeners about the change 
     */
    public synchronized void onOutput(ITypedRegion region)
    {
        Assert.isTrue(!done, "Output source is not accepting new output after it reported the finalization");

        this.detectedRegions.add(region);
        for (int i = 0; i < this.listenerHolders.size(); i++)
        {
            onOutput(((ListenerProgressHolder) this.listenerHolders.get(i)), region);
        }
    }

    /**
     * Inform the listeners about completion
     */
    public synchronized void onDone()
    {
        this.done = true;
        for (int i = 0; i < this.listenerHolders.size(); i++)
        {
            ((ListenerProgressHolder) this.listenerHolders.get(i)).listener.onDone();
        }
    }

    private synchronized void onOutput(ListenerProgressHolder holder, ITypedRegion region)
    {
        Assert.isNotNull(document, "The document must be initialized");
        holder.listener.onOutput(region, document);
        holder.reported++;
    }

    public void addTLCOutputListener(ITLCOutputListener listener)
    {
        ListenerProgressHolder holder = new ListenerProgressHolder(listener, 0);
        // remove the existing
        if (this.listenerHolders.contains(holder))
        {
            removeTLCOutputListener(listener);
        }
        // add the new one
        this.listenerHolders.add(holder);
        for (int i = 0; i < this.detectedRegions.size(); i++)
        {
            /* inform the listener about missed changes */
            onOutput(holder, (ITypedRegion) this.detectedRegions.get(i));
        }
        if (done)
        {
            holder.listener.onDone();
        }

    }

    public void removeTLCOutputListener(ITLCOutputListener listener)
    {
        this.listenerHolders.remove(new ListenerProgressHolder(listener, 0));
    }

    public void setDocument(IDocument document)
    {
        this.document = document;
    }

    public IDocument getDocument()
    {
        return this.document;
    }

    /**
     * @see org.lamport.tla.toolbox.tool.tlc.output.source.ITLCOutputSource#getTLCOutputName()
     */
    public String getTLCOutputName()
    {
        return sourceName;
    }

    /**
     * @see org.lamport.tla.toolbox.tool.tlc.output.source.ITLCOutputSource#getListeners()
     */
    public ITLCOutputListener[] getListeners()
    {
        ITLCOutputListener[] listeners = new ITLCOutputListener[listenerHolders.size()];
        for (int i = 0; i < listeners.length; i++)
        {
            listeners[i] = ((ListenerProgressHolder) listenerHolders.get(i)).listener;
        }
        return listeners;
    }

    /**
     * @see org.lamport.tla.toolbox.tool.tlc.output.source.ITLCOutputSource#getSourcePrio()
     */
    public int getSourcePrio()
    {
        return priority;
    }

    /**
     * Holder for the listener and the number of message reported
     */
    class ListenerProgressHolder
    {
        ITLCOutputListener listener;
        int reported;

        /**
         * Constructor
         * @param listener
         * @param reported
         */
        public ListenerProgressHolder(ITLCOutputListener listener, int reported)
        {
            this.listener = listener;
            this.reported = reported;
        }

        public boolean equals(Object obj)
        {
            if (obj instanceof ListenerProgressHolder)
                return listener.equals(((ListenerProgressHolder) obj).listener);
            else if (obj instanceof ITLCOutputListener)
                return listener.equals(obj);
            else
                return false;
        }

        public int hashCode()
        {
            return listener.hashCode();
        }

        public String toString()
        {
            return listener.toString();
        }

    }

}
