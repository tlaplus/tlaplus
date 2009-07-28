package org.lamport.tla.toolbox.tool.tlc.output;

import java.util.Vector;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITypedRegion;

/**
 * TLC output source, caching the output for listeners registered after the source 
 * has output 
 *  
 * @author Simon Zambrovski
 * @version $Id$
 */
public abstract class CachingTLCOutputSource implements ITLCOutputSource
{
    private Vector listeners = new Vector();
    private boolean done = false;
    private Vector detectedRegions = new Vector();
    protected IDocument document;

    /**
     * Inform the listeners about the change 
     */
    public synchronized void onOutput(ITypedRegion region)
    {
        Assert.isTrue(!done, "Output source is not accepting new output after it reported the finalization");

        this.detectedRegions.add(region);
        for (int i = 0; i < this.listeners.size(); i++)
        {
            onOutput(((ListenerProgressHolder) this.listeners.get(i)), region);
        }
    }

    /**
     * Inform the listeners about completion
     */
    public synchronized void onDone()
    {
        this.done = true;
        for (int i = 0; i < this.listeners.size(); i++)
        {
            ((ListenerProgressHolder) this.listeners.get(i)).listener.onDone();
        }
    }

    private void onOutput(ListenerProgressHolder holder, ITypedRegion region)
    {
        Assert.isNotNull(document, "The docuemnt must be initialized");
        holder.listener.onOutput(region, document);
        holder.reported++;
    }

    public void addTLCStatusListener(ITLCOutputListener listener)
    {
        ListenerProgressHolder holder = new ListenerProgressHolder(listener, 0);
        this.listeners.add(holder);
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

    public void removeTLCStatusListener(ITLCOutputListener listener)
    {
        this.listeners.remove(new ListenerProgressHolder(listener, 0));
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
            return listener.equals(obj);
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
