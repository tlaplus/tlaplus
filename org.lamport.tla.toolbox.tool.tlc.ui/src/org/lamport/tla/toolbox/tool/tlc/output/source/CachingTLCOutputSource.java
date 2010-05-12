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
    /**
     * List of {@link TypedRegionAndText}s.
     */
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
     * Inform the listeners about the change. The change comes in the form
     * of an {@link ITypedRegion} and the text represented by the region. The
     * text represented by the region is the text that could be obtained from this
     * source's document using the region's offset and length when the region was created.
     * However, the document may have changed since the region was created, so its
     * offset and length may not correspond to anything useful. However, its type
     * is useful, and if it is a {@link TLCRegion}, then it could contain other
     * useful information.
     * 
     * @param regionText TODO
     */
    public synchronized void onOutput(ITypedRegion region, String regionText)
    {
        Assert.isTrue(!done, "Output source is not accepting new output after it reported the finalization");

        this.detectedRegions.add(new TypedRegionAndText(region, regionText));
        for (int i = 0; i < this.listenerHolders.size(); i++)
        {
            onOutput(((ListenerProgressHolder) this.listenerHolders.get(i)), region, regionText);
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

    /**
     * Inform the listener about the change. The change comes in the form
     * of an {@link ITypedRegion} and the text represented by the region. The
     * text represented by the region is the text that could be obtained from this
     * source's document using the region's offset and length when the region was created.
     * However, the document may have changed since the region was created, so its
     * offset and length may not correspond to anything useful. However, its type
     * is useful, and if it is a {@link TLCRegion}, then it could contain other
     * useful information.
     * 
     * @param holder
     * @param region
     * @param regionText
     */
    private synchronized void onOutput(ListenerProgressHolder holder, ITypedRegion region, String regionText)
    {
        Assert.isNotNull(document, "The document must be initialized");
        holder.listener.onOutput(region, regionText);
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
            onOutput(holder, ((TypedRegionAndText) this.detectedRegions.get(i)).getRegion(),
                    ((TypedRegionAndText) this.detectedRegions.get(i)).getText());
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

    /**
     * Wrapper class for a region and the text that it
     * represents in the document when it was created.
     * 
     * @author Daniel Ricketts
     *
     */
    private class TypedRegionAndText
    {
        private ITypedRegion region;
        private String text;

        private TypedRegionAndText(ITypedRegion region, String text)
        {
            this.region = region;
            this.text = text;
        }

        /**
         * @return the region
         */
        public ITypedRegion getRegion()
        {
            return region;
        }

        /**
         * @return the text
         */
        public String getText()
        {
            return text;
        }

    }

}
