package org.lamport.tla.toolbox.tool.prover.ui.output.data;

/**
 * An interface for things that have a proof status. In particular
 * obligations and steps have proof statuses.
 * 
 * @author Daniel Ricketts
 *
 */
public interface IStatusProvider
{
    /**
     * The status of the provider.
     * 
     * @return
     */
    public int getStatus();

}
