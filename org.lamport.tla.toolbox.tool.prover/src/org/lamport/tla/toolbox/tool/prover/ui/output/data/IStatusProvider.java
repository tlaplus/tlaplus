package org.lamport.tla.toolbox.tool.prover.ui.output.data;

import org.lamport.tla.toolbox.tool.prover.ui.preference.ProverPreferencePage;

/**
 * An interface for things that have a proof status. In particular
 * obligations and steps have proof statuses.
 * 
 * @author Daniel Ricketts
 *
 */
public interface IStatusProvider
{
    // /**
    // * The values of the color predicates of the provider. This is an array indexed
    // * by color numbers of length equal to
    // * {@link ProverPreferencePage#NUM_STATUS_COLORS}.
    // *
    // * @return
    // */
    // public boolean[] getColorPredicateValues();

}
