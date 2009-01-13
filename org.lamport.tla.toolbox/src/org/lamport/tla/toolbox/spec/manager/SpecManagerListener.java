package org.lamport.tla.toolbox.spec.manager;


/**
 * Reacts to changes in a list of specs
 * @author zambrovski
 */
public interface SpecManagerListener
{

    public void specManagerChanges(SpecManagerEvent e);
}
