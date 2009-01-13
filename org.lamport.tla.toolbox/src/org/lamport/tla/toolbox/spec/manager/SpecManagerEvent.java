package org.lamport.tla.toolbox.spec.manager;

import org.lamport.tla.toolbox.spec.Spec;

/**
 * Represent changes in the list of specs
 * 
 * @author zambrovski
 */
public class SpecManagerEvent
{
    public static int CHANGE_ADD    = 1;
    public static int CHANGE_REMOVE = 2;

    public int        changeType;
    public Spec[]     specs;

    public SpecManagerEvent(int changeType, Spec[] specs)
    {
        this.changeType = changeType;
        this.specs = specs;
    }
}
