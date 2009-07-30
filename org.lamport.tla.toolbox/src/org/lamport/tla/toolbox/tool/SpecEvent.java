package org.lamport.tla.toolbox.tool;

import org.lamport.tla.toolbox.spec.Spec;

/**
 * Specification life cycle event
 * 
 * 
 * <br>This class is not intended to be sub-classed
 * <br>This class is not intended to be instantiated by the tool developers
 * @author Simon Zambrovski
 * @version $Id$
 */
public class SpecEvent
{
    public static final int TYPE_CREATE = 1;
    public static final int TYPE_DELETE = 2;
    public static final int TYPE_RENAME = 4;
    public static final int TYPE_OPEN = 8;
    public static final int TYPE_CLOSE = 16;
    public static final int TYPE_PARSE = 32;
    /**
     * All events
     */
    public static final int TYPE_ALL = TYPE_CREATE | TYPE_DELETE | TYPE_RENAME | TYPE_OPEN | TYPE_CLOSE | TYPE_PARSE;
    
    
    public static SpecEvent CLOSE(Spec spec) 
    {
        return new SpecEvent(spec, TYPE_CLOSE);
    }
    
    
    private int type;
    private Spec spec;
    
    /**
     * Construct the immutable SpecEvent object
     * @param type one of the constants
     * @param spec
     */
    public SpecEvent(Spec spec, int type)
    {
        this.spec = spec;
        this.type = type;
    }

    /**
     * Retrieves the type of the event 
     */
    public final int getType()
    {
        return type;
    }
    /**
     * Retrieves the spec
     */
    public final Spec getSpec()
    {
        return spec;
    }

    public String toString()
    {
        
        return ((spec != null) ? spec.getName() : "no spec") + " | " + getType(); 
    }
    
    
}
