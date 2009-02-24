package org.lamport.tla.toolbox.spec.parser;

import tla2sany.modanalyzer.SpecObj;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ParseResult
{
    private int status = IParseConstants.UNPARSED;
    private SpecObj specObj;
    
    /**
     * Constructs the parse status object 
     * @param status one of the {@link IParseConstants} values
     * @param specObj current specObject or null
     */
    public ParseResult(int status, SpecObj specObj)
    {
        this.status = status;
        this.specObj = specObj;
    }
    
    /**
     * @param specObj the specObj to set
     */
    public void setSpecObj(SpecObj specObj)
    {
        this.specObj = specObj;
    }
    /**
     * @return the specObj
     */
    public SpecObj getSpecObj()
    {
        return specObj;
    }
    /**
     * @param status the status to set
     */
    public void setStatus(int status)
    {
        this.status = status;
    }
    /**
     * @return the status
     */
    public int getStatus()
    {
        return status;
    }
}
