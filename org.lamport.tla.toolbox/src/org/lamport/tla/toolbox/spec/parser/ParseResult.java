package org.lamport.tla.toolbox.spec.parser;

import org.eclipse.core.resources.IResource;

import tla2sany.modanalyzer.SpecObj;

/**
 * A holder for status specobj and the resource
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ParseResult
{
    private int status = IParseConstants.UNPARSED;
    private SpecObj specObj;
    private IResource parsedResource;
    
    /**
     * Constructs the parse status object 
     * @param status one of the {@link IParseConstants} values
     * @param specObj current specObject or null
     */
    public ParseResult(int status, SpecObj specObj, IResource parsedResource)
    {
        this.status = status;
        this.specObj = specObj;
        this.parsedResource = parsedResource;
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

    public IResource getParsedResource()
    {
        return parsedResource;
    }

    public void setParsedResource(IResource parsedResource)
    {
        this.parsedResource = parsedResource;
    }
}
