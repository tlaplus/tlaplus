package org.lamport.tla.toolbox.spec.parser;

import java.util.Vector;

import org.eclipse.core.resources.IResource;
import org.lamport.tla.toolbox.tool.IParseResult;
import org.lamport.tla.toolbox.util.TLAMarkerInformationHolder;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.Errors;

/**
 * A holder for status SpecObj and the resource, and the parse status
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ParseResult implements IParseResult
{
    private int status = IParseConstants.UNPARSED;
    private SpecObj specObj;
    private IResource parsedResource;
    private Errors parseErrors;
    private Errors semanticErrors;
    private Vector detectedErrors;
    /**
     * Time stamp for when the parser
     * was called that eventually produced this result
     * as returned by {@link System#currentTimeMillis()}.
     */
    private long parserCalled;

    /**
     * Constructs the parse status object 
     * @param status one of the {@link IParseConstants} values
     * @param specObj current specObject or null
     */
    public ParseResult(int status, SpecObj specObj, IResource parsedResource, Errors parseErrors,
            Errors semanticErrors, long parserCalled)
    {
        this.status = status;
        this.specObj = specObj;
        this.parsedResource = parsedResource;
        this.parseErrors = parseErrors;
        this.semanticErrors = semanticErrors;
        this.detectedErrors = new Vector();
        this.parserCalled = parserCalled;
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
     * 
     * According to Eclipse, this method is never called.
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

    public Errors getParseErrors()
    {
        return parseErrors;
    }

    public Errors getSemanticErrors()
    {
        return semanticErrors;
    }

    public Vector getDetectedErrors()
    {
        return detectedErrors;
    }

    /**
     * Add an error to the error list
     * @param error marker information holder
     */
    public void addMarker(TLAMarkerInformationHolder error)
    {
        detectedErrors.add(error);
    }

    /**
     * Time stamp for when the parser
     * was called that eventually produced this result
     * as returned by {@link System#currentTimeMillis()}
     * 
     * @return the time when the parser was called to produce
     * this result
     */
    public long getParserCalled()
    {
        return parserCalled;
    }
}
