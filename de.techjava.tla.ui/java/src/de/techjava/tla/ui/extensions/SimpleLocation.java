package de.techjava.tla.ui.extensions;

/**
 * DOCME
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: SimpleLocation.java,v 1.1 2005/08/22 15:43:33 szambrovski Exp $
 */
public class SimpleLocation 
	implements ILocation 
{

    private String source;
    private boolean isNull;
    private int beginLine;
    private int endLine;
    private int beginColumn;
    private int endColumn;

    public SimpleLocation(int beginLine, int beginColumn, int endLine, int endColumn)
    {
        this.beginColumn = beginColumn;
        this.endColumn = endColumn;
        this.beginLine = beginLine;
        this.endLine = endLine;
        
    }
    /**
     * @see de.techjava.tla.ui.extensions.ILocation#isNullLocation()
     */
    public boolean isNullLocation() 
    {
        return this.isNull;
    }

    /**
     * @see de.techjava.tla.ui.extensions.ILocation#beginLine()
     */
    public int beginLine() {
        return beginLine;
    }

    /**
     * @see de.techjava.tla.ui.extensions.ILocation#beginColumn()
     */
    public int beginColumn() {
        return beginColumn;
    }

    /**
     * @see de.techjava.tla.ui.extensions.ILocation#endLine()
     */
    public int endLine() {
        return endLine;
    }

    /**
     * @see de.techjava.tla.ui.extensions.ILocation#endColumn()
     */
    public int endColumn() {
        return endColumn;
    }

    /**
     * @see de.techjava.tla.ui.extensions.ILocation#source()
     */
    public String source() 
    {
        return this.source;
    }

}

/*
 * $Log: SimpleLocation.java,v $
 * Revision 1.1  2005/08/22 15:43:33  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 *
 */