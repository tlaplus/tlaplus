package de.techjava.tla.ui.extensions;


/**
 * Represents the parser result
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: ITLAParserResult.java,v 1.1 2005/08/22 15:43:33 szambrovski Exp $
 */
public interface ITLAParserResult 
{
    public IProblemContainer getInitErrors();
    public IProblemContainer getParseErrors();
    public IProblemContainer getSemanticErrors();
}

/*
 * $Log: ITLAParserResult.java,v $
 * Revision 1.1  2005/08/22 15:43:33  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 *
 */