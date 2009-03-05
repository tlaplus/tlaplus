package de.techjava.tla.ui.util;

import de.techjava.tla.ui.extensions.ITLAParserConfiguration;
import de.techjava.tla.ui.extensions.ITLAParserRuntime;

/**
 * Holder for parser configuration and runtime
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: ParserExtensionHolder.java,v 1.1 2005/08/22 15:43:31 szambrovski Exp $
 */
public class ParserExtensionHolder
{
    private ITLAParserRuntime 		runtime;
    private ITLAParserConfiguration	configuration;
    
    public ParserExtensionHolder()
    {
        
    }
    
    public void setConfiguration(ITLAParserConfiguration configuration)
    {
        this.configuration = configuration;
    }
    
    public void setRuntime(ITLAParserRuntime runtime)
    {
        this.runtime = runtime;
    }
    
    public boolean isValid() {
        return this.configuration != null && this.runtime != null;
    }
    public ITLAParserConfiguration getConfiguration()
    {
        return this.configuration;
    }
    
    public ITLAParserRuntime getRuntime()
    {
        return this.runtime;
    }
    
    
}

/*
 * $Log: ParserExtensionHolder.java,v $
 * Revision 1.1  2005/08/22 15:43:31  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/13 09:46:02  sza
 * plugin integration
 *
 *
 */