package de.techjava.tla.ui.util;

import de.techjava.tla.ui.extensions.ITLCModelCheckConfiguration;
import de.techjava.tla.ui.extensions.ITLCModelCheckRuntime;

/**
 * Holder for checker configuration and runtime
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: CheckerExtensionHolder.java,v 1.1 2005/08/22 15:43:31 szambrovski Exp $
 */
public class CheckerExtensionHolder
{
    private ITLCModelCheckRuntime 		runtime;
    private ITLCModelCheckConfiguration	configuration;
    
    public CheckerExtensionHolder()
    {
        
    }
    
    public void setConfiguration(ITLCModelCheckConfiguration configuration)
    {
        this.configuration = configuration;
    }
    
    public void setRuntime(ITLCModelCheckRuntime runtime)
    {
        this.runtime = runtime;
    }
    
    public boolean isValid() {
        return this.configuration != null && this.runtime != null;
    }
    public ITLCModelCheckConfiguration getConfiguration()
    {
        return this.configuration;
    }
    
    public ITLCModelCheckRuntime getRuntime()
    {
        return this.runtime;
    }
    
    
}

/*
 * $Log: CheckerExtensionHolder.java,v $
 * Revision 1.1  2005/08/22 15:43:31  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/13 14:42:53  sza
 * init
 *
 * Revision 1.1  2004/10/13 09:46:02  sza
 * plugin integration
 *
 *
 */