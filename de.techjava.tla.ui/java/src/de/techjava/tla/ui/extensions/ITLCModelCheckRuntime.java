package de.techjava.tla.ui.extensions;

import org.eclipse.core.resources.IResource;

/**
 * Defines basic model checker interface
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: ITLCModelCheckRuntime.java,v 1.1 2005/08/22 15:43:33 szambrovski Exp $
 */
public interface ITLCModelCheckRuntime
{
    /**
     * Starts model check
     * @param resource resources to be checked
     * @return results of model check
     */
    public ITLCModelCheckResult[] startCheck(IResource[] resource);

    /**
     * Stops model check
     * @param resource resources to stop the checking at
     * @return results of model check
     */
    public ITLCModelCheckResult[] stopCheck(IResource[] resource);
    
    /**
     * Cleans files from working directory
     * @return 
     */
    public boolean flushWorkingDirectory();
}

/*
 * $Log: ITLCModelCheckRuntime.java,v $
 * Revision 1.1  2005/08/22 15:43:33  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 *
 */