package de.techjava.tla.ui.util;

import java.util.Hashtable;
import java.util.Vector;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;

import de.techjava.tla.ui.UIPlugin;
import de.techjava.tla.ui.extensions.ITLAParserConfiguration;
import de.techjava.tla.ui.extensions.ITLAParserRuntime;
import de.techjava.tla.ui.extensions.ITLCModelCheckConfiguration;
import de.techjava.tla.ui.extensions.ITLCModelCheckRuntime;

/**
 * Manages the plugin extensions
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: ExtensionManager.java,v 1.1 2005/08/22 15:43:31 szambrovski Exp $
 */
public class ExtensionManager 
{
    public final static String PARSER 	= "parser";
    public final static String CHECKER 	= "modelchecker";
    
    // provides a hash of all plugin extension-points
    private 		Hashtable			extensionHash;
    private 		Vector				parsers 		= new Vector(1);
    private			Vector				modelCheckers 	= new Vector(1);
    
    public ExtensionManager()
    {
        try 
        {
            registerExtensions();
        } catch (CoreException ce)
        {
            ce.printStackTrace();
        }
    }
    
	private void registerExtensions()
		throws CoreException
	{
		System.out.println("Initializing extensions...");
	    IExtensionPoint parserPoint = Platform.getExtensionRegistry().getExtensionPoint(UIPlugin.PLUGIN_ID, PARSER);
	    IExtension[] parserExtensions = parserPoint.getExtensions();
	    
	    for ( int j = 0; j < parserExtensions.length; j++ ) 
		{
			IConfigurationElement[] configElements = parserExtensions[j].getConfigurationElements();
			ParserExtensionHolder parserHolder = new ParserExtensionHolder();
			for ( int k = 0; k < configElements.length; k++ ) 
			{
				Object listener = configElements[k].createExecutableExtension("class");
		
				if (listener instanceof ITLAParserConfiguration) 
				{
				    parserHolder.setConfiguration((ITLAParserConfiguration) listener);
				} 
				
				if (listener instanceof ITLAParserRuntime)
				{
				    parserHolder.setRuntime((ITLAParserRuntime) listener);
				}
			}
			if (parserHolder.isValid())
			{
			    parsers.add(parserHolder);
			}
		
		}

	    IExtensionPoint checkerPoint = Platform.getExtensionRegistry().getExtensionPoint(UIPlugin.PLUGIN_ID, CHECKER);
	    IExtension[] checkerExtensions = checkerPoint.getExtensions();
	    
	    for ( int j = 0; j < checkerExtensions.length; j++ ) 
		{
			IConfigurationElement[] configElements = checkerExtensions[j].getConfigurationElements();
			CheckerExtensionHolder checkerHolder = new CheckerExtensionHolder();
			for ( int k = 0; k < configElements.length; k++ ) 
			{
				Object listener = configElements[k].createExecutableExtension("class");
		
				if (listener instanceof ITLCModelCheckConfiguration) 
				{
				    checkerHolder.setConfiguration((ITLCModelCheckConfiguration) listener);
				} 
				
				if (listener instanceof ITLCModelCheckRuntime)
				{
				    checkerHolder.setRuntime((ITLCModelCheckRuntime) listener);
				}
			}
			if (checkerHolder.isValid())
			{
			    modelCheckers.add(checkerHolder);
			}
		
		}

	    System.out.println("Initialized.");
	}
	/**
	 * Retrieves parser configuration
	 * @return
	 * @throws CoreException
	 */
	public ITLAParserConfiguration getParserConfiguration()
		throws CoreException
	{
	    if (parsers.size() == 1)
	    {
	        if (((ParserExtensionHolder)parsers.get(0)).isValid())
	        {
	            return ((ParserExtensionHolder)parsers.get(0)).getConfiguration();
	        } else {
	            throw new CoreException(new Status(Status.ERROR, UIPlugin.PLUGIN_ID, 0, "Error retrieving the parser configuration", new IllegalStateException("Parser and parser configuration must be both set")));
	        }
	    } else {
	        throw new CoreException(new Status(Status.ERROR, UIPlugin.PLUGIN_ID, 0, "Error retrieving the parser configuration", new IllegalStateException("Wrong number of parsers : " + parsers.size())));    
	    }
	    
	}
    /**
     * Retrieves a parser runtime instance
     * @return
     * @throws CoreException
     */
    public ITLAParserRuntime getParserRuntime()
    	throws CoreException
    {
	    if (parsers.size() == 1)
	    {
	        if (((ParserExtensionHolder)parsers.get(0)).isValid())
	        {
	            return ((ParserExtensionHolder)parsers.get(0)).getRuntime();
	        } else {
	            throw new CoreException(new Status(Status.ERROR, UIPlugin.PLUGIN_ID, 0, "Error retrieving the parser runtime", new IllegalStateException("Parser and parser configuration must be both set")));
	        }
	    } else {
	        throw new CoreException(new Status(Status.ERROR, UIPlugin.PLUGIN_ID, 0, "Error retrieving the parser runtime", new IllegalStateException("Wrong number of parsers : " + parsers.size())));    
	    }
    }
    /**
     * Retrieves TLC ModelChecker Configuration
     * @return
     * @throws CoreException
     */
    public ITLCModelCheckConfiguration getModelCheckConfiguration() 
		throws CoreException
    {
	    if (modelCheckers.size() == 1)
	    {
	        if (((CheckerExtensionHolder)modelCheckers.get(0)).isValid())
	        {
	            return ((CheckerExtensionHolder)modelCheckers.get(0)).getConfiguration();
	        } else {
	            throw new CoreException(new Status(Status.ERROR, UIPlugin.PLUGIN_ID, 0, "Error retrieving the checker configuration", new IllegalStateException("Checker and checker configuration must be both set")));
	        }
	    } else {
	        throw new CoreException(new Status(Status.ERROR, UIPlugin.PLUGIN_ID, 0, "Error retrieving the parser configuration", new IllegalStateException("Wrong number of checkers : " + modelCheckers.size())));    
	    }

    }
    /**
     * Retrieves TLC ModelChecker Runtime
     * @return
     * @throws CoreException
     */
    public ITLCModelCheckRuntime getModelCheckerRuntime() 
		throws CoreException
    {
	    if (modelCheckers.size() == 1)
	    {
	        if (((CheckerExtensionHolder)modelCheckers.get(0)).isValid())
	        {
	            return ((CheckerExtensionHolder)modelCheckers.get(0)).getRuntime();
	        } else {
	            throw new CoreException(new Status(Status.ERROR, UIPlugin.PLUGIN_ID, 0, "Error retrieving the checker runtime", new IllegalStateException("Checker and checker configuration must be both set")));
	        }
	    } else {
	        throw new CoreException(new Status(Status.ERROR, UIPlugin.PLUGIN_ID, 0, "Error retrieving the checker runtime", new IllegalStateException("Wrong number of checkers : " + modelCheckers.size())));    
	    }

    }


}

/*
 * $Log: ExtensionManager.java,v $
 * Revision 1.1  2005/08/22 15:43:31  szambrovski
 * sf cvs init
 *
 * Revision 1.6  2004/10/13 17:14:31  bgr
 * launcher built
 *
 * Revision 1.5  2004/10/13 14:43:43  sza
 * added modelchecker
 *
 * Revision 1.4  2004/10/13 10:50:56  bgr
 * ids changed
 *
 * Revision 1.3  2004/10/13 09:46:02  sza
 * plugin integration
 *
 * Revision 1.2  2004/10/12 16:47:23  sza
 * removed compilation probelms
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.1  2004/10/12 09:55:12  sza
 * additions
 *
 *
 */