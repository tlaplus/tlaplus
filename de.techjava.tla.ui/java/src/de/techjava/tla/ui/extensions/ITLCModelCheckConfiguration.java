package de.techjava.tla.ui.extensions;

import java.util.Map;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IPath;

/**
 * defines basic model checker configuration
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: ITLCModelCheckConfiguration.java,v 1.1 2005/08/22 15:43:33 szambrovski Exp $
 */
public interface ITLCModelCheckConfiguration 
{
    public final static String MODEL_CHECK_DEADLOCK 		= "CheckDeadlock";
    public final static String MODEL_RUN_IN_SIMULATE_MODE 	= "RunSimmulation";
    public final static String MODEL_RUN_DEPTH 				= "RunDepth";
    public final static String MODEL_USE_WITH_SEED 			= "useWithSeed";
    public final static String MODEL_WITH_SEED 				= "WithSeed";
    public final static String MODEL_USE_WITH_ARIL 			= "useWithAril";
    public final static String MODEL_WITH_ARIL 				= "WithAril";
    public final static String MODEL_PRINT_COVERAGE 		= "PrintCoverage";
    public final static String MODEL_USE_RECOVER_FROM 		= "useRecoverFrom";
    public final static String MODEL_RECOVER_FROM 			= "RecoverFrom";
    public final static String MODEL_USE_DIFF_TRACE 		= "useDiffTrace";
    public final static String MODEL_DIFF_TRACE 			= "DiffTrace";
    public final static String MODEL_TERSE 					= "Terse";
    public final static String MODEL_WORKER_COUNT			= "WorkerCount";
    public final static String MODEL_NO_WARNINGS			= "NoWarnings";
    
    
    
    public final static boolean MODEL_CHECK_DEADLOCK_DEFAULT 		= false;
    public final static boolean MODEL_RUN_IN_SIMULATE_MODE_DEFAULT 	= false;
    public final static String  MODEL_RUN_DEPTH_DEFAULT 			= "100";
    public final static boolean MODEL_USE_WITH_SEED_DEFAULT 		= false;
    public final static String  MODEL_WITH_SEED_DEFAULT 			= "1";
    public final static boolean MODEL_USE_WITH_ARIL_DEFAULT 		= false;
    public final static String  MODEL_WITH_ARIL_DEFAULT 			= "1";
    public final static String  MODEL_PRINT_COVERAGE_DEFAULT 		= "10";
    public final static boolean MODEL_USE_RECOVER_FROM_DEFAULT 		= false;
    public final static String  MODEL_RECOVER_FROM_DEFAULT 			= "1";
    public final static boolean MODEL_USE_DIFF_TRACE_DEFAULT 		= false;
    public final static String  MODEL_DIFF_TRACE_DEFAULT 			= "1";
    public final static boolean MODEL_TERSE_DEFAULT					= false;
    public final static String  MODEL_WORKER_COUNT_DEFAULT			= "1";
    public final static boolean MODEL_NO_WARNINGS_DEFAULT			= false;
    
    
    /**
     * Retrieves configuration file name
     * @return
     */
    public IResource getConfigFilename();
    /**
     * Sets configuration file name  
     */
    public void setConfigFileName(IResource configpath);
    /**
     * Retrieves the config directory
     * @return
     */
    public IPath getConfigDirectory();
    /**
     * Retrieves the module library paths
     * @return
     */
    public IPath[] getModuleLibraryPath();
    /**
     * Retrirves the source directory
     * @return
     */
    public IPath getRootDirectory();
    /**
     * Retrieves switches
     * @return
     */
    public Map getSwitches();
    /**
     * Retrieves working directory
     * @return
     */
    public IPath getWorkingDirectory();
    /**
     * Sets the module library path
     * @param paths
     */
    public void setModuleLibraryPath(IPath[] paths);
    /**
     * Sets the configuration directory
     * @param path
     */
    public void setConfigDirectory(IPath path);
    /**
     * Sets source directory
     * @param path
     */
    public void setRootDirectory(IPath path);
    /**
     * Sets switches
     * @param properties
     */
    public void setSwitches(Map properties);
    /**
     * Sets working directory
     * @param path
     */
    public void setWorkingDirectory(IPath path);

}

/*
 * $Log: ITLCModelCheckConfiguration.java,v $
 * Revision 1.1  2005/08/22 15:43:33  szambrovski
 * sf cvs init
 *
 * Revision 1.6  2004/10/26 14:24:54  sza
 * configuration file support added
 *
 * Revision 1.5  2004/10/20 14:01:39  bgr
 * runtime configuration written through to the simulator
 *
 * Revision 1.4  2004/10/14 22:22:00  sza
 * simulate mode changed
 *
 * Revision 1.3  2004/10/14 21:38:17  bgr
 * checker runtime conf added
 *
 * Revision 1.2  2004/10/13 17:14:31  bgr
 * launcher built
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 *
 */