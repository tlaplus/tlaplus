package de.techjava.tla.ui.builders;

import java.util.Map;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;

/**
 * TLA Builder
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLABuilder.java,v 1.1 2005/08/22 15:43:36 szambrovski Exp $
 */
public class TLABuilder 
	extends IncrementalProjectBuilder 
{
	public static final String BUILDER_ID = "de.techjava.tla.ui.builders.TLABuilder";
    /**
	 * @see org.eclipse.core.internal.events.InternalBuilder#build(int, java.util.Map, org.eclipse.core.runtime.IProgressMonitor)
	 */
	protected IProject[] build(int kind, Map args, IProgressMonitor monitor)
		throws CoreException 
	{
	    switch (kind)
	    {
	    	case IncrementalProjectBuilder.FULL_BUILD:
	    	    System.out.println("Running full build");
	    	    runBuild(monitor);
	    	    break;
	    	case IncrementalProjectBuilder.AUTO_BUILD:
	    	    System.out.println("Running auto build");
	    	    runBuild(monitor);
	    	    break;
	    	case IncrementalProjectBuilder.CLEAN_BUILD:
	    	    System.out.println("Running clean build");
	    	    runBuild(monitor);
	    	    break;
	    	case IncrementalProjectBuilder.INCREMENTAL_BUILD:
	    	    System.out.println("Running incremental build");
	    	    runBuild(monitor);
	    	    break;
	    	default:
	    	    break;
	    }
		return null;
	}
	/**
	 * Starts the build process
	 * @throws CoreException
	 */
	private void runBuild(IProgressMonitor monitor)
		throws CoreException
	{
	    try 
	    {
	        getProject().accept(new TLABuildVisitor(monitor));
	    } catch (Exception e)
	    {
	        e.printStackTrace();
	    }
	}
}
