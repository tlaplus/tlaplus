package org.lamport.tla.toolbox.tool.tlc.job;

import java.io.IOException;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.jface.action.Action;
import org.eclipse.ui.console.IOConsoleOutputStream;
import org.lamport.tla.toolbox.tool.tlc.ui.ConsoleFactory;

/**
 * Abstract TLC job
 * @author Simon Zambrovski
 * @version $Id$
 */
public abstract class TLCJob extends AbstractJob
{

    protected IResource rootModule;
    protected IResource cfgFile;
    protected IResource projectDir;
    protected int workers = 1;
    protected IOConsoleOutputStream outputStream = ConsoleFactory.getTLCConsole().newOutputStream();


    /**
     * @param rootModule
     * @param cfgFile
     * @param projectDir
     */
    public TLCJob(IResource rootModule, IResource cfgFile, IResource projectDir)
    {
        super("TLC run for " + rootModule.getName());
        this.rootModule = rootModule;
        this.cfgFile = cfgFile;
        this.projectDir = projectDir;
    }

    /**
     * Sets the number of workers
     * @param workers number of threads to be run in parallel
     */
    public void setWorkers(int workers)
    {
        this.workers = workers;
    }

    protected Action getJobCompletedAction()
    {
        return new Action("View job results") 
        {
            public void run()
            {
                // TODO
                System.out.println("Results viewed");
            }
        };
    }

    /**
     * The run method
     */
    protected abstract IStatus run(IProgressMonitor monitor);

    /**
     * @param string
     */
    protected void println(String string)
    {
        try
        {
            outputStream.write(string);
            outputStream.write("\n");
        } catch (IOException e)
        {
            e.printStackTrace();
        }
    }

    /**
     * Initilizes the console and shows the view 
     */
    protected void initConsole()
    {
        ConsoleFactory.getTLCConsole().activate();
    }
}