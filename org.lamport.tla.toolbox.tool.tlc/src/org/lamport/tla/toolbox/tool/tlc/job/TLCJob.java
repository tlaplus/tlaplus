package org.lamport.tla.toolbox.tool.tlc.job;

import java.io.IOException;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.action.Action;
import org.eclipse.ui.console.IOConsoleOutputStream;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.ConsoleFactory;
import org.lamport.tla.toolbox.util.RCPNameToFileIStream;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tlc2.TLC;
import util.ToolIO;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCJob extends AbstractJob
{
    private static final long TIMEOUT = 1000 * 5;
    private static final int STEP = 30;

    private IResource rootModule;
    private IResource cfgFile;
    private IResource projectDir;
    
    private TLCThread tlcThread;
    private int workers = 1;
    
    private IOConsoleOutputStream outputStream = ConsoleFactory.getTLCConsole().newOutputStream();
    

    int reported;

    /**
     * @param name
     */
    public TLCJob(IResource rootModule, IResource cfgFile, IResource projectDir)
    {
        super("TLC run for " + rootModule.getName());
        
        this.rootModule = rootModule;
        this.cfgFile = cfgFile;
        this.projectDir = projectDir;

        // initialize the progress reporting variable
        reported = 0;
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

    protected IStatus run(IProgressMonitor monitor)
    {
        monitor.beginTask("TLC run for " + rootModule.getName(), IProgressMonitor.UNKNOWN);

        
        // open the console
        ConsoleFactory.getTLCConsole().activate();
        
        
        monitor.subTask("Preparing the tool environment");
        // setup tool io
        // Reset the tool output messages.
        ToolIO.reset();
        ToolIO.setMode(ToolIO.TOOL);
        ToolIO.setUserDir(ResourceHelper.getParentDirName(rootModule));
        monitor.worked(STEP);
        
        
        monitor.subTask("Initilizing TLC");
        // create a TLC instance
        TLC tlc = new TLC();

        // setup name resolver
        tlc.setResolver(new RCPNameToFileIStream(null));

        // setup SpecObj from parser
        // SpecObj specObj = ToolboxHandle.getSpecObj();
        // tlc.setSpecObject(specObj);

        // handle parameters
        String[] params = new String[] { "-config", cfgFile.getName(), 
                                         //"-coverage", "0.1",
                                         "-workers", "" + workers,
                                         "-metadir", projectDir.getLocation().toOSString(),
                                         ResourceHelper.getModuleName(rootModule) };
        boolean status = tlc.handleParameters(params);
        
        // report errors in parameters
        if (!status)
        {
            return new Status(Status.ERROR, TLCActivator.PLUGIN_ID, "Error processing arguments");
        }
        monitor.worked(STEP);

        
        
        // create thread for TLC running
        tlcThread = new TLCThread(tlc);
        
        monitor.subTask("Starting TLC processing");

        // Start the TLC thread
        tlcThread.start();
        monitor.worked(STEP);

        monitor.subTask("Runing TLC");
        while (this.checkAndSleep())
        {
            // report the messages created since last reporting
            reportProgress(monitor);

            // check the cancellation status
            if (monitor.isCanceled())
            {
                // cancel the TLC
                tlc.setCanceledFlag(true);

                // report the messages created since last reporting
                reportProgress(monitor);

                // abnormal termination
                return Status.CANCEL_STATUS;
            }
        }
        monitor.worked(STEP);
        
        // handle finish
        doFinish();

        // report progress
        reportProgress(monitor);

        // successful termination
        return Status.OK_STATUS;
    }

    // decrement the number and sleep
    private boolean checkAndSleep()
    {
        try
        {
            // go sleep
            Thread.sleep(TIMEOUT);

        } catch (InterruptedException e)
        {
            // nothing to do
            e.printStackTrace();
        }
        // return true if the TLC is still calculating
        return (tlcThread.isRunning());
    }

    /**
     * Report progress to the monitor 
     * @param monitor
     * TODO 
     */
    protected void reportProgress(IProgressMonitor monitor)
    {
        // report progress

        String[] messages = ToolIO.getAllMessages();
        for (; reported < messages.length; reported++)
        {
            println(messages[reported]);
        }
    }

    /**
     * @param string
     */
    private void println(String string)
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
     * Thread to run TLC in
     */
    class TLCThread extends Thread
    {
        private boolean isRunning = false;
        private final TLC tlc;

        public TLCThread(TLC tlc)
        {
            this.tlc = tlc;
        }

        public void run()
        {
            synchronized (this)
            {
                println("TLC Thread {STARTED} -------------");
                isRunning = true;
            }
            // start TLC
            this.tlc.process();

            synchronized (this)
            {
                println("TLC Thread {FINISHED} ------------");
                isRunning = false;
            }
        }

        /**
         * 
         * @return
         */
        public synchronized boolean isRunning()
        {
            return isRunning;
        }
    }

}
