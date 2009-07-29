package org.lamport.tla.toolbox.tool.tlc.job;


import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.debug.core.ILaunch;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink;
import org.lamport.tla.toolbox.tool.tlc.output.internal.BroadcastStreamListener;
import org.lamport.tla.toolbox.util.RCPNameToFileIStream;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tlc2.TLC;
import util.ToolIO;

/**
 * Runs TLC as internal process
 * @author Simon Zambrovski
 * @version $Id$
 * @deprecated
 */
public class TLCInternalJob extends TLCJob
{
    private TLCThread tlcThread;
    private BroadcastStreamListener outputListener;
    int reported;

    /**
     * @param name
     */
    public TLCInternalJob(String specName, String modelName, ILaunch launch)
    {
        super(specName, modelName, launch);
        
        // initialize the progress reporting variable
        reported = 0;
        
        outputListener = new BroadcastStreamListener(modelName, IProcessOutputSink.TYPE_OUT);
    }

    protected IStatus run(IProgressMonitor monitor)
    {
        
        monitor.beginTask("TLC run for " + rootModule.getName(), IProgressMonitor.UNKNOWN);
        
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
        String[] params;
        try
        {
            params = constructProgramArguments();
        } catch (CoreException e)
        {
            return new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID, "Error reading model parameters", e);
        }
        
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
            reportProgress();

            // check the cancellation status
            if (monitor.isCanceled())
            {
                // cancel the TLC
                tlc.setCanceledFlag(true);

                // report the messages created since last reporting
                reportProgress();

                // inform about completion
                outputListener.streamClosed();
                
                // abnormal termination
                return Status.CANCEL_STATUS;
            }
        }
        monitor.worked(STEP);
        
        // handle finish
        doFinish();

        // report progress
        reportProgress();

        // inform about completion
        outputListener.streamClosed();
        
        // successful termination
        return Status.OK_STATUS;
    }

    // decrement the number and sleep
    public boolean checkAndSleep()
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
     * Report progress to the fake listener
     */
    protected void reportProgress()
    {
        // report progress
        String[] messages = ToolIO.getAllMessages();
        for (; reported < messages.length; reported++)
        {
            outputListener.streamAppended(messages[reported], null);
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
                isRunning = true;
            }
            // start TLC
            this.tlc.process();

            synchronized (this)
            {
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
