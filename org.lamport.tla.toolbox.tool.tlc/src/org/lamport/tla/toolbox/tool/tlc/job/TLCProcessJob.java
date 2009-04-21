package org.lamport.tla.toolbox.tool.tlc.job;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.lamport.tla.toolbox.util.ResourceHelper;

/**
 * A job to launch TLC as a separate process
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCProcessJob extends TLCJob
{

    /**
     * @param name
     */
    public TLCProcessJob(IResource rootModule, IResource cfgFile, IResource projectDir)
    {
        super(rootModule, cfgFile, projectDir);
    }

    /* (non-Javadoc)
     * @see org.eclipse.core.runtime.jobs.Job#run(org.eclipse.core.runtime.IProgressMonitor)
     */
    protected IStatus run(IProgressMonitor monitor)
    {
        // init the console
        initConsole();

        monitor.beginTask("Starting", IProgressMonitor.UNKNOWN);

        String[] params = new String[] { 
                "java -cp %CLASSPATH% tlc2.TLC",
                "-config", cfgFile.getName(), 
                //"-coverage", "0.1",
                "-workers", "" + workers,
                "-metadir", projectDir.getLocation().toOSString(),
                ResourceHelper.getModuleName(rootModule) };

        
        try
        {
            Process tlcProcess = Runtime.getRuntime().exec(params, null, this.projectDir.getLocation().toFile());
            BufferedReader in = new BufferedReader(new InputStreamReader(tlcProcess.getInputStream()));
            String text;
            while ((text = in.readLine()) != null)
            {
                println(text);
            }

        } catch (IOException e)
        {
            e.printStackTrace(new PrintStream(outputStream));
        }

        monitor.done();
        return Status.OK_STATUS;
    }
}
