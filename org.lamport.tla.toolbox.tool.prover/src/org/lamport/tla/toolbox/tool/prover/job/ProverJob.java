package org.lamport.tla.toolbox.tool.prover.job;

import java.io.IOException;
import java.util.ArrayList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.Launch;
import org.eclipse.debug.core.model.IProcess;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.tool.prover.output.IProverProcessOutputSink;
import org.lamport.tla.toolbox.tool.prover.output.internal.TLAPMBroadcastStreamListener;
import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;
import org.lamport.tla.toolbox.tool.prover.ui.util.ProverHelper;
import org.lamport.tla.toolbox.tool.prover.ui.view.ObligationsView;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Long running job for launching the prover.
 * 
 * @author Daniel Ricketts
 *
 */
public class ProverJob extends Job
{

    /**
     * the IPath pointing to the module to be checked, e.g.
     *    new Path("C:/Users/drickett/work/svn-repository/examples/HourClock/HourClock.tla")
     */
    private IFile module;
    /**
     * Path to the tlapm executable.
     */
    private IPath tlapmPath;
    /**
     * Path to the folder containing cygwin.
     */
    private IPath cygwinPath;
    /**
     * This is a useless launch object. It is
     * used later to construct an {@link IProcess}. This object
     * provides convenience methods for processes.
     * In particular, an IProcess listens for the termination
     * of the underlying process. It requires a non-null
     * {@link ILaunch} but the {@link ILaunch} can contain
     * a null {@link ILaunchConfiguration}.
     */
    private ILaunch launch;
    /**
     * The process for the prover.
     */
    private IProcess proverProcess;
    /**
     * Broadcasts prover output
     * to registered listeners.
     */
    private TLAPMBroadcastStreamListener listener;
    /**
     * The timeout used when waiting for cancelation
     * of this job.
     */
    protected static final long TIMEOUT = 1000 * 1;
    /**
     * Array holding the coordinates of the job.
     * 
     * {bl, bc, el, ec}
     */
    private int[] coordinates = new int[] { -1, -1, -1, -1 };
    /**
     * True iff fingerprints should be used for
     * the run of the prover.
     */
    private boolean useFP = true;
    /**
     * True iff the entire module should be checked.
     * The value of coordinates will be ignored if
     * this is true.
     */
    private boolean all = false;
    /**
     * If true, the prover will be launched for
     * status checking only, not proving.
     */
    private boolean checkStatus = false;

    /**
     * Constructor. Call {@link ProverJob#setLocation(int, int, int, int)} to set
     * the location of the prover launch.
     * 
     * @param name human readable name for the job, will appear in progress monitor
     * @param module the {@link IFile} pointing to the module on which the prover is being
     * launched
     * @param tlapmPath absolute path to the tlapm executable, or null if it is assumed
     * to be in the system Path
     * @param cygwinPath absolute path to the folder containing cygwin, or null
     * if this is not Windows or the cygwin path is assumed to be in the System Path.
     */
    public ProverJob(String name, IFile module, IPath tlapmPath, IPath cygwinPath)
    {
        super(name);
        this.module = module;

        /*
         * The following sets the path to tlapm.
         */
        Assert.isTrue(Platform.isRunning(), "Platform is not running when prover was launched. This makes no sense.");
        // the default tlapm command on all systems if
        // no complete tlapm path can be found.
        this.tlapmPath = new Path("tlapm");
        if (Platform.getOS().equals(Platform.OS_WIN32))
        {
            /*
             * If tlapmPath is not null, that is the path.
             * 
             * If tlapmPath is null, check if "C:/cygwin/usr/local/bin/tlapm.exe" exists.
             * If it does exist, that is the path. Else, the path is "tlapm". Setting
             * the path to "tlapm" assumes that it is in the system path.
             */
            IPath defaultPath = new Path("C:/cygwin/usr/local/bin/tlapm.exe");
            if (tlapmPath != null)
            {
                this.tlapmPath = tlapmPath;
            } else if (defaultPath.toFile().exists())
            {
                this.tlapmPath = defaultPath;
            }

        } else if (Platform.getOS().equals(Platform.OS_MACOSX) || Platform.getOS().equals(Platform.OS_LINUX))
        {

            /*
             * If tlapmPath is not null, that is the path.
             * 
             * If tlapmPath is null, check if "/usr/local/bin/tlapm" exists.
             * If it does exist, that is the path. Else, the path is tlapm. Setting
             * the path to "tlapm" assumes that it is in the system path.
             */
            IPath defaultPath = new Path("/usr/local/bin/tlapm");
            if (tlapmPath != null)
            {
                this.tlapmPath = tlapmPath;
            } else if (defaultPath.toFile().exists())
            {
                this.tlapmPath = defaultPath;
            }

        } else
        {
            // TODO indicate that the operating system is unsupported
        }

        /*
         * If cygwin path is specified, use that. If not
         * use the default cygwin path : 
         * "C:\cygwin\bin"
         */
        if (cygwinPath != null)
        {
            this.cygwinPath = cygwinPath;
        } else
        {
            this.cygwinPath = new Path("C:\\cygwin\\bin");
        }

        /*
         * We create a useless launch object. It is
         * used later to construct a IProcess. This object
         * provides convenience methods for processes.
         * In particular, an IProcess listens for the termination
         * of the underlying process.
         */
        this.launch = new Launch(null, "", null);
    }

    protected IStatus run(IProgressMonitor monitor)
    {
        try
        {

            IPath modulePath = module.getLocation();

            /*
             * Check that the module exists and that the tlapm
             * and cygwin paths are valid paths, if they aren't null.
             */

            if (!modulePath.toFile().exists())
            {
                ProverUIActivator.logDebug("Module file given to ProverJob does not exist.");
                return new Status(IStatus.ERROR, ProverUIActivator.PLUGIN_ID, "Module file does not exist.");
            } else if (tlapmPath != null && !tlapmPath.toFile().exists())
            {
                ProverUIActivator.logDebug("The given tlapm path does not exist.");
                // TODO show error message to user
                return new Status(IStatus.ERROR, ProverUIActivator.PLUGIN_ID, "The given tlapm path does not exist.");
            } else if (Platform.getOS().equals(Platform.OS_WIN32) && cygwinPath != null
                    && !cygwinPath.toFile().exists())
            {
                // TODO show error message to user
                ProverUIActivator.logDebug("The given cygwin path does not exist.");
                return new Status(IStatus.ERROR, ProverUIActivator.PLUGIN_ID, "The given cygwin path " + cygwinPath
                        + " does not exist.");
            }

            /*
             * Clear obligation markers on the project containing the module.
             * 
             * Refresh the obligations view to reflect the deletion of markers.
             * 
             */
            try
            {
                ProverHelper.clearObligationMarkers(module.getProject());
                UIHelper.runUIAsync(new Runnable() {

                    public void run()
                    {
                        ObligationsView.refreshObligationView();
                    }
                });
            } catch (CoreException e1)
            {
                ProverUIActivator.logError("Error clearing obligation markers for project of module " + modulePath, e1);
            }

            /*
             * Set the module to be read-only.
             */
            EditorUtil.setReadOnly(module, true);

            /*
             * Launch the prover. The path to the tlapm is set in the
             * constructor for this class. Check there for how that is done.
             */

            /*
             * Launch the prover command:
             */
            String[] commandArray = constructCommand();
            ProcessBuilder pb = new ProcessBuilder(commandArray);

            System.out.println("---------------Start Prover Command-----------");
            for (int i = 0; i < commandArray.length; i++)
            {
                System.out.println(commandArray[i]);
            }
            System.out.println("---------------End Prover Command-----------");

            /*
             * Set the working directory to be the directory
             * containing the module.
             */
            pb.directory(modulePath.toFile().getParentFile());

            /*
             * On Windows,
             * the prover requires Cygwin. According to a post
             * on http://stackoverflow.com/questions/1307202/how-can-i-run-cygwin-from-java,
             * 

            If you are trying to run a binary that requires the cygwin1.dll
            (which includes most commands you can execute from the cygwin bash shell)
            then you can run it by specifying the cygwin\bin directory in the path environment variable like this:

            Process p = Runtime.getRuntime().exec(
            "C:/path/to/cygwin/binary.exe", new String[] { "PATH=C:\\cygwin\\bin" });
            
            This assumes you installed cygwin in C:\cygwin
            
             * We actually use the ProcessBuilder class which wraps the
             * Runtime.exec method. It provides a map of environment variables
             * instead of a string array.
             * 
             * On Linux and Mac, I don't think anything extra needs to be done.
             * 
             * The working directory should be set to the one containing
             * the module.
             * 
             * Note that Platform.OS_WIN32 is the only constant for Windows
             * operating systems. The documentation says that it is for
             * 32-bit windows operating systems, but hopefully it also is
             * for 64-bit systems. This needs to be tested.
             */
            if (Platform.isRunning() && Platform.getOS().equals(Platform.OS_WIN32))
            {
                String pathVar = "Path";
                if (cygwinPath != null)
                {
                    pb.environment().put(pathVar, cygwinPath.toOSString() + ";" + pb.environment().get(pathVar));
                }
            }

            pb.redirectErrorStream(true);

            /*
             * Start the process. Calling DebugPlugin.newProcess()
             * wraps the java.lang.Process in an IProcess with some
             * convenience methods.
             */
            proverProcess = DebugPlugin.newProcess(launch, pb.start(), getName());

            if (proverProcess != null)
            {
                /*
                 * Setup the broadcasting of the prover output stream.
                 * 
                 * We name the process using a string representation of the
                 * path to the module.
                 * 
                 * This should allow interested listeners to uniquely identify
                 * the appropriate output.
                 */
                listener = new TLAPMBroadcastStreamListener(modulePath.toPortableString(),
                        IProverProcessOutputSink.TYPE_PROVE, monitor);

                /*
                 * Send a string to the listener indicating
                 * that a new prover job is starting.
                 */
                listener.streamAppended("---------------- New Prover Launch --------------\n", null);

                proverProcess.getStreamsProxy().getErrorStreamMonitor().addListener(listener);
                proverProcess.getStreamsProxy().getOutputStreamMonitor().addListener(listener);

                /*
                 * The following loop checks for job cancellation while
                 * the process is running and terminates the process
                 * if the job is canceled while the process is still running.
                 * 
                 * It handles any errors in terminating the process.
                 */
                while (checkAndSleep())
                {
                    // check the cancellation status
                    if (monitor.isCanceled())
                    {
                        /*
                         * Cancel the prover. This is done
                         * by sending the string "kill\n" to the
                         * prover. The prover takes the appropriate
                         * steps to shut down.
                         */
                        proverProcess.getStreamsProxy().write("kill\n");

                        /*
                         * Wait for the process to actually
                         * kill itself. It can stream data
                         * to the toolbox after the kill string
                         * is sent.
                         */
                        while (checkAndSleep())
                        {

                        }

                        // cancellation termination
                        return Status.CANCEL_STATUS;
                    }
                }

                /*
                 * Check for and handle unsuccessful termination that does not cause an exception
                 * to be thrown. The only cause that I am aware of is not having
                 * the path to cygwin in the system environment path on Windows.
                 */
                try
                {
                    if (proverProcess.isTerminated() && proverProcess.getExitValue() != 0
                            && proverProcess.getExitValue() != 1)
                    {
                        return new Status(
                                IStatus.ERROR,
                                ProverUIActivator.PLUGIN_ID,
                                "Error running tlapm. If this "
                                        + "is Windows, make sure the path to cygwin is in the system path or that the path "
                                        + "to cygwin is specified in the prover preference page. If this does not solve the problem "
                                        + "then report a bug with the error code to the developers at http://bugzilla.tlaplus.net/."
                                        + "\n \n Error code: " + proverProcess.getExitValue());
                    }
                } catch (DebugException e)
                {
                    return new Status(IStatus.ERROR, ProverUIActivator.PLUGIN_ID,
                            "Error getting exit code for tlapm process. This is a bug. Report it to the developers at http://bugzilla.tlaplus.net/");
                }

                // successful termination
                return Status.OK_STATUS;

            } else
            {
                return new Status(IStatus.ERROR, ProverUIActivator.PLUGIN_ID,
                        "Error launching prover. Launching the prover returned a null process.");
            }

        } catch (IOException e)
        {
            /*
             * Handle errors properly.
             * 
             * This should definitely show an error to the user
             * if the tlapm executable is not found or if this is
             * Windows and tlapm crashes because cygwin is not found.
             * 
             * Returning an error status shows a message to the user.
             * We may decide that we want to customize the appearance of the
             * message in which case we would not return a status, but instead
             * we would probably use the MessageDialog class.
             */
            return new Status(
                    IStatus.ERROR,
                    ProverUIActivator.PLUGIN_ID,
                    e.getMessage()
                            + "\n The following could resolve this issue: \n"
                            + "1.) If you did not specify in preferences the path to the tlapm executable, make sure it is in your system path.\n"
                            + "2.) If you specified the absolute path to the tlapm executable in preferences, verify that it is correct.",
                    e);

        } finally
        {
            // send the notification about completion
            if (listener != null)
            {
                listener.streamClosed();
            }
            // make sure to complete the monitor
            monitor.done();

            /*
             * Remove the launch from the launch manager and remove
             * the stream broadcaster as a listener from the process streams.
             * This avoids a memory leak.
             */
            DebugPlugin.getDefault().getLaunchManager().removeLaunch(launch);

            /*
             * The listener and prover process can be null if the prover could
             * not be launched successfully, e.g. an exception was thrown.
             */
            if (proverProcess != null && listener != null)
            {
                proverProcess.getStreamsProxy().getErrorStreamMonitor().removeListener(listener);
                proverProcess.getStreamsProxy().getOutputStreamMonitor().removeListener(listener);
            }

            EditorUtil.setReadOnly(module, false);
        }
    }

    /**
     * Sleeps for {@link #TIMEOUT} and then returns
     * true if the tlapm is still running. Returns false
     * if the tlapm was not launched.
     * @return true, if tlapm is still running
     */
    public boolean checkAndSleep()
    {
        try
        {
            // go sleep
            Thread.sleep(TIMEOUT);

        } catch (InterruptedException e)
        {
            // nothing to do
            // e.printStackTrace();
        }
        // return true if tlapm is still running
        return (proverProcess != null && !proverProcess.isTerminated());
    }

    /**
     * Sets the location of the job. The coordinates should all
     * be 1-based. If setAll(true) is called, the arguments to this method
     * will be ignored.
     * 
     * Note that currently the prover does not consider column
     * numbers, so those arguments are irrelevant.
     * 
     * @param bl begin line
     * @param bc begin column
     * @param el end line
     * @param ec end column
     */
    public void setLocation(int bl, int bc, int el, int ec)
    {
        coordinates = new int[] { bl, bc, el, ec };
    }

    /**
     * Set to false if fingerprints should not be used.
     * Default is true.
     * @param useFP
     */
    public void setUseFP(boolean useFP)
    {
        this.useFP = useFP;
    }

    /**
     * Sets whether the prover should be run
     * on the entire module. Default is false.
     * Setting this to true will make any calls
     * to setCoordinates() have no effect.
     * 
     * @param all true iff the prover should
     * be run on the entire module
     */
    public void setAll(boolean all)
    {
        this.all = all;
    }

    /**
     * This class is used for finding running
     * ProverJobs. One can find all such jobs
     * by calling
     * 
     * Job.getJobManager().find(new ProverJobMatcher());
     * 
     * The job manager finds matches by calling
     * the belongsTo(Object) method for each job with the
     * argument equal to the argument given to the find method.
     * The belongsTo method for this class returns true iff
     * the argument is an instance of ProverJobMatcher.
     * 
     * @author Daniel Ricketts
     *
     */
    public static class ProverJobMatcher
    {
    }

    /**
     * Returns true iff the argument is an instance of ProverJobMatcher.
     * This method is used by the job manager to locate jobs. See
     * {@link ProverJobMatcher}.
     */
    public boolean belongsTo(Object family)
    {
        return family instanceof ProverJobMatcher;
    }

    /**
     * Constructs and returns the command to launch the prover.
     * 
     * @return
     */
    private String[] constructCommand()
    {
        ArrayList command = new ArrayList();
        /*
         * Launch from the command line:
         * 
         * > <tlapm-command> --isaprove --toolbox <loc> moduleName
         * 
         * where <loc> is "bl:el" or "all" if the entire module
         * is to be checked.
         * 
         * Optionally --nofp can be specified to not use fingerprinting.
         * 
         * If no path has been specified (probably in the preferences
         * by the user, then we assume the path to the tlapm has been
         * put in the system Path, and <tlapm-command> is tlapm. If a path
         * has been specified, <tlapm-command> is the path to the tlapm
         * executable.
         * 
         * Module name should end with .tla
         * such as HourClock.tla
         */

        command.add(tlapmPath.toOSString());

        command.add("--isaprove");

        command.add("--toolbox");

        if (all)
        {
            command.add("all");
        } else
        {
            command.add(coordinates[0] + ":" + coordinates[2]);
        }

        if (!useFP)
        {
            command.add("--nofp");
        }

        command.add(module.getLocation().lastSegment());

        return (String[]) command.toArray(new String[command.size()]);
    }
}
