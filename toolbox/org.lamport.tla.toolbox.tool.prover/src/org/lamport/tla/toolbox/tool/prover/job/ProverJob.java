package org.lamport.tla.toolbox.tool.prover.job;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.core.runtime.jobs.MultiRule;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.Launch;
import org.eclipse.debug.core.model.IFlushableStreamMonitor;
import org.eclipse.debug.core.model.IProcess;
import org.eclipse.debug.core.model.IStreamMonitor;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.TextSelection;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.spec.parser.IParseConstants;
import org.lamport.tla.toolbox.spec.parser.ModuleParserLauncher;
import org.lamport.tla.toolbox.spec.parser.ParseResult;
import org.lamport.tla.toolbox.tool.prover.output.internal.TLAPMBroadcastStreamListener;
import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;
import org.lamport.tla.toolbox.tool.prover.ui.output.TagBasedTLAPMOutputIncrementalParser;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ColorPredicate;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ObligationStatus;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ObligationStatusMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.StepStatusMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.StepTuple;
import org.lamport.tla.toolbox.tool.prover.ui.preference.ColorPredicatePreferencePage;
import org.lamport.tla.toolbox.tool.prover.ui.util.ProverHelper;
import org.lamport.tla.toolbox.tool.prover.ui.util.TLAPMExecutableLocator;
import org.lamport.tla.toolbox.tool.prover.ui.view.ObligationsView;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tla2sany.semantic.LevelNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.TheoremNode;
import util.UniqueString;

/**
 * Long running job for launching the prover. Look at the constructor
 * and the run method for information about this job.
 * 
 * @author Daniel Ricketts
 */
public class ProverJob extends Job {
    /**
     * The time that the run method was called.
     * This is the time in milliseconds returned
     * by {@link System#currentTimeMillis()}.
     */
    private long startTime;
    /**
     * A flag used strictly for debugging
     * that is true iff no obligation status
     * messages with status "to be proved" have been
     * processed yet.
     */
    private boolean noToBeProved = true;
    /**
     * A flag that is true iff the only
     * obligation status messages to be
     * sent to the toolbox so far for
     * this launch of the prover have
     * status {@link ProverHelper#TO_BE_PROVED}.
     */
    private boolean toBeProvedOnly = true;
    /**
     * The most prover job that led to the most
     * recent launch of the prover.
     */
    private static ProverJob lastJob;

    /**
     * The {@link IFile} pointing to the module to be checked.
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
     * The timeout used when waiting for cancellation
     * of this job.
     */
    protected static final long TIMEOUT = 100 * 1;
    /**
     * If true, the PM will be launched for
     * status checking only, not proving.
     */
    private boolean checkStatus = false;
    /**
     * True iff the PM should be launched
     * with the {@link ITLAPMOptions#TOOLBOX}
     * option.
     */
    private boolean toolboxMode = true;
    /**
     * The options used to launch the PM in an array, e.g. {"--paranoid","--threads","2"}.
     * The elements in the array would normally be separated by a space in the command line. This
     * array should NOT contain the --toolbox option or the --noproving option.
     */
    private String[] options;
    /**
     * The full command used to launch the PM.
     */
    private String[] command;
    /**
     * The node on which the prover will be launched.
     * Set in the constructor. If left null, the prover
     * will be launched on the entire module.
     */
    private LevelNode nodeToProve;
    /**
     * A character offset on the line of the step or leaf proof on which the prover will be launched. This will
     * launch the prover on the first step on that line, or if the line contains only a leaf proof, it will launch
     * the prover on the step for which that is a leaf proof. If the line does not contain a leaf proof or a step,
     * the prover will be launched on the entire module.
     */
    private int offset;
    /**
     * Map from {@link Integer} line numbers of steps to
     * the last {@link StepStatusMessage} reported by the prover
     * for that step.
     */
    private Map<Integer, StepStatusMessage> stepMessageMap = new HashMap<Integer, StepStatusMessage>();
    /**
     * Map from {@link Integer}s to {@link StepTuple}s.
     * The integer keys give the begin line of the step
     * tuple. This is the begin line reported by sany
     * for that step at the time that this job was run.
     * This is only for step tuples that represent leaf
     * steps.
     */
    private Map<Integer, StepTuple> leafStepMap = new TreeMap<Integer, StepTuple>();
    /**
     * Map from {@link Integer} ids of obligations
     * to {@link ObligationStatus}
     */
    private Map<Integer, ObligationStatus> obsMap = new HashMap<Integer, ObligationStatus>();
    /**
     * A list of all obligation message with
     * status {@link ProverHelper#TO_BE_PROVED} that
     * have been sent so far.
     */
    private List<ObligationStatusMessage> obMessageList = new LinkedList<ObligationStatusMessage>();
    /**
     * The color predicates that were set in preferences at the
     * time of the launch of the prover by this job.
     */
    private ColorPredicate[] colorPredicates;

    /**
     * Constructor. This constructor sets the appropriate scheduling rule for this job, so there is no
     * need to call {@link #setRule(org.eclipse.core.runtime.jobs.ISchedulingRule)}.
     * @param module the module on which the prover is being launched.
     * @param offset a character offset on the line of the step or leaf proof on which the prover will be launched. This will
     * launch the prover on the first step on that line, or if the line contains only a leaf proof, it will launch
     * the prover on the step for which that is a leaf proof. If the line does not contain a leaf proof or a step,
     * the prover will be launched on the entire module. Setting the offset to -1 will cause the PM to be launched
     * on the entire module.
     * @param checkStatus true iff the PM should be launched for status checking only
     * @param options the options used to launch the PM in an array, e.g. {"--paranoid","--threads","2"}.
     * The elements in the array would normally be separated by a space in the command line. This
     * array should NOT contain the --toolbox option or the --noproving option. This job will put
     * those options in. The --noproving options should be specified using the checkStatus argument.
     * This argument can be null if no additional options are to be used.
     * @param toolboxMode true iff the
     */
    public ProverJob(IFile module, int offset, boolean checkStatus, String[] options, boolean toolboxMode)
    {
        super(checkStatus ? "Status Checking Launch" : "Prover Launch");
        this.checkStatus = checkStatus;
        this.toolboxMode = toolboxMode;
        this.module = module;
        this.offset = offset;
        this.options = options;

        /*
         * Running this job can potentially result in parsing
         * the module. This can result in changes to the workspace (because
         * of markers removed from or placed on parse errors). This must
         * be indicated in the scheduling rule for this job. We do this
         * by using a multi rule that includes the ProverJobRule and the
         * rule associated with the root of the workspace. If this is not done,
         * an exception can be thrown. See the comments for MultiRule
         * and read the article http://www.eclipse.org/articles/Article-Concurrency/jobs-api.html
         * for more information on eclipse Jobs.
         */
        setRule(new MultiRule(new ISchedulingRule[] { new ProverJobRule(), this.module.getWorkspace().getRoot() }));

        /*
         * The following sets the path to tlapm.
         */
        Assert.isTrue(Platform.isRunning(), "Platform is not running when prover was launched. This makes no sense.");
        
        final TLAPMExecutableLocator locator = TLAPMExecutableLocator.INSTANCE;
        this.tlapmPath = locator.getTLAPMPath();
        this.cygwinPath = locator.getCygwinPath();

        /*
         * We create a useless launch object. It is
         * used later to construct a IProcess. This object
         * provides convenience methods for processes.
         * In particular, an IProcess listens for the termination
         * of the underlying process.
         */
        this.launch = new Launch(null, "", null);
    }

    /**
     * This method is called by eclipse at some appropriate point after
     * the job is scheduled. Check out
     * http://www.eclipse.org/articles/Article-Concurrency/jobs-api.html
     * for more information on eclipse jobs.
     * 
     * This method performs the necessary preparation for running the PM, launches
     * the PM, and attaches the appropriate listener to the output of the PM. It
     * also handles cancellation of the job.
     */
    protected IStatus run(IProgressMonitor monitor)
    {
        this.startTime = System.currentTimeMillis();
        ProverUIActivator.getDefault().logDebug("Run method called " + getCurRelTime());

        /*
         * Create the ColorPredicate objects.
         * 
         * Note that color numbers for the preference page are 1-based.
         */
        colorPredicates = new ColorPredicate[ColorPredicatePreferencePage.NUM_STATUS_COLORS];

        // the preference store containing color predicate preferences
        IPreferenceStore store = ProverUIActivator.getDefault().getPreferenceStore();
        for (int i = 1; i <= colorPredicates.length; i++)
        {
            String predicate = store.getString(ColorPredicatePreferencePage.getColorPredPrefName(i));
            boolean appliesToLeafOnly = store.getBoolean(ColorPredicatePreferencePage.getAppliesToLeafPrefName(i));
            colorPredicates[i - 1] = new ColorPredicate((appliesToLeafOnly ? "leaf " : "") + predicate);
        }

        /*
         * Initialize the fields nodeToProve and module.
         * 
         * See the comments for initialize fields for more information
         * on what it does.
         */
        initializeFields();

        /*
         * If nodeToProve is null after this, then this means
         * that the module was not parsed successfully, so
         * the prover cannot be run.
         */
        if (nodeToProve == null)
        {
            return new Status(IStatus.INFO, ProverUIActivator.PLUGIN_ID,
                    "The module has parse errors. The prover cannot be run.");
        }

        try
        {

            IPath modulePath = module.getLocation();

            /*
             * Check that the module exists and that the tlapm
             * and cygwin paths are valid paths, if they aren't null.
             */

            if (!modulePath.toFile().exists())
            {
                ProverUIActivator.getDefault().logDebug("Module file given to ProverJob does not exist.");
                return new Status(IStatus.ERROR, ProverUIActivator.PLUGIN_ID, "Module file does not exist.");
            } else if (Platform.getOS().equals(Platform.OS_WIN32) && cygwinPath != null
                    && !cygwinPath.toFile().exists())
            {
                // TODO show error message to user
                ProverUIActivator.getDefault().logDebug("The given cygwin path does not exist.");
                return new Status(IStatus.ERROR, ProverUIActivator.PLUGIN_ID, "The given cygwin path " + cygwinPath
                        + " does not exist.");
            }

            /*
             * Set the last run prover job to be this one.
             * We have to be careful where we set the pointer to the
             * last run prover job.
             */
            lastJob = this;

            /**************************************************************
             * The following performs some cleanup and preparation work   *                                                
             **************************************************************/
            try
            {
                /*
                 * Clear obligation markers on the project containing the module.
                 */
                ProverHelper.clearObligationMarkers(module.getProject());

                /*
                 * Refresh the obligations view to reflect the deletion of markers.
                 */
                ObligationsView.refreshObligationView();

                /*
                 * Perform the necessary work to prepare for the launch of the prover.
                 * See the method comments to understand what is done.
                 */
                ProverHelper.prepareModuleForProverLaunch(module, this);
            } catch (CoreException e1)
            {
                ProverUIActivator.getDefault().logError("Error clearing obligation markers for project of module " + modulePath, e1);
            }
            /**************************************************************
             * Finished with preparation work.                            *
             **************************************************************/

            //  On 7 Nov 2011, LL commented out the following code so that the file can be edited while
            //  the prover is being run.  It's useful to be able to do this on a long run.  If the user
            //  is doing this, he presumably knows the risks.
            /*
             * Set the module to be read-only only if this is
             * not a status check launch.
             */
            //if (!checkStatus)
            //{
            //    EditorUtil.setReadOnly(module, true);
            //}

            /*
             * Launch the prover. The path to the tlapm is set in the
             * constructor for this class. Check there for how that is done.
             */

            /*
             * Launch the prover command:
             */
            command = constructCommand();
            ProcessBuilder pb = new ProcessBuilder(command);

            // log command line
            ProverUIActivator.getDefault().logDebug(
            		"Prover ARGUMENTS: " +
            		Arrays.toString(command));

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
             * Start the prover process.
             */
            ProverUIActivator.getDefault().logDebug("TLAPM launched " + getCurRelTime());
            Process process = pb.start();
            setUpStreamListening(process, monitor);

            if (proverProcess != null)
            {
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
                        ProverUIActivator.getDefault().logDebug("Sent kill to tlapm.");

                        /*
                         * Wait for the process to actually
                         * kill itself. It can stream data
                         * to the toolbox after the kill string
                         * is sent.
                         */
                        while (checkAndSleep())
                        {
                            // ProverUIActivator.getDefault().logDebug("Cancel requested. The toolbox still thinks the prover is running.");
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
                    if (proverProcess.isTerminated() && proverProcess.getExitValue() == 2)
                    {
                        return new Status(IStatus.ERROR, ProverUIActivator.PLUGIN_ID,
                                "Incorrect arguments to the PM. The command to launch the PM was :\n"
                                        + getLaunchProverCommand());
                    }
                    if (proverProcess.isTerminated() && proverProcess.getExitValue() != 0
                            && proverProcess.getExitValue() != 1)
                    {
                        return new Status(IStatus.ERROR, ProverUIActivator.PLUGIN_ID,
                                "Error running tlapm. Report a bug with the error code to the developers at https://github.com/tlaplus/tlapm/issues."
                                        + "\n \n Error code: " + proverProcess.getExitValue());
                    }
                } catch (DebugException e)
                {
                    return new Status(IStatus.ERROR, ProverUIActivator.PLUGIN_ID,
                            "Error getting exit code for tlapm process. This is a bug. Report it to the developers at https://github.com/tlaplus/tlapm/issues");
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
             * Handle errors. I don't know what errors can occur here, so for now
             * we will just use the message from the exception.
             * 
             * Returning an error status shows a message to the user.
             * We may decide that we want to customize the appearance of the
             * message in which case we would not return a status, but instead
             * we would probably use the MessageDialog class.
             */
            return new Status(IStatus.ERROR, ProverUIActivator.PLUGIN_ID,
                    "The following error occurred while running the PM : \n" + e.getMessage(), e);

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
            ProverUIActivator.getDefault().logDebug("Done with proving " + getCurRelTime());

            EditorUtil.setReadOnly(module, false);

            /*
             * Always remove SANY markers at the end
             * of the (attempted) run of the prover, regardless of
             * whether it was successful or not because they
             * are no longer needed.
             */
            try
            {
                ProverHelper.removeSANYStepMarkers(module);
            } catch (CoreException e)
            {
                ProverUIActivator.getDefault().logError("Error removing SANY step markers after prover finished running.", e);
            }
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

        List<String> command = new ArrayList<String>();
        /*
         * Launch from the command line:
         * 
         * > <tlapm-command> --toolbox <loc> <options> moduleName
         * 
         * where <loc> is "bl el". If the entire module
         * is to be checked, bl = el = 0.
         * 
         * Module name should end with .tla
         * such as HourClock.tla
         */

        command.add(tlapmPath.toOSString());

		// Use Windows Subsystem for Linux instead of Cygwin. This is experimental and
		// a hack.  A user has to enter wsl.exe or C:\Windows\system32\wsl.exe on the
        // Toolbox's preference page.  The next if block the appends 'tlapm'. 
        final boolean useWSL = tlapmPath.toOSString().contains("wsl.exe");
        if (useWSL) {
			// Assume tlapm is on PATH in the Linux subsystem. With this, prefixing the
			// command with 'wsl' tells Windows to invoke the binary (tlapm) via WSL. I
			// expect this to only work with a single WSL distro installed (otherwise, we
			// probably have to choose a distro). More information and how to install WSL is
			// at https://docs.microsoft.com/en-us/windows/wsl/wsl2-install.
    		command.add("tlapm");
        }

        if (toolboxMode)
        {
            command.add("--toolbox");

            /*
             * The following adds the location to the
             * command. The location is given by "bl el"
             * or "0 0" for the entire module. However, adding
             * the string "<bl> <el>" to the command will not
             * work because java will tell the prover that
             * "12 14" is one argument rather than two separated
             * by a space. Thus, the prover will try to parse
             * "12 14" into an integer instead of into two integers.
             * Adding the two integers as separate arguments works.
             */
            if (nodeToProve instanceof ModuleNode)
            {
                command.add("0");
                command.add("0");
            } else
            {
                /*
                 * Get the begin line and end line of the node.
                 */
                int beginLine = getBeginLine(nodeToProve);
                int endLine = getEndLine(nodeToProve);

                command.add("" + beginLine);
                command.add("" + endLine);
            }
        }

        /*
         * Add threads option, if there is one.
         */
        ProverHelper.setThreadsOption(command);

        /*
         * Add solver option, if there is one.
         */
        ProverHelper.setSolverOption(command);

        /*
         * Add --safefp option, if there is one.
         */
        ProverHelper.setSafeFPOption(command);

        if (checkStatus)
        {
            // Denis reported adding this tlapm switch on 19 Jun 2010
            command.add("--noproving");
        }

        // put in additional options
        if (options != null)
        {
            for (int i = 0; i < options.length; i++)
            {
                command.add(options[i]);
            }
        }
        // Following code added by LL on 30 Nov 2012.  It
        // sets pathList to the array of library paths specified in the Preferences
        // menu.  It then gives them to tlapm as -I options, in reverse order.
        // SANY searches the library paths in the order they're specified in the
        // preference menu; tlapm seems to search them in the inverse order of the
        // -I options.
        String[] pathList = Activator.getSpecManager().getSpecLoaded().getTLALibraryPath();
        if (pathList != null) {
            for (int i=0; i < pathList.length; i++) {
                command.add("-I") ;
                if (useWSL) {
					// 'wslpath' is executed inside the Linux subsystem. It converts an UNC (?) path
					// such as "C:\\Users\\markus\\Library\\dir\\" to something that can be resolved
					// in the Linux subsystem. Unfortunately, pathList[n] =
					// "C:\Users\markus\Library\dir" which is why we replace \\ with \\\\
					// backslashes.
    				command.add(String.format("$(wslpath %s)", pathList[pathList.length - i - 1].replace("\\", "\\\\")));
                } else {
                    command.add(pathList[pathList.length - i - 1]) ;
                }
            }
        }
        
        if (useWSL) {
        	// See pathList above about wslpath.  This path here is the actual spec to be verified.
    		command.add(String.format("$(wslpath %s)", module.getLocation().toOSString().replace("\\", "\\\\")));
        } else {
            // why just the last segment?
            command.add(module.getLocation().toOSString());
        }
     
        // for debugging
        // for (int i=0; i<command.size(); i++) {
        //     System.out.println(command.get(i)) ;
        // }
        
        return (String[]) command.toArray(new String[command.size()]);
    }


    /**
     * Get the begin line of the region to pass to the prover.
     * 
     * The begin line is the begin line of the location of the level node.
     */
    private static int getBeginLine(LevelNode nodeToProve)
    {
        return nodeToProve.getLocation().beginLine();
    }

    /**
     * Get the end line of the region to pass to the prover.
     * 
     * If the level node has a proof, the end line is the end line of the proof. If the
     * level node does not have a proof, the end line is the end line of the level node.
     */
    private static int getEndLine(LevelNode nodeToProve)
    {
        // only TheoremNodes can have proofs
        if (nodeToProve instanceof TheoremNode && ((TheoremNode) nodeToProve).getProof() != null)
        {
            return ((TheoremNode) nodeToProve).getProof().getLocation().endLine();
        } else
        {
            return nodeToProve.getLocation().endLine();
        }
    }

    /**
     * If true, the prover will be launched for
     * status checking only, not proving.
     */
    public boolean isStatusCheck()
    {
        return checkStatus;
    }

    /**
     * Gets the step or module node on which the
     * prover was launched.
     * @return the levelNode
     */
    public LevelNode getLevelNode()
    {
        return nodeToProve;
    }

    /**
     * Returns the map from {@link Integer} begin line numbers of steps to
     * the last {@link StepStatusMessage} reported by the prover
     * for that step.
     */
    public Map<Integer, StepStatusMessage> getStepMessageMap()
    {
        return stepMessageMap;
    }

    /**
     * Returns a map from {@link Integer}s to {@link StepTuple}s.
     * The integer keys give the begin line of the step
     * tuple. This is the begin line reported by sany
     * for that step at the time that this job was run.
     * This is only for step tuples that represent leaf
     * steps.
     */
    public Map<Integer, StepTuple> getLeafStepMap()
    {
        return leafStepMap;
    }

    /**
     * Returns the {@link Collection} of {@link StepTuple}s
     * corresponding to leaf steps considered in this launch of
     * the prover. The iterator for this collection will return
     * the steps in ascending order of their start line. If multiple
     * steps are on the same line, there is no guarantee about the
     * order of steps on the same line. If this is the case, then other
     * stuff will probably break anyway, so don't worry about it.
     * @return
     */
    public Collection<StepTuple> getLeafSteps()
    {
        return leafStepMap.values();
    }

    /**
     * Returns the map from {@link Integer} ids of obligations
     * to {@link ObligationStatus}
     */
    public Map<Integer, ObligationStatus> getObsMap()
    {
        return obsMap;
    }

    /**
     * Returns a {@link Collection} of {@link ObligationStatus}s generated
     * by this launch of the prover.
     * 
     * @return
     */
    public Collection<ObligationStatus> getObs()
    {
        return obsMap.values();
    }

    /**
     * Returns the {@link ColorPredicate}s that were
     * in the user's preferences at the time of the running
     * of this job.
     * 
     * @return
     */
    public ColorPredicate[] getColorPredicates()
    {
        return colorPredicates;
    }

    /**
     * This method sets the values for the field nodeToProve
     * to be the step at the offset, where step is either a proof
     * step or a top level USE node. A step is at the offset if the method
     * {@link ResourceHelper#getPfStepOrUseHideFromMod(ParseResult, String, ITextSelection, IDocument)}
     * returns that node for the text selection representing the offset.
     * 
     * If there is not a step at the offset, this method will set nodeToProve
     * to be the {@link ModuleNode} pointing to the entire module.
     */
    private void initializeFields()
    {
        /*
         * This method takes the following steps:
         * 
         * 1.) Try to obtain a valid parse result for the module passed in to the constructor.
         *     A valid parse result is one that was created since the module was last
         *     written. If there is no valid parse result available, then parse the module. This creates
         *     a valid parse result.
         * 2.) Check if there are errors in the valid parse result obtained in step 3. If
         *     there are errors, return on this method. There is no need to show a message
         *     to the user in this case because the parse errors view will pop open anyway.
         * 3.) Get the LevelNode representing a step or top level use/hide containing the offset,
         *     if the offset is at such a node. Set nodeToProve to this node. The offset is passed
         *     in to the constructor.
         * 4.) If nodeToProve is still null or it is an instance of DefStepNode or InstanceNode,
         * set nodeToProve to be the ModuleNode for the module. InstanceNodes and DefStepNodes do
         * not generate obligations.
         * 
         * Note that at step 4 ,there are some other possibilities:
         *     -If the caret is not at any proof step, check the whole module.
         *     -If the caret is at a step without a proof, check the whole module.
         *     -If the caret is at a step without a proof, show a message to the user.
         *     -If the caret is at a step without a proof, disable this handler.
         *     -If the caret is not at any proof step, disable this handler.
         *     -If the caret is not at a step with a proof, ask the user if he wants
         *      to check the entire module.
         */

        /**********************************************************
         * Step 1                                                 *
         **********************************************************/

        ParseResult parseResult = ResourceHelper.getValidParseResult(module);

        if (parseResult == null)
        {
            /*
             * Its necessary to call this parsing within the job's run method.
             * Its a bad idea to have two calls to SANY executing at the same time,
             * and its possible for a launch of the prover to trigger background
             * parsing. For example, the user might have dirty editors open
             * when launching the prover. He will be prompted to save them. This
             * could trigger background parsing. The run method will not be
             * executed while the background parsing completes. This ensures
             * that the following parsing will not occur while the background parsing
             * executes.
             */
            parseResult = new ModuleParserLauncher().parseModule(module, new NullProgressMonitor());
        }

        /**********************************************************
         * Step 2                                                 *
         **********************************************************/
        if (parseResult.getStatus() != IParseConstants.PARSED)
        {
            return;
        }

        /**********************************************************
         * Step 3                                                 *
         **********************************************************/
        String moduleName = ResourceHelper.getModuleName(module);
        /*
         * An offset of -1 indicates that the PM should be launched
         * on the entire module. Leave nodeToProve null in this case
         * and Step 4 will set nodeToProve to the ModuleNode.
         */
        if (offset != -1)
        {
            nodeToProve = ResourceHelper.getPfStepOrUseHideFromMod(parseResult, moduleName,
                    new TextSelection(offset, 0), ResourceHelper.getDocFromFile(module));
        }

        /**********************************************************
         * Step 4                                                 *
         **********************************************************/
        /*
         * The "|| nodeToProve instanceof DefStepNode" disjunct caused the entire module
         * to be proved if the user selected a DefStepNode.  This seemed like obviously the
         * wrong thing to do.  So, LL commented it out on 4 Feb 2014.  This causes the Toolbox
         * to call the prover on just that definition step, which causes the prover to do 
         * nothing.  The case of an InstanceNode was also commented out for the same reason,
         * in case TLAPS ever handles an INSTANCE step.
         * 
         * An alternate fix would  be to have the Toolbox call the prover on the smallest 
         * containing proof, but we decided not to do that.  If we change our minds, the
         * fix is indicated in a comment on line 1152 of ResourceHelper.
         */

        if (nodeToProve == null /* || nodeToProve instanceof InstanceNode  || nodeToProve instanceof DefStepNode */ )
        {
            nodeToProve = parseResult.getSpecObj().getExternalModuleTable().getModuleNode(
                    UniqueString.uniqueStringOf(moduleName));
            return;
        }

    }

    /**
     * This method sets up the mechanism for listening to the error and output streams
     * of the prover. It also sets the value of the field proverProcess.
     * 
     * @param process
     * @param monitor
     */
    private void setUpStreamListening(Process process, IProgressMonitor monitor)
    {
        /*
         * This code proceeds as follows. First, we wrap the java.lang.Process in an IProcess by calling
         * DebugPlugin.newProcess(). An IProcess is an eclipse object with some
         * convenience methods. Then we create a TLAPMBroadcastStreamListener and add it as
         * a listener to the output and error streams of the IProcess.
         * 
         * The code is wrapped in two synchronized blocks to avoid a race condition on the
         * prover's output. The race condition can occur as follows. Calling DebugPlugin.newProcess()
         * creates instances of IStreamMonitor to monitor the output and error streams
         * of the prover. These monitors immediately start monitoring the streams and passing the
         * text from the streams to registered listeners. This means that they can potentially read
         * text from the prover's streams before the TLAPMBroadcastStreamListener is added as a listener.
         * This text would be lost. To solve this, this thread locks access to the prover's output and error
         * streams until after the TLAPMBroadcastStreamListener has been added as a listener.
         */
        if (process != null)
        {
            synchronized (process.getInputStream())
            {
                synchronized (process.getErrorStream())
                {
                    /* 
                     * Calling DebugPlugin.newProcess()
                     * wraps the java.lang.Process in an IProcess with some
                     * convenience methods.
                     */
                    proverProcess = DebugPlugin.newProcess(launch, process, getName());
                    /*
                     * Setup the broadcasting of the prover output stream.
                     * We pass in the progress monitor to allow listeners
                     * to report progress.
                     */
                    listener = new TLAPMBroadcastStreamListener(module, this, monitor);

                    /*
                     * Send a string to the listener indicating
                     * that a new prover job is starting. This makes
                     * it easier to read the console.
                     */
                    listener.streamAppended("---------------- New Prover Launch --------------\n", null);

                    IStreamMonitor esMonitor = proverProcess.getStreamsProxy().getErrorStreamMonitor();
                    IStreamMonitor osMonitor = proverProcess.getStreamsProxy().getOutputStreamMonitor();

                    esMonitor.addListener(listener);
                    osMonitor.addListener(listener);

                    /*
                     * The output from the prover can be long, so buffering it can lead to an
                     * OutOfMemoryError. The following code turns off buffering.
                     */
                    if (esMonitor instanceof IFlushableStreamMonitor && osMonitor instanceof IFlushableStreamMonitor)
                    {
                        ((IFlushableStreamMonitor) esMonitor).setBuffered(false);
                        ((IFlushableStreamMonitor) osMonitor).setBuffered(false);
                    }
                }
            }
        }
    }

    /**
     * Returns the name of the task that this prover job performs. This
     * should be used to set the name of the task in the call of
     * {@link IProgressMonitor#beginTask(String, int)} for the progress monitor
     * passed to this job's run method.
     * 
     * This method is public so that other classes can call begin task on the progress
     * monitor. We cannot call begin task until we know the total number of obligations.
     * The {@link TagBasedTLAPMOutputIncrementalParser} gets this information when it
     * is sent by the tlapm, so it makes sense for that class to call begin task.
     * 
     * @return
     */
    public String getProverJobTaskName()
    {
        return (checkStatus ? "Status check" : "Prover")
                + " launched on "
                + (nodeToProve instanceof ModuleNode ? "entire" : "")
                + " module "
                + module.getName()
                + (nodeToProve instanceof ModuleNode ? "" : " from line " + getBeginLine(nodeToProve) + " to line "
                        + getEndLine(nodeToProve));
    }

    /**
     * Sends a signal to the tlapm indicating that the obligation
     * with the given id should be stopped.
     * 
     * @param id
     */
    public void stopObligation(int id)
    {
        if (proverProcess != null && !proverProcess.isTerminated())
        {
            try
            {
                proverProcess.getStreamsProxy().write("stop " + id + "\n");
            } catch (IOException e)
            {
                ProverUIActivator.getDefault().logError("Error sending signal to tlapm to stop obligation " + id, e);
            }
        }
    }

    /**
     * Returns the most prover job that led to the most
     * recent launch of the prover.
     */
    public static ProverJob getLastJob()
    {
        return lastJob;
    }

    /**
     * Returns a list of all obligation message with
     * status {@link ProverHelper#TO_BE_PROVED} that
     * have been sent so far.
     * @return the obMessageList
     */
    public List<ObligationStatusMessage> getObMessageList()
    {
        return obMessageList;
    }

	public boolean addObMessageList(ObligationStatusMessage message) {
		return obMessageList.add(message);
	}

    /**
     * Sets the flag indicating that should be true
     * iff the only obligation status messages to be
     * sent to the toolbox so far for
     * this launch of the prover have
     * status {@link ProverHelper#TO_BE_PROVED}.
     * @param toBeProvedOnly the toBeProvedOnly to set
     */
    public void setToBeProvedOnly(boolean toBeProvedOnly)
    {
        this.toBeProvedOnly = toBeProvedOnly;
    }

    /**
     * Returns a flag that is true iff the only
     * obligation status messages to be
     * sent to the toolbox so far for
     * this launch of the prover have
     * status {@link ProverHelper#TO_BE_PROVED}.
     * 
     * @return the toBeProvedOnly
     */
    public boolean isToBeProvedOnly()
    {
        return toBeProvedOnly;
    }

    /**
     * Returns the {@link IFile} pointing to the module to be checked.
     */
    public IFile getModule()
    {
        return module;
    }

    /**
     * Returns the command used to launch the prover
     * as a single string.
     * 
     * Returns null if {@link #command} is null.
     *  
     * @return
     */
    public String getLaunchProverCommand()
    {
        if (command == null)
        {
            return "";
        }

        StringBuilder buffer = new StringBuilder();
        for (int i = 0; i < command.length; i++)
        {
            buffer.append(command[i]).append(" ");
        }
        return buffer.toString();
    }

    /**
     * Returns the String[] representing the full command
     * used to launch the prover.
     * 
     * @return
     */
    public String[] getProverCommandArray()
    {
        return command;
    }

    public long getCurRelTime()
    {
        return System.currentTimeMillis() - startTime;
    }

	public boolean getNoToBeProved() {
		return noToBeProved;
	}

	public void setNoToBeProved(boolean b) {
		noToBeProved = b;
	}
}
