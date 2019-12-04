package org.lamport.tla.toolbox.tool.tlc.job;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Status;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.debug.core.model.IProcess;
import org.eclipse.debug.core.model.IStreamsProxy;
import org.eclipse.jdt.launching.IVMInstall;
import org.eclipse.jdt.launching.IVMRunner;
import org.eclipse.jdt.launching.VMRunnerConfiguration;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.IOConsole;
import org.eclipse.ui.console.IOConsoleInputStream;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.launch.TraceExplorerDelegate;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink;
import org.lamport.tla.toolbox.tool.tlc.output.internal.BroadcastStreamListener;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tlc2.TLC;
import tlc2.output.EC;
import tlc2.tool.fp.FPSetFactory;
import tlc2.tool.fp.NoopFPSet;
import tlc2.tool.fp.OffHeapDiskFPSet;
import util.TLCRuntime;

/**
 * A job to launch TLC as a separate process
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCProcessJob extends TLCJob
{
    public static final int HEAP_SIZE_DEFAULT = 25;
	protected IProcess process = null;
    private BroadcastStreamListener listener = null;

    /**
     * The tlc start time in milliseconds as given
     * by {@link System#currentTimeMillis()}.
     */
    private long tlcStartTime;
    /**
     * The tlc end time in milliseconds as given
     * by {@link System#currentTimeMillis()}.
     */
    private long tlcEndTime;

    /**
     * Constructs a process job
     * @param workers 
     * @param name
     */
    public TLCProcessJob(String specName, String modelName, ILaunch launch, int workers)
    {
        super(specName, modelName, launch, workers);
    }

    /* (non-Javadoc)
     * @see org.eclipse.core.runtime.jobs.Job#run(org.eclipse.core.runtime.IProgressMonitor)
     */
    protected IStatus run(IProgressMonitor monitor)
    {
        try
        {

            // start the monitor ( we don't know the )
            monitor.beginTask("Running TLC model checker", IProgressMonitor.UNKNOWN);

            // step 1
            monitor.worked(STEP);
            monitor.subTask("Preparing the TLC Launch");

            // classpath
            final String runtimeClasspath = ToolboxHandle.getTLAToolsClasspath().toOSString();
			// Add 3rd party libraries to classpath. Star acts as wildcard
			// picking up all .jar files (added by MAK on 07/31/2012)
			final String libClasspath = runtimeClasspath + File.separator + "lib" + File.separator + "*";
			final String libMailClasspath = runtimeClasspath + File.separator + "lib" + File.separator + "javax.mail"
					+ File.separator + "*";
			// classpath during toolbox development within Eclipse (will simply not
			// exist in packaged toolbox)
			final String devClasspath = runtimeClasspath + File.separator + "class";
			
			// Add TLA+ library path entries to the class path in case any one of them
			// includes module overwrites.  It is the last element on the classpath.
			final Spec spec = Activator.getSpecManager().getSpecByName(specName);
			final String libraryPathClassPath = spec.getTLALibraryPathAsClassPath();
			
			final String[] classPath = new String[] { runtimeClasspath, libClasspath, libMailClasspath, devClasspath, libraryPathClassPath };

            // arguments
            String[] arguments = constructProgramArguments();

            final List<String> vmArgs = new ArrayList<String>();

            // get max heap size as fraction from model editor
            int maxHeapSize = launch.getLaunchConfiguration().getAttribute(LAUNCH_MAX_HEAP_SIZE, HEAP_SIZE_DEFAULT);
            if (maxHeapSize < 1 || maxHeapSize > 99) {
				TLCActivator.logInfo(String.format(
						"Defaulting fraction of physical memory to %s because %s is out of range (0,100). Value can be adjusted on the model editor's \"Advanced TLC option\" tab.",
						HEAP_SIZE_DEFAULT, maxHeapSize));
            	// Dealing with a legacy model (absolute memory values) or somehow bogus input.
            	maxHeapSize = HEAP_SIZE_DEFAULT;
            }
			final TLCRuntime instance = TLCRuntime.getInstance();
			long absolutePhysicalSystemMemory = instance.getAbsolutePhysicalSystemMemory(maxHeapSize / 100d);

			// Get class name of the user selected FPSet. If it is unset, try and load the
			// OffHeapDiskFPSet (which might not be supported). In unsupported, revert to
			// TLC's default set.
			// If the user happened to select OffHeapDiskFPSet, the -XX:MaxDirectMemorySize
			// is set by getVMArguments.
			String clazz = getOptimalFPsetImpl();
			if (!hasSpec(launch.getLaunchConfiguration())) {
				// If a spec has no behaviors, TLC won't need a fingerprint set. Thus, use the
				// NoopFPSet whose initialization cost is next to nothing. Real fpsets on the
				// other hand - such as OffHeapDiskFPSet - do heavy weight initialization at startup.
				clazz = NoopFPSet.class.getName();
			}
			if (clazz == null || clazz.equals(OffHeapDiskFPSet.class.getName())) {
				if (OffHeapDiskFPSet.isSupported()) {
					// ...good, can use lock-free/scalabe fpset, but need to divide assigned memory
					// into JVM heap and non-heap/off-heap memory. Let's assign 2/3 to the off-heap
					// FPSet.
					final long offheapMemory = (long) (absolutePhysicalSystemMemory * 0.6666d);
					vmArgs.add(FPSetFactory.getVMArguments(OffHeapDiskFPSet.class.getName(), offheapMemory));

					// Rest goes to the heap (state queue/...).
					vmArgs.add(FPSetFactory.getVMArguments(FPSetFactory.getImplementationDefault(),
							absolutePhysicalSystemMemory - offheapMemory));
					
					vmArgs.add("-D" + FPSetFactory.IMPL_PROPERTY + "=" + OffHeapDiskFPSet.class.getName());
				} else {
					// Off-heap fpset couldn't be loaded. Use default fpset and assign all memory to
					// heap memory.
					vmArgs.add(FPSetFactory.getVMArguments(FPSetFactory.getImplementationDefault(),
							absolutePhysicalSystemMemory));
					vmArgs.add("-D" + FPSetFactory.IMPL_PROPERTY + "=" + FPSetFactory.getImplementationDefault());
				}
			} else {
				vmArgs.add(FPSetFactory.getVMArguments(clazz, absolutePhysicalSystemMemory));
				vmArgs.add("-D" + FPSetFactory.IMPL_PROPERTY + "=" + clazz);
			}
			
			// specify Java8+ acceptable GC
			vmArgs.add("-XX:+UseParallelGC");
			
            // add remaining VM args
            vmArgs.addAll(getAdditionalVMArgs());


            // assemble the config
            VMRunnerConfiguration tlcConfig = new VMRunnerConfiguration(getMainClass().getName(), classPath);
            // tlcConfig.setProgramArguments(new String[] { ResourceHelper.getModuleName(rootModule) });
            tlcConfig.setProgramArguments(arguments);
            tlcConfig.setVMArguments((String[]) vmArgs.toArray(new String[vmArgs.size()]));
            tlcConfig.setWorkingDirectory(ResourceHelper.getParentDirName(rootModule));
            // Following added for testing by LL on 6 Jul 2012
            final IVMInstall vmInstall = getVMInstall();
            
            
			final IVMRunner runner = vmInstall.getVMRunner(ILaunchManager.RUN_MODE);

            launch.setAttribute(DebugPlugin.ATTR_CAPTURE_OUTPUT, "true");

            // step 2
            monitor.worked(STEP);
            monitor.subTask("Launching TLC");

            try
            {
                // step 3
                runner.run(tlcConfig, launch, new NullProgressMonitor());
                tlcStartTime = System.currentTimeMillis();
            } catch (CoreException e)
            {
            	// Include command-line for users to figure out what failed.
				return new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
						String.format("Error launching TLC with command-line (CWD: %s): %s%sbin%sjava -cp %s %s %s %s",
								tlcConfig.getWorkingDirectory(), vmInstall.getInstallLocation(), File.separator,
								File.separator, String.join(File.pathSeparator, tlcConfig.getClassPath()),
								String.join(" ", tlcConfig.getVMArguments()),
								String.join(" ", tlcConfig.getClassToLaunch()), String.join(" ", arguments)),
						e);
            }

            // find the running process
            this.process = findProcessForLaunch(launch);

            // step 4
            monitor.worked(STEP);
            monitor.subTask("Connecting to running instance");

            // process found
            if (this.process != null)
            {
				// Log command-line that can (almost) copied&pasted verbatim to a shell to
				// run TLC directly.
				// (Working directory needed because TLC does not find MC.tla even if -metadir
				// is set).
            	final String cmd = this.process.getAttribute(IProcess.ATTR_CMDLINE);
            	final String cwd = this.process.getAttribute(DebugPlugin.ATTR_WORKING_DIRECTORY);
            	TLCActivator.logInfo(String.format("TLC COMMAND-LINE (CWD: %s): %s", cwd, cmd));
            	
                // step 5
                monitor.worked(STEP);
                monitor.subTask("Model checking...");

                // register the broadcasting listener

                final Model model = launch.getLaunchConfiguration().getAdapter(Model.class);

                /*
                 * If TLC is being run for model checking then the stream kind passed to
                 * BroadcastStreamListener (second argument) is IProcessOutputSink.TYPE_OUT.
                 * If TLC is being run for trace exploration, then it is
                 * IProcessOutputSink.TYPE_TRACE_EXPLORE.
                 */

                int kind = IProcessOutputSink.TYPE_OUT;

                if (launch.getLaunchMode().equals(TraceExplorerDelegate.MODE_TRACE_EXPLORE))
                {
                    kind = IProcessOutputSink.TYPE_TRACE_EXPLORE;
                }

                listener = new BroadcastStreamListener(model, kind);

                // stdout, stderr, stdin of the forked TLC process.
                final IStreamsProxy streamsProxy = process.getStreamsProxy();
				streamsProxy.getOutputStreamMonitor().addListener(listener);
				streamsProxy.getErrorStreamMonitor().addListener(listener);
				
				// This is a reader wrapping the input stream of the Toolbox console. In other
				// words, if a user types a string into the Toolbox console, we can read the
				// string from the reader. Iff consoleStdIn is not null (there is a Toolbox
				// console), the loop below reads from consoleStdIn and writes (forwards) the
				// string to stdin of the TLC process.  Because the while loop sleeps for a
				// second, the response time isn't perfect but is good enough for now.
				final BufferedReader consoleReader = getConsoleReader();
				
                // loop until the process is terminated
				while (checkAndSleep()) {
					// check the cancellation status
					if (monitor.isCanceled()) {
						// cancel the TLC
						try {
							process.terminate();
						} catch (DebugException e) {
							// react on the status code
							switch (e.getStatus().getCode()) {
							case DebugException.TARGET_REQUEST_FAILED:
							case DebugException.NOT_SUPPORTED:
							default:
								// MAK 11/2012: Remove e.getStatus().getCode()
								// and e (throwable) once Chris' problem
								// cancellation has been diagnosed
								return new Status(
										IStatus.ERROR,
										TLCActivator.PLUGIN_ID,
										e.getStatus().getCode(),
										"Error terminating the running TLC instance. This is a bug. Make sure to exit the toolbox.",
										e);
							}
						}

						// Wait for the process to terminate. Otherwise, it
						// opens the door to a race condition in
						// org.lamport.tla.toolbox.tool.tlc.model.Model such
						// that isRunning returns true querying the Launch (which
						// is directly connected to the Process instance), even
						// after the outer TLCProcessJob's JobListener
						// ...launch.TLCModelLaunchDelegate.TLCJobChangeListener
						// has setRunning(false). 
						int i = 0;
						while (!process.isTerminated() || i++ >= 10) {
							try {
								Thread.sleep(100L);
							} catch (InterruptedException e) {
								e.printStackTrace();
								return new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
										"Error waiting for process termination.", e);
							}
						}
						if (!process.isTerminated()) {
							TLCActivator.logInfo(
									"TLC process failed to terminate within expected time window. Expect Toolbox to show an incorrect model state.");
						}
						
						// abnormal termination
						tlcEndTime = System.currentTimeMillis();
						return Status.CANCEL_STATUS;
					}
					
					
					try {
						if (consoleReader != null && consoleReader.ready()) {
							streamsProxy.write(consoleReader.readLine() + "\n");
						}
					} catch (IOException e) {
						throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
								"Error reading from Toolbox console or writing to stdin of TLC process", e));
					}
				}

                // step 6
                monitor.worked(STEP);
                monitor.subTask("Model checking finished.");

                // handle finish
                doFinish();

                tlcEndTime = System.currentTimeMillis();

                return Status.OK_STATUS;

            } else
            {
                // process not found
                return new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                        "Error launching TLC, the launched process cound not be found");
            }

        } catch (CoreException e)
        {
            return new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID, "Error reading model parameters", e);
        } finally
        {
            // send the notification about completion
            if (listener != null)
            {
                listener.streamClosed();
                // remove this listener from the stream to avoid memory leak
                if (process != null && process.getStreamsProxy() != null)
                {
                    if (process.getStreamsProxy().getOutputStreamMonitor() != null)
                    {
                        process.getStreamsProxy().getOutputStreamMonitor().removeListener(listener);
                    }
                    if (process.getStreamsProxy().getErrorStreamMonitor() != null)
                    {
                        process.getStreamsProxy().getErrorStreamMonitor().removeListener(listener);
                    }
                }
            }
            // make sure to complete the monitor
            monitor.done();
        }
    }

	private static BufferedReader getConsoleReader() {
		final IConsoleManager consoleManager = ConsolePlugin.getDefault().getConsoleManager();
		final List<IConsole> tlcConsole = Arrays.asList(consoleManager.getConsoles()).stream()
				.filter(c -> "TLC-Console".equals(c.getName())).collect(Collectors.toList());
		if (!tlcConsole.isEmpty()) {
			final IConsole iConsole = tlcConsole.get(0);
			if (iConsole instanceof IOConsole) {
				IOConsoleInputStream inputStream = ((IOConsole) iConsole).getInputStream();
				return new BufferedReader(new InputStreamReader(inputStream));
			}
		}
		return null;
	}

	protected String getOptimalFPsetImpl() throws CoreException {
		return launch.getLaunchConfiguration().getAttribute(LAUNCH_FPSET_IMPL, (String) null);
	}

	/**
	 * @return A list of additional vm arguments
	 */
	protected List<String> getAdditionalVMArgs() throws CoreException {
		final List<String> result = new ArrayList<String>(0);
		
		// Library Path
		final Spec spec = Activator.getSpecManager().getSpecByName(specName);
		final String tlaLibraryPathAsVMArg = spec.getTLALibraryPathAsVMArg();
		if (!"".equals(tlaLibraryPathAsVMArg)) {
			result.add(tlaLibraryPathAsVMArg);
		}

		// JVM arguments/system properties
		final ILaunchConfiguration launchConfig = launch.getLaunchConfiguration();
		final String vmArgs = launchConfig.getAttribute(LAUNCH_JVM_ARGS, (String) null);
		if(vmArgs != null) {
			result.addAll(sanitizeString(vmArgs));
		}

		return result;
	}
	
	/**
	 * @param vmArgs may look like " -Djava.rmi.foo=bar  -Djava.tralla=avalue  "
	 * @return a {@link List} with ["-Djava.rmi.foo=bar", "-Djava.tralla=avlue"]
	 */
	private List<String> sanitizeString(final String vmArgs) {
		final String[] strings = vmArgs.split(" ");
		final List<String> results = new ArrayList<String>(strings.length);
		for (int i = 0; i < strings.length; i++) {
			final String string = strings[i];
			if(!"".equals(string) && !" ".equals(string)) {
				results.add(string.trim());
			}
			// additional sanity checks could go here, but the nested process will report errors anyway
		}
		return results;
	}

	@SuppressWarnings("rawtypes")
	protected Class getMainClass() {
		return TLC.class;
	}

    protected boolean checkCondition() {
        // return true if the TLC is still calculating
    	return !process.isTerminated();
    }
    
    /**
     * Retrieves a process to a given ILaunch
     * @param launch
     * @return
     */
    private static IProcess findProcessForLaunch(ILaunch launch)
    {
        // find the process
        IProcess[] processes = DebugPlugin.getDefault().getLaunchManager().getProcesses();
        for (int i = 0; i < processes.length; i++)
        {
            if (processes[i].getLaunch().equals(launch))
            {
                return processes[i];
            }
        }
        return null;
    }

    /**
     * Returns the tlc start time in milliseconds as given
     * by {@link System#currentTimeMillis()}.
     * @return
     */
    public long getTlcStartTime()
    {
        return tlcStartTime;
    }

    /**
     * Returns the tlc end time in milliseconds as given
     * by {@link System#currentTimeMillis()}.
     * @return
     */
    public long getTlcEndTime()
    {
        return tlcEndTime;
    }

	/**
	 * @return The processee's exit/return value or -1 if unknown.
	 */
    public int getExitValue() {
    	if (this.process != null) {
    		try {
    			return this.process.getExitValue();
    		} catch (DebugException shouldNotHappen) {
    			shouldNotHappen.printStackTrace();
    		}
    	}
    	return 255;
    }

	public boolean hasCrashed() {
		return EC.ExitStatus.exitStatusToCrash(getExitValue());
	}
}
