package org.lamport.tla.toolbox.tool.prover.launch;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.jobs.IJobChangeEvent;
import org.eclipse.core.runtime.jobs.IJobChangeListener;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.model.LaunchConfigurationDelegate;
import org.lamport.tla.toolbox.spec.parser.ModuleParserLauncher;
import org.lamport.tla.toolbox.spec.parser.ParseResult;
import org.lamport.tla.toolbox.tool.prover.ProverActivator;
import org.lamport.tla.toolbox.tool.prover.job.ProverJob;
import org.lamport.tla.toolbox.tool.prover.util.ProverHelper;
import org.lamport.tla.toolbox.util.ResourceHelper;

public class ProverLaunchDelegate extends LaunchConfigurationDelegate implements IProverConfigurationConstants
{

    public static final String CONFIG_TYPE = "org.lamport.tla.toolbox.tool.prover.proverLaunch";
    public static final String MODE_CHECK_STEP = "checkStep";

    IPath modulePath;
    /**
     * Begin line.
     */
    int bl;
    /**
     * Begin column.
     */
    int bc;
    /**
     * End line.
     */
    int el;
    /**
     * End column.
     */
    int ec;
    IResource module;

    public boolean finalLaunchCheck(ILaunchConfiguration configuration, String mode, IProgressMonitor monitor)
            throws CoreException
    {

        /*
         * Check if the module exists and if the line
         * number is a valid line number for that module.
         * 
         * The string stored in the configuration for
         * IProverConfigurationConstants.MODULE_PATH should be
         * stored using Path.toPortableString() and so can
         * be restored using Path.fromPortableString().
         */
        modulePath = Path.fromPortableString(configuration.getAttribute(IProverConfigurationConstants.MODULE_PATH, ""));

        if (!modulePath.toFile().exists())
        {
            // TODO print error message
            return false;
        }

        /*
         * Get the coordinates.
         * 
         * If begin line or end line are -1, the prover should not be launched.
         * This is a bug.
         */
        bl = configuration.getAttribute(IProverConfigurationConstants.BEGIN_LINE, -1);
        bc = configuration.getAttribute(IProverConfigurationConstants.BEGIN_COLUMN, -1);
        el = configuration.getAttribute(IProverConfigurationConstants.END_LINE, -1);
        ec = configuration.getAttribute(IProverConfigurationConstants.END_COLUMN, -1);

        if (bl == -1 || el == -1)
        {
            ProverActivator.logDebug("Begin line or end line is -1 for a launch of the prover on module " + modulePath
                    + ". This is a bug.");
            return false;
        }

        /*
         * Get the IResource pointing to the module.
         * 
         * If the following method returns null, then
         * no module exists by the name given by modulePath
         * in the currently open spec. In that case, this
         * method should return false. The launch should not
         * proceed.
         */
        module = ResourceHelper.getResourceByName(modulePath.lastSegment());

        if (module == null)
        {
            return false;
        }

        /*
         * Parse module.
         * 
         * If parsing is unsuccessful, return false.
         */
        ParseResult result = (new ModuleParserLauncher()).parseModule(module, new NullProgressMonitor());
        if (!result.getDetectedErrors().isEmpty())
        {
            // MessageDialog.openError(UIHelper.getShellProvider().getShell(), "Module not parsed.",
            // "The module must be parsed before launching the prover.");
            return false;
        }

        return true;
    }

    public void launch(ILaunchConfiguration configuration, String mode, ILaunch launch, IProgressMonitor monitor)
            throws CoreException
    {

        /*
         * Set a flag on the module indicating that the prover is running.
         * 
         * This flag is set to false by a job change listener when the job finishes.
         * 
         * It is currently only possible to run the prover on a module in the open spec.
         */
        ProverHelper.setProverRunning(module, true);

        /*
         * Launch the prover.
         * 
         * For now, we pass in null for the path to cygwin and to the tlapm executable. Eventually, there
         * may be a user preference for these paths, so these arguments may not be null in the future.
         */
        ProverJob job = new ProverJob("Prover Job", modulePath, null /*new Path("C:/cygwin/usr/local/bin/tlapm")*/,
                null /*new Path(
                     "C:/cygwin/bin")*/, launch);

        job.setLocation(bl, bc, el, ec);

        // set the job progress to appear in a dialog in the UI
        job.setUser(true);

        job.addJobChangeListener(new ProverJobChangeListener());

        job.schedule();

    }

    /**
     * A job change listener for the prover.
     * 
     * Currently, this only sets the flag
     * on the module to indicate that the prover
     * is no longer running on that module when
     * the prover finishes.
     * 
     * @author Daniel Ricketts
     *
     */
    class ProverJobChangeListener implements IJobChangeListener
    {

        public void aboutToRun(IJobChangeEvent event)
        {
            // TODO Auto-generated method stub

        }

        public void awake(IJobChangeEvent event)
        {
            // TODO Auto-generated method stub

        }

        public void done(IJobChangeEvent event)
        {
            try
            {
                ProverHelper.setProverRunning(module, false);
            } catch (CoreException e)
            {
                ProverActivator.logError("Error setting flag on module to indicate the prover is not running.", e);
            }
        }

        public void running(IJobChangeEvent event)
        {
            // TODO Auto-generated method stub

        }

        public void scheduled(IJobChangeEvent event)
        {
            // TODO Auto-generated method stub

        }

        public void sleeping(IJobChangeEvent event)
        {
            // TODO Auto-generated method stub

        }

    }

}
