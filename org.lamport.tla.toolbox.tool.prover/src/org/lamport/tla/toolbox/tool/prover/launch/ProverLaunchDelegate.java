package org.lamport.tla.toolbox.tool.prover.launch;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.model.LaunchConfigurationDelegate;
import org.lamport.tla.toolbox.spec.parser.ModuleParserLauncher;
import org.lamport.tla.toolbox.spec.parser.ParseResult;
import org.lamport.tla.toolbox.tool.prover.job.ProverJob;
import org.lamport.tla.toolbox.util.ResourceHelper;

public class ProverLaunchDelegate extends LaunchConfigurationDelegate implements IProverConfigurationConstants
{

    public static final String CONFIG_TYPE = "org.lamport.tla.toolbox.tool.prover.proverLaunch";
    public static final String MODE_CHECK_STEP = "checkStep";

    IPath modulePath;
    int lineNumber;

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

        lineNumber = configuration.getAttribute(IProverConfigurationConstants.LINE_NUMBER, -1);

        // TODO check that line number is valid
        // use document provider

        /*
         * Parse module.
         * 
         * If parsing is unsuccessful, return false.
         */
        ParseResult result = (new ModuleParserLauncher()).parseModule(ResourceHelper.getResourceByName(modulePath
                .lastSegment()), new NullProgressMonitor());
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

        ProverJob job = new ProverJob("Prover Job", modulePath, null /*new Path("C:/cygwin/usr/local/bin/tlapm")*/,
                null /*new Path(
                     "C:/cygwin/bin")*/, launch);
        job.schedule();

    }

}
