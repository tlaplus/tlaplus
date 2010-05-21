package org.lamport.tla.toolbox.tool.tlc.util;

import java.util.List;
import java.util.Vector;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.util.ResourceHelper;

/**
 * Visitor to find out what modules in the root file's directory have changed
 */

public abstract class ChangedSpecModulesGatheringDeltaVisitor implements IResourceDeltaVisitor
{

    private IContainer rootFileParent;
    private Vector modules = new Vector();
    private IResource model = null;
    private boolean checkpointsChanged = false;
    private IFolder modelDir;

    public ChangedSpecModulesGatheringDeltaVisitor(ILaunchConfiguration config)
    {
        modelDir = ModelHelper.getModelTargetDirectory(config);
        rootFileParent = Activator.getSpecManager().getSpecLoaded().getRootFile().getParent();
    }

    /**
     * If the delta points to a module in the currently loaded spec, it adds that resource to
     * the list modules.
     * If the delta points to the file of the configuration, then it sets model equal to 
     * that file.
     * If the delta points to a resouce that is the model directory for the configuration in
     * the constructor, then sets checkpointsChanged to true.
     * @see org.eclipse.core.resources.IResourceDeltaVisitor#visit(org.eclipse.core.resources.IResourceDelta)
     */
    /* (non-Javadoc)
     * @see org.eclipse.core.resources.IResourceDeltaVisitor#visit(org.eclipse.core.resources.IResourceDelta)
     */
    public boolean visit(IResourceDelta delta) throws CoreException
    {
        final IResource resource = delta.getResource();
        // System.out.println("resource = " + resource.getFullPath().toString());
        if (IResource.FILE == resource.getType())
        {

            // add the file only if it's parent is the root file's parent.
            if (ResourceHelper.isModule(resource) && (resource.getParent().equals(rootFileParent)))
            {
                // System.out.println("module resource added");
                modules.add(resource);
            } else

            // The first conjunct of the following test should probably be ((delta.getFlags() & IResourceDelta.MARKERS)
            // == IResourceDelta.MARKERS),
            // but it doesn't hurt to remove that test and risk unnecessarily removing and resetting markers.
            if (/* delta.getFlags() == IResourceDelta.MARKERS && */(getModel() != null) && getModel().equals(resource))
            {
                // System.out.println("model set to resource");

                model = resource;
                return false;
            }
        } else if (IResource.FOLDER == resource.getType())
        {
            if ((modelDir != null) && (modelDir.exists()) && (modelDir.equals(resource)))
            {
                checkpointsChanged = true;
                return false;
            }
        }
        // TODO: we don't really want the visitor to visit the whole tree, do we?
        return true;
    }

    /**
     * Retrieves found modules, or an empty list, if nothing found
     * @return a list with found modules
     */
    public List getModules()
    {
        return modules;
    }

    /**
     * This method must be provided, in order to supply the model of interest 
     * @return the resource storing the model
     */
    public abstract IResource getModel();

    /**
     * Returns if the resource delta contained a marker modifications of the model file
     */
    public boolean isModelChanged()
    {
        return this.model != null;
    }

    /**
     * Returns true if the visitor has found a change to the directory
     * containing the checkpoints, so a checkpoint might have changed.
     * @return
     */
    public boolean getCheckpointChanged()
    {

        return checkpointsChanged;
    }
}
