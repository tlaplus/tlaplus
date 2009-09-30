package org.lamport.tla.toolbox.util;

import java.util.List;
import java.util.Vector;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.runtime.CoreException;
import org.lamport.tla.toolbox.Activator;

/**
 * Visitor to find out what modules in the root file's directory have changed
 */

public class ChangedSpecModulesGatheringDeltaVisitor implements IResourceDeltaVisitor
{

    private IContainer rootFileParent;
    private Vector modules = new Vector();

    public ChangedSpecModulesGatheringDeltaVisitor()
    {
        rootFileParent = Activator.getSpecManager().getSpecLoaded().getRootFile().getParent();
    }

    /**
     * @see org.eclipse.core.resources.IResourceDeltaVisitor#visit(org.eclipse.core.resources.IResourceDelta)
     */
    public boolean visit(IResourceDelta delta) throws CoreException
    {
        final IResource resource = delta.getResource();
        if (IResource.FILE == resource.getType())
        {

            // add the file only if it's parent is the root file's parent.
            if (ResourceHelper.isModule(resource) && (resource.getParent().equals(rootFileParent)))
            {
                modules.add(resource);
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
}
