package org.lamport.tla.toolbox.util;

import java.util.List;
import java.util.Vector;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.runtime.CoreException;

/**
 * Visitor to find out what files changed
 */

public class ChangedModulesGatheringDeltaVisitor implements IResourceDeltaVisitor
{
    Vector modules = new Vector();

    public ChangedModulesGatheringDeltaVisitor()
    {
    }

    /**
     * @see org.eclipse.core.resources.IResourceDeltaVisitor#visit(org.eclipse.core.resources.IResourceDelta)
     */
    public boolean visit(IResourceDelta delta) throws CoreException
    {
        final IResource resource = delta.getResource();
        if (IResource.FILE == resource.getType())
        {
            // a file found
            if (resource.exists() && ResourceHelper.isModule(resource))
            {
                modules.add(resource);
            }
        }
        // we want the visitor to visit the whole tree
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
