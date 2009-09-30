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

public abstract class ChangedSpecModulesGatheringDeltaVisitor implements IResourceDeltaVisitor
{

    private IContainer rootFileParent;
    private Vector modules = new Vector();
    private IResource model = null;

    public ChangedSpecModulesGatheringDeltaVisitor()
    {
        rootFileParent = Activator.getSpecManager().getSpecLoaded().getRootFile().getParent();
    }

    /**
     * @see org.eclipse.core.resources.IResourceDeltaVisitor#visit(org.eclipse.core.resources.IResourceDelta)
     */
    /* (non-Javadoc)
     * @see org.eclipse.core.resources.IResourceDeltaVisitor#visit(org.eclipse.core.resources.IResourceDelta)
     */
    public boolean visit(IResourceDelta delta) throws CoreException
    {
        final IResource resource = delta.getResource();
//        System.out.println("resource = " + resource.getFullPath().toString());
        if (IResource.FILE == resource.getType())
        {

            // add the file only if it's parent is the root file's parent.
            if (ResourceHelper.isModule(resource) && (resource.getParent().equals(rootFileParent)))
            {
// System.out.println("module resource added");
                modules.add(resource);
            } else
            {
//                System.out.println("first conjunct = " + (delta.getFlags() == IResourceDelta.MARKERS));
//                System.out.println("delta.getFlags() = " + delta.getFlags());
//                System.out.println("blah blah = " + ((delta.getFlags() & IResourceDelta.MARKERS) == IResourceDelta.MARKERS));
//                System.out.println("IResourceDelta.MARKERS = " + IResourceDelta.MARKERS);
//                System.out.println("model  = " + getModel().getFullPath().toString());
                // The first conjunct of the following test should probably  be ((delta.getFlags() & IResourceDelta.MARKERS) == IResourceDelta.MARKERS),
                // but it doesn't hurt to remove that test and risk unnecessarily removing and resetting markers.
                if(/* delta.getFlags() == IResourceDelta.MARKERS && */ (getModel() != null) && getModel().equals(resource)) 
                {
//                    System.out.println("model set to resource");

                    model = resource;
                    return false;
                }
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
}
