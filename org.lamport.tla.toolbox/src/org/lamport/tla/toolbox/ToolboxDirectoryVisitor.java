
package org.lamport.tla.toolbox;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.runtime.CoreException;
import org.lamport.tla.toolbox.util.ResourceHelper;

/**
 * Visitor for finding changed .toolbox directories.
 * 
 * @author lamport
 *
 */
public class ToolboxDirectoryVisitor implements IResourceDeltaVisitor
{
    LinkedList iprojects = new LinkedList();
    
    /**
     * 
     */
//    public ToolboxDirectoryVisitor()
//    {
//        // TODO Auto-generated constructor stub
//    }

    /** 
     * The visit method gets a resource and returns true or false depending on
     * whether or not it wants to be called with the children of the resource.
     * In this case, we return true unless the resource is a project representing
     * a spec (and thus whose resource is stored as a File (in this case a directory)
     * with extension toolbox.
     * 
     * @see org.eclipse.core.resources.IResourceDeltaVisitor#visit(org.eclipse.core.resources.IResourceDelta)
     */
    public boolean visit(IResourceDelta delta) throws CoreException
    {
        IResource resource = delta.getResource(); 
        if ((resource instanceof IProject) ) {
            iprojects.add(resource);
            return false;
        }
        return true;
    }
    
    public List getDirectories() {
        return iprojects;
    }

}
