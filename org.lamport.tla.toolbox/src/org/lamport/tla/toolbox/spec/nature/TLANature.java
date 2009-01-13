package org.lamport.tla.toolbox.spec.nature;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectNature;
import org.eclipse.core.runtime.CoreException;

public class TLANature implements IProjectNature
{
    
    private IProject project;
    public static final String ID = "toolbox.natures.TLANature";


    public void configure() throws CoreException
    {
        System.out.print("Nature added");
    }

    public void deconfigure() throws CoreException
    {
        System.out.print("Nature removed");
    }

    public IProject getProject()
    {
        return this.project;
    }

    public void setProject(IProject project)
    {
        this.project = project;
    }

}
