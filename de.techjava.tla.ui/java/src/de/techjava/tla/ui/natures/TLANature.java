package de.techjava.tla.ui.natures;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IProjectNature;
import org.eclipse.core.runtime.CoreException;

import de.techjava.tla.ui.builders.TLABuilder;

/**
 * 
 * TLA Nature
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLANature.java,v 1.1 2005/08/22 15:43:38 szambrovski Exp $
 */
public class TLANature 
	implements IProjectNature 
{

	private IProject project;
    public static final String NATURE_ID = "de.techjava.tla.ui.natures.TLANature";

	/**
	 * @see org.eclipse.core.resources.IProjectNature#configure()
	 */
	public void configure() 
		throws CoreException 
	{
	    // System.out.println("nature added");
	    IProjectDescription desc = project.getDescription();
	    ICommand[] commands = desc.getBuildSpec();
	    boolean found = false;

	    for (int i = 0; i < commands.length; ++i) 
	    {
	       if (commands[i].getBuilderName().equals(TLABuilder.BUILDER_ID)) 
	       {
	          found = true;
	          break;
	       }
	    }
	    if (!found) 
	    {
	       // System.out.println("Adding a builder");
	       //add builder to project
	       ICommand[] newCommands = new ICommand[commands.length + 1];
	       
	       // Add it before other builders.
	       System.arraycopy(commands, 0, newCommands, 1, commands.length);
	       newCommands[0] = desc.newCommand();
	       newCommands[0].setBuilderName( TLABuilder.BUILDER_ID );

	       desc.setBuildSpec(newCommands);
	       project.setDescription(desc, null);
	    }

	}

	/**
	 * @see org.eclipse.core.resources.IProjectNature#deconfigure()
	 */
	public void deconfigure() 
		throws CoreException 
	{
	    // System.out.println("nature removed");
	    IProjectDescription desc = project.getDescription();
	    ICommand[] commands = desc.getBuildSpec();
	    ICommand[] newCommands = new ICommand[commands.length - 1];
	    
	    for (int j = 0, i = 0; i < commands.length; ++i) 
	    {
	       if (!commands[i].getBuilderName().equals(TLABuilder.BUILDER_ID)) 
	       {
	          newCommands[j++] = commands[i];
	       }
	    }

	       desc.setBuildSpec(newCommands);
	       project.setDescription(desc, null);
	}

	/**
	 * @see org.eclipse.core.resources.IProjectNature#getProject()
	 */
	public IProject getProject() 
	{
		return project;
	}

	/**
	 * @see org.eclipse.core.resources.IProjectNature#setProject(org.eclipse.core.resources.IProject)
	 */
	public void setProject(IProject project) {
		this.project = project;

	}

}
