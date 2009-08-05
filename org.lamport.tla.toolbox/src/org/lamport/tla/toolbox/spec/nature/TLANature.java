package org.lamport.tla.toolbox.spec.nature;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IProjectNature;
import org.eclipse.core.runtime.CoreException;
import org.lamport.tla.toolbox.Activator;

/**
 * TLA Nature
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLANature implements IProjectNature
{
    
    private IProject project;
    public static final String ID = "toolbox.natures.TLANature";


    /**
     * add TLA nature
     */
    public void configure() throws CoreException
    {
        IProjectDescription desc = project.getDescription();
        ICommand[] commands = desc.getBuildSpec();

        boolean tlaBuilderFound = false;
        boolean pcalBuilderFound = false;
        int numberOfBuildersToInstall = 2;
        
        
        for (int i = 0; i < commands.length; ++i) {
            String builderName = commands[i].getBuilderName();
            if (builderName.equals(TLAParsingBuilder.BUILDER_ID)) 
            {
                tlaBuilderFound = true;
                numberOfBuildersToInstall--;
            } else if (builderName.equals(PCalDetectingBuilder.BUILDER_ID))
            {
               pcalBuilderFound = true;
               numberOfBuildersToInstall--;
            }
            
            if (tlaBuilderFound && pcalBuilderFound) 
            {
                return;
            }
        }

        ICommand[] newCommands = new ICommand[commands.length + numberOfBuildersToInstall];
        System.arraycopy(commands, 0, newCommands, 0, commands.length);
        
        int position = commands.length;
        
        if (!tlaBuilderFound) 
        {
            ICommand command = desc.newCommand();
            command.setBuilderName(TLAParsingBuilder.BUILDER_ID);
            newCommands[position] = command;
            position++;
        }
        if (!pcalBuilderFound) 
        {
            ICommand command = desc.newCommand();
            command.setBuilderName(PCalDetectingBuilder.BUILDER_ID);
            newCommands[position] = command;
        }
        
        desc.setBuildSpec(newCommands);
        project.setDescription(desc, null);
        Activator.logDebug("Nature added");
    }

    /**
     * remove TLA nature
     */
    public void deconfigure() throws CoreException
    {
        
        IProjectDescription description = getProject().getDescription();
        ICommand[] commands = description.getBuildSpec();
        for (int i = 0; i < commands.length; ++i) {
            String builderName = commands[i].getBuilderName();
            if (builderName.equals(TLAParsingBuilder.BUILDER_ID) || builderName.equals(PCalDetectingBuilder.BUILDER_ID)) {
                ICommand[] newCommands = new ICommand[commands.length - 1];
                System.arraycopy(commands, 0, newCommands, 0, i);
                System.arraycopy(commands, i + 1, newCommands, i,
                        commands.length - i - 1);
                description.setBuildSpec(newCommands);
            } 
        }
        Activator.logDebug("Nature removed");
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
