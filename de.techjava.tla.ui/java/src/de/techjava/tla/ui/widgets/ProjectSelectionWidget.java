package de.techjava.tla.ui.widgets;

import java.util.Vector;

import org.eclipse.core.resources.IProject;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.dialogs.ElementListSelectionDialog;
import org.eclipse.ui.dialogs.ResourceSelectionDialog;
import org.eclipse.ui.model.WorkbenchLabelProvider;

import de.techjava.tla.ui.util.TLACore;

/**
 * creates a groups where a project can be selected
 * 
 * @author Boris Gruschko, <a href="http://gruschko.org">http://gruschko.org</a> 
 * @version $Id: ProjectSelectionWidget.java,v 1.1 2005/08/22 15:43:33 szambrovski Exp $
 */
public class ProjectSelectionWidget 
{
    private IProject  	project;	
    private Text	  	projectName;
    private Button	  	projectSelectionButton;
    private Group 	  	group;
    private Vector		listeners = new Vector();
    
    
    public ProjectSelectionWidget( Composite composite )
    {
    
        createControls(composite);
    }
    
    private void createControls(Composite composite)
    {
        group = new Group( composite, SWT.FILL);
        GridLayout layout = new GridLayout(2, false);
        GridData gd = new GridData( GridData.FILL_HORIZONTAL | GridData.GRAB_HORIZONTAL );
        group.setLayout( layout );
        group.setLayoutData( gd );
        group.setText( "Project" );        
        
        projectName = new Text( group, SWT.BORDER | SWT.SINGLE | SWT.FILL );
        
        GridData projectNameLayout = new GridData(GridData.FILL_HORIZONTAL | GridData.GRAB_HORIZONTAL);
        projectNameLayout.horizontalAlignment = GridData.FILL;
        projectName.setLayoutData(projectNameLayout);

        projectSelectionButton = new Button( group, SWT.PUSH );
        projectSelectionButton.setText( "Browse" );
        projectSelectionButton.addSelectionListener( 
                new SelectionListener()
                {
                    public void widgetSelected(SelectionEvent e) 
                    {
                        widgetDefaultSelected(e);
                    }

                    public void widgetDefaultSelected(SelectionEvent e) 
                    {
                    	ElementListSelectionDialog dialog = 
                    	    new ElementListSelectionDialog( group.getShell(), 
                    	    	new WorkbenchLabelProvider());
                    	
                    	dialog.setElements(TLACore.getTLAProjects());
                    	dialog.setTitle( "TLA Projects" );
                    	
                        if ( dialog.open() == ResourceSelectionDialog.OK ) {
                            project = (IProject) (dialog.getResult() != null ? dialog.getResult()[0] : null);
                            projectName.setText( project != null ? project.getName() : "" );
                            
                        }
                        projectSelectedOccured();
                }

    	    }
        );
    }
    
    /**
     * retrieves the selected project
     * 
     * @return reference to the selected proejct or null, if
     * 	no project has been seleced
     */
    public IProject getProject()
    {
        return project;
    }
    /**
     * Sets a project
     * @param attribute
     */
    public void setProject(String projectName) 
    {
        project = TLACore.getProjectByName(projectName);
        this.projectName.setText( project != null ? project.getName() : "" );
        projectSelectedOccured();
    }
    
    public void addProjectSelectionListener( IProjectSelectionListener listener )
    {
        this.listeners.add(listener);
    }
    
    public void removeProjectSelectionListener( IProjectSelectionListener listener)
    {
        this.listeners.remove(listener);
    }

    private void projectSelectedOccured() 
    {
        // inform listeners
        for (int i = 0; i < listeners.size(); i++)
        {
            ((IProjectSelectionListener)listeners.elementAt(i)).projectSelected(project);
        }
    }
    
}

/*
 * $Log: ProjectSelectionWidget.java,v $
 * Revision 1.1  2005/08/22 15:43:33  szambrovski
 * sf cvs init
 *
 * Revision 1.3  2004/10/25 16:50:09  sza
 * new content provider used
 *
 * Revision 1.2  2004/10/13 11:13:24  bgr
 * layout fixed
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.2  2004/10/12 09:54:47  sza
 * running copy
 *
 * Revision 1.1  2004/10/11 19:39:43  bgr
 * initial load
 *
 *
 */