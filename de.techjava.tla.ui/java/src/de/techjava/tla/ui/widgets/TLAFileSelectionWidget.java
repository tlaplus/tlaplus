package de.techjava.tla.ui.widgets;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.dialogs.ElementTreeSelectionDialog;
import org.eclipse.ui.dialogs.ISelectionStatusValidator;
import org.eclipse.ui.model.WorkbenchLabelProvider;

import de.techjava.tla.ui.util.ITLAProjectConstants;
import de.techjava.tla.ui.widgets.provider.TLAFolderProvider;


/**
 * Selects a TLA file
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLAFileSelectionWidget.java,v 1.1 2005/08/22 15:43:33 szambrovski Exp $
 */
public class TLAFileSelectionWidget
	implements IProjectSelectionListener
{
	
    private Group						mainFileGroup;
    private Text						mainFile;
    private Button						browseButton;
    private ElementTreeSelectionDialog 	dialog;
    private IProject					project;
    private	List						listeners	=	new LinkedList();
    
    private String						fileExtension;
    private String  					title;
    private String 						groupLabelText;
    
    private ITreeContentProvider 		folderProvider;
    
    
    /**
     * Constructor for a composite widget
     * @param parent parent SWT control
     * @param fileExtension file extensions for files to be shown
     * @param label label text of the group
     * @param title title of dialog chown by browsing
     */
    public TLAFileSelectionWidget(Composite parent, String fileExtension, String label, String title)
    {
        if (ITLAProjectConstants.CFG_FILE_EXTENSION.equals(fileExtension)) 
        {
            folderProvider = new TLAFolderProvider( false, true, false, new String[]{ITLAProjectConstants.CFG_FILE_EXTENSION} );
        } else if (ITLAProjectConstants.TLA_FILE_EXTENSION.equals(fileExtension)) 
        {
            folderProvider = new TLAFolderProvider( true, false, false, new String[]{ITLAProjectConstants.TLA_FILE_EXTENSION} );
        } else 
        {
            folderProvider = new TLAFolderProvider( true, true, true );
        }
        this.groupLabelText = label;
        this.title = title;
        this.fileExtension	=	fileExtension;
        createControls(parent);
        browseButton.setEnabled(false);
        mainFile.setEnabled(false);
        
    }
    
    
    public void createControls( Composite parent )
    {
        mainFileGroup = new Group(parent, SWT.FILL);
		GridLayout mainFileGroupLayout = new GridLayout(2, false);
		GridData mainFileGroupData = new GridData(GridData.FILL_HORIZONTAL | GridData.GRAB_HORIZONTAL);
		mainFileGroup.setLayout(mainFileGroupLayout);
		mainFileGroup.setLayoutData(mainFileGroupData);
		mainFileGroup.setText(this.groupLabelText);
		
		mainFile = new Text(mainFileGroup, SWT.BORDER | SWT.SINGLE | SWT.FILL);
		GridData mainFileData = new GridData(GridData.FILL_HORIZONTAL | GridData.GRAB_HORIZONTAL);
		mainFileData.horizontalAlignment = GridData.FILL;
		mainFile.setLayoutData(mainFileData);
		
		browseButton = new Button(mainFileGroup, SWT.PUSH);
		browseButton.setText("Browse");
		
		browseButton.addSelectionListener(new SelectionListener()
		        {

                    public void widgetSelected(SelectionEvent e) 
                    {
                        widgetDefaultSelected(e);
                    }

                    public void widgetDefaultSelected(SelectionEvent e) 
                    {
                    	
                        if ( dialog.open() == ElementTreeSelectionDialog.OK ) 
                        {
                            mainFile.setText( ((IResource)dialog.getFirstResult()).getProjectRelativePath().toString() );
                            fireFileSelected( (IFile)dialog.getFirstResult());
                        }

                    }
		    	
		        }
		);
        dialog = new ElementTreeSelectionDialog( mainFileGroup.getShell(), 
                new WorkbenchLabelProvider(), 
                folderProvider
        );
        
        dialog.setValidator( 
        		new ISelectionStatusValidator()
				{

					public IStatus validate(Object[] selection)
					{
						if ( selection.length < 1 )
							return Status.CANCEL_STATUS;
						
						if ( ((IResource)selection[0]).getType() != IResource.FILE  )
							return Status.CANCEL_STATUS;
						
						return Status.OK_STATUS;
					}
        			
				}
        );
        
    	dialog.setTitle( this.title );
        
    }
    /**
     * Retrieves selected mainfile
     * @return
     */
    public String getMainFile()
    {
        return this.mainFile.getText();
    }
    
    public void setProject(IProject project)
    {
        if (this.project != project) 
        {
            this.project = project;
            this.mainFile.setText("");
        }
        dialog.setInput(this.project);
        this.browseButton.setEnabled(true);
        this.mainFile.setEnabled(true);
    }
    
    /**
     * @see org.gruschko.tla.eclipse.tlclauncher.widgets.IProjectSelectionListener#projectSelected(org.eclipse.core.resources.IProject)
     */
    public void projectSelected(IProject project) 
    {
        setProject(project);
    }

    /**
     * @param attribute
     */
    public void setMainFile(String mainFile) 
    {
        this.mainFile.setText(mainFile);
        
    }
    
    public void addFileSelectionListener( IFileSelectionListener listener )
    {
    	listeners.add( listener );
    }
    
    public void removeSelectionListener( IFileSelectionListener listener )
    {
    	listeners.remove( listener );
    }
    
    protected void fireFileSelected( IFile selectedResource )
    {
    	for ( Iterator i = listeners.iterator(); i.hasNext();)
    	{
    		((IFileSelectionListener)i.next()).fileSelected(selectedResource);
    	}
    }
    /**
     * Sets if the file selection widget is enabled
     * @param enabled 
     */
    public void setEnabled(boolean enabled)
    {
        
        browseButton.setEnabled(enabled);
        mainFile.setEnabled(enabled);
        
        mainFileGroup.setEnabled(enabled);
        mainFileGroup.update();
    }
}

/*
 * $Log: TLAFileSelectionWidget.java,v $
 * Revision 1.1  2005/08/22 15:43:33  szambrovski
 * sf cvs init
 *
 * Revision 1.6  2004/10/25 16:50:09  sza
 * new content provider used
 *
 * Revision 1.5  2004/10/25 11:22:23  bgr
 * file type extensions added
 *
 * Revision 1.4  2004/10/25 10:58:05  bgr
 * only TLA files can be selected
 *
 * Revision 1.3  2004/10/25 10:09:10  bgr
 * apply button handling added
 *
 * Revision 1.2  2004/10/13 11:13:24  bgr
 * layout fixed
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.1  2004/10/12 09:54:47  sza
 * running copy
 *
 *
 */