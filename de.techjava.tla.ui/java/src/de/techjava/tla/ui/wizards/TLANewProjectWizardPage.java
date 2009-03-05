package de.techjava.tla.ui.wizards;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

import de.techjava.tla.ui.UIPlugin;
import de.techjava.tla.ui.util.ITLAProjectConstants;
import de.techjava.tla.ui.widgets.ProjectLayoutComposite;

/**
 * TLA+ new project page
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLANewProjectWizardPage.java,v 1.1 2005/08/22 15:43:35 szambrovski Exp $
 */
public class TLANewProjectWizardPage 
	extends WizardPage
{

    private IStatus currentStatus;
	private String 	projectName	= "";
	private ProjectLayoutComposite projectLayoutComposite;
	
	private Text 	projectNameText;
    
    
    public TLANewProjectWizardPage()
    {
        super("newTLAProjectWizardPage");
		setTitle("TLA+ Project");
		setDescription("Creates a new TLA+ project");
		currentStatus= createStatus(IStatus.OK, ""); 
    }
	/**
	 * @see org.eclipse.jface.dialogs.IDialogPage#createControl(org.eclipse.swt.widgets.Composite)
	 */
	public void createControl(Composite parent) 
	{
		Composite composite= new Composite(parent, SWT.NONE);
		GridLayout gd= new GridLayout();
		gd.numColumns= 2;
		composite.setLayout(gd);
			
		Label label= new Label(composite, SWT.LEFT);
		label.setText("Project Name:");
			
		projectNameText= new Text(composite, SWT.SINGLE | SWT.BORDER);
		projectNameText.setText(projectName);
		projectNameText.addModifyListener(new ModifyListener() 
		{
			public void modifyText(ModifyEvent e) {
				if (!projectNameText.isDisposed()) {
					validateProjectName(projectNameText.getText());
				}
			}
		});
		projectNameText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));

		this.projectLayoutComposite = new ProjectLayoutComposite(composite);
		initDefaults();
			
		setControl(composite);
	}
	/**
	 * @see org.eclipse.jface.wizard.IWizardPage#getName()
	 */
	public String getProjectName()
	{
		return this.projectName;
	}
	/**
	 * Retrieves the source folder location
	 * @return
	 */
	public String getSourceFolder()
	{
	    return (isSeparated()) ? projectLayoutComposite.getSourceFolder() : ""; 
	}
	/**
	 * Retrieves the config folder location
	 * @return
	 */
	public String getConfigFolder()
	{
	    return (isSeparated()) ? projectLayoutComposite.getConfigFolder() : "";
	}
	
    /**
     * @return
     */
    public String getWorkingFolder() {
        return projectLayoutComposite.getWorkingFolder();
    }

	/**
	 * Retrieves the project layout
	 * @return true if the project should be created in separated mode
	 */
	public boolean isSeparated()
	{
	    return (this.projectLayoutComposite.isProjectLayoutSeparated());
	}
	/**
	 * Validate a project name
	 * @param text
	 */
	private void validateProjectName(String text) 
	{
		IWorkspace workspace= ResourcesPlugin.getWorkspace();
		IStatus status= workspace.validateName(text, IResource.PROJECT);
		if (status.isOK()) {
			if (workspace.getRoot().getProject(text).exists()) {
				status= createStatus(IStatus.ERROR, "A Project with this name already exists."); 
			}
		}	
		updateStatus(status);
		projectName= text;
	}	
	/**
	 * Update status
	 * @param status
	 */
	private void updateStatus(IStatus status) 
	{
		currentStatus= status;
		setPageComplete(!status.matches(IStatus.ERROR));
	}
	/**
	 * Initialize ddefault values
	 */
	private void initDefaults()
	{
	    IPreferenceStore store = UIPlugin.getDefault().getPreferenceStore();
	    this.projectLayoutComposite.setSourceFolder(store.getDefaultString(ITLAProjectConstants.TLA_PROJECT_LAYOUT_SEPARATED_SOURCEDIR));
	    this.projectLayoutComposite.setConfigFolder(store.getDefaultString(ITLAProjectConstants.TLA_PROJECT_LAYOUT_SEPARATED_CONFIGDIR));
	    this.projectLayoutComposite.setWorkingFolder(store.getDefaultString(ITLAProjectConstants.TLA_PROJECT_LAYOUT_WORKINGDIR));
		this.projectLayoutComposite.setProjectLayout(store.getDefaultBoolean(ITLAProjectConstants.TLA_PROJECT_LAYOUT_SEPARATED));
		
	}
    /**
     * Creates status
     * @param severity
     * @param message
     * @return
     */
	private static IStatus createStatus(int severity, String message) 
	{
	    //return new Status(severity, Platform.getExtensionRegistry().getExtension(UIPlugin.PLUGIN_ID).getUniqueIdentifier(), severity, message, null);
		return new Status(severity, UIPlugin.PLUGIN_ID, severity, message, null);
	}

}

/*
 * $Log: TLANewProjectWizardPage.java,v $
 * Revision 1.1  2005/08/22 15:43:35  szambrovski
 * sf cvs init
 *
 * Revision 1.4  2004/10/15 01:16:53  sza
 * working directory added
 *
 * Revision 1.3  2004/10/13 21:34:10  sza
 * id changed
 *
 * Revision 1.2  2004/10/13 14:44:17  sza
 * project storage
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.1  2004/10/12 09:55:12  sza
 * additions
 *
 * Revision 1.1  2004/10/06 01:02:29  sza
 * initial commit
 *
 * Revision 1.1  2004/10/06 00:59:04  sza
 * initial commit
 *
 *
 */