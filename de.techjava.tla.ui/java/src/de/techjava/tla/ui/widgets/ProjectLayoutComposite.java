package de.techjava.tla.ui.widgets;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

/**
 * Project layout composite
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: ProjectLayoutComposite.java,v 1.1 2005/08/22 15:43:33 szambrovski Exp $
 */
public class ProjectLayoutComposite 
{
    
    private Group		projectLayoutGroup;
    private Button 		projectLayoutMixed;
    private Button 		projectLayoutSeparated;
    private Text 		projectFolderSource;
    private Text 		projectFolderConfig;
    private Text 		projectFolderWorking;
    private Composite 	projectFolderGroup;

    /**
     * 
     */
    public ProjectLayoutComposite(Composite parent) 
    {
        createContents(parent);
    }
    
    protected void createContents(Composite parent)
    {
        Group	projectLayoutGroup = new Group(parent, SWT.NULL);
		GridLayout projectLayoutGroupLayout = new GridLayout();
		GridData projectLayoutGroupLayoutData = new GridData(GridData.FILL_HORIZONTAL);
		projectLayoutGroupLayoutData.horizontalSpan = 2;
		projectLayoutGroupLayoutData.grabExcessHorizontalSpace = true;
		projectLayoutGroup.setLayout(projectLayoutGroupLayout);
		projectLayoutGroup.setLayoutData(projectLayoutGroupLayoutData);
		projectLayoutGroup.setText("Project layout");
		
		projectLayoutMixed 		= new Button(projectLayoutGroup, SWT.RADIO);
		projectLayoutSeparated 	= new Button(projectLayoutGroup, SWT.RADIO);
		projectLayoutMixed.setText("Use project folder as root for all files");
		projectLayoutSeparated.setText("Create separate source and configuration folders");
		projectLayoutMixed.addSelectionListener(new SelectionListener() 
	        {
		    	/**
		    	 * @see org.eclipse.swt.events.SelectionListener#widgetSelected(org.eclipse.swt.events.SelectionEvent)
		    	 */
		    	public void widgetSelected(SelectionEvent e) 
	            {
	                projectLayoutSeparated.setSelection(!projectLayoutMixed.getSelection());
	            }
		    	/**
		    	 * @see org.eclipse.swt.events.SelectionListener#widgetDefaultSelected(org.eclipse.swt.events.SelectionEvent)
		    	 */
	            public void widgetDefaultSelected(SelectionEvent e) 
	            {
	                projectLayoutSeparated.setSelection(!projectLayoutMixed.getSelection());
	            }
        	}
		);
		projectLayoutSeparated.addSelectionListener(new SelectionListener() 
		        {
			    	
                    /**
			    	 * @see org.eclipse.swt.events.SelectionListener#widgetSelected(org.eclipse.swt.events.SelectionEvent)
			    	 */
			    	public void widgetSelected(SelectionEvent e) 
		            {
	                    projectLayoutMixed.setSelection(!projectLayoutSeparated.getSelection());
	                    projectFolderSource.setEnabled(projectLayoutSeparated.getSelection());
	                    projectFolderConfig.setEnabled(projectLayoutSeparated.getSelection());
		            }
			    	/**
			    	 * @see org.eclipse.swt.events.SelectionListener#widgetDefaultSelected(org.eclipse.swt.events.SelectionEvent)
			    	 */
		            public void widgetDefaultSelected(SelectionEvent e) 
		            {
	                    projectLayoutMixed.setSelection(!projectLayoutSeparated.getSelection());
	                    projectFolderSource.setEnabled(projectLayoutSeparated.getSelection());
	                    projectFolderConfig.setEnabled(projectLayoutSeparated.getSelection());
		            }
	        	}
		);
		
		projectFolderGroup = new Composite(projectLayoutGroup, SWT.NULL);
		GridData projectFolderGroupLayoutData = new GridData(GridData.FILL_HORIZONTAL);
		projectFolderGroupLayoutData.grabExcessHorizontalSpace = true;
		projectFolderGroup.setLayout(new GridLayout(2, false));
		projectFolderGroup.setLayoutData(projectFolderGroupLayoutData);

		Label sourceFolderLabel = new Label(projectFolderGroup, SWT.NULL);
		sourceFolderLabel.setText("Source folder");
		
		projectFolderSource = new Text(projectFolderGroup, SWT.SINGLE | SWT.BORDER);
		projectFolderSource.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		
		Label configFolderLabel = new Label(projectFolderGroup, SWT.NULL);
		configFolderLabel.setText("Config folder");
		
		projectFolderConfig = new Text(projectFolderGroup, SWT.SINGLE | SWT.BORDER);
		projectFolderConfig.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));

		Label workFolderLabel = new Label(projectFolderGroup, SWT.NULL);
		workFolderLabel.setText("Working folder");
		
		projectFolderWorking = new Text(projectFolderGroup, SWT.SINGLE | SWT.BORDER);
		projectFolderWorking.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		
    }
    /**
     * Sets project layout
     * @param value Use ProjectLayoutComposite.MIXED ProjectLayoutComposite.SEPARATED
     */
    public void setProjectLayout(boolean projectLayoutSeparated)
    {
        if (projectLayoutSeparated)
        {
            this.projectFolderConfig.setEnabled(true);
            this.projectFolderSource.setEnabled(true);
            this.projectFolderWorking.setEnabled(true);
            this.projectLayoutSeparated.setSelection(true);
            this.projectLayoutMixed.setSelection(false);
        } else 
        {
            this.projectFolderConfig.setEnabled(false);
            this.projectFolderSource.setEnabled(false);
            this.projectFolderWorking.setEnabled(false);
            this.projectLayoutSeparated.setSelection(false);
            this.projectLayoutMixed.setSelection(true);
        }
    }
	/**
	 * Retrieves the source folder location
	 * @return
	 */
	public String getSourceFolder()
	{
	    return this.projectFolderSource.getText();
	}
	/**
	 * Retrieves the config folder location
	 * @return
	 */
	public String getConfigFolder()
	{
	    return this.projectFolderConfig.getText();
	}
	/**
	 * Retrieves the working folder
	 * @return
	 */
	public String getWorkingFolder()
	{
	    return this.projectFolderWorking.getText();
	}
	/**
	 * Retrieves the project layout
	 * @return true if the project should be created in separated mode
	 */
	public boolean isProjectLayoutSeparated()
	{
	    return this.projectLayoutSeparated.getSelection();
	}

    /**
     * @param string
     */
    public void setSourceFolder(String folderPath) 
    {
        this.projectFolderSource.setText(folderPath);
    }
    /**
     * @param string
     */
    public void setConfigFolder(String folderPath) 
    {
        this.projectFolderConfig.setText(folderPath);
    }

    /**
     * @param projectWorking
     */
    public void setWorkingFolder(String folderPath) 
    {
        this.projectFolderWorking.setText(folderPath);
        
    }

}

/*
 * $Log: ProjectLayoutComposite.java,v $
 * Revision 1.1  2005/08/22 15:43:33  szambrovski
 * sf cvs init
 *
 * Revision 1.5  2004/10/15 01:16:53  sza
 * working directory added
 *
 * Revision 1.4  2004/10/15 00:38:42  sza
 * working folder added
 *
 * Revision 1.3  2004/10/13 14:44:08  sza
 * project storage
 *
 * Revision 1.2  2004/10/13 12:41:01  sza
 * changed separated property from string to boolen
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.1  2004/10/12 09:55:11  sza
 * additions
 *
 *
 */