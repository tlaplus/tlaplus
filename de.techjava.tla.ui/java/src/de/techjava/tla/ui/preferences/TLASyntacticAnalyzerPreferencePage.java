package de.techjava.tla.ui.preferences;

import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.DirectoryDialog;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.List;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

import de.techjava.tla.ui.UIPlugin;
import de.techjava.tla.ui.util.ITLASANYConstants;
import de.techjava.tla.ui.util.ParserManager;

/**
 * TLA Semantic Analyser Preferences
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLASyntacticAnalyzerPreferencePage.java,v 1.1 2005/08/22 15:43:31 szambrovski Exp $
 */
public class TLASyntacticAnalyzerPreferencePage 
	extends PreferencePage
	implements IWorkbenchPreferencePage 
{
    
	private List 	lstLibraries;
    private Button 	btnGenerateStats;
    private Button 	btnBeVerbose;
    private Button 	btnRunLevelChecking;
    private Button 	btnDoSemantic;
    
    private ParserManager manager;
    
    /**
     * Constructor
     */
    public TLASyntacticAnalyzerPreferencePage()
    {
		setDescription("TLA+ module locations are searched for modules on syntactical analysis.");
    }
    
    /**
     * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
     */
    public void init(IWorkbench workbench) 
    {
        manager = UIPlugin.getDefault().getSANYManager();
		setPreferenceStore(UIPlugin.getDefault().getPreferenceStore());
    }
    
	/**
	 * Performs special processing when this page's Restore Defaults button has been pressed.
	 * be the default 
	 */
	protected void performDefaults() 
	{
		lstLibraries.setItems(convertPathToStrings(manager.getDefaultLibraries()));
		btnBeVerbose.setSelection(getPreferenceStore().getDefaultBoolean(ITLASANYConstants.TLA_SANY_DO_DEBUGGING));
		btnDoSemantic.setSelection(getPreferenceStore().getDefaultBoolean(ITLASANYConstants.TLA_SANY_DO_SEMANTIC_ANALYSIS));
		btnGenerateStats.setSelection(getPreferenceStore().getDefaultBoolean(ITLASANYConstants.TLA_SANY_DO_STATS));
		btnRunLevelChecking.setSelection(getPreferenceStore().getDefaultBoolean(ITLASANYConstants.TLA_SANY_DO_LEVEL_CHECKING));
	}
	/**
	 * Read values from store and display them
	 */
	private void initValues()
	{
		btnBeVerbose.setSelection( getPreferenceStore().getBoolean(ITLASANYConstants.TLA_SANY_DO_DEBUGGING));
		btnGenerateStats.setSelection( getPreferenceStore().getBoolean(ITLASANYConstants.TLA_SANY_DO_STATS));
		btnDoSemantic.setSelection( getPreferenceStore().getBoolean(ITLASANYConstants.TLA_SANY_DO_SEMANTIC_ANALYSIS));
		btnRunLevelChecking.setSelection( getPreferenceStore().getBoolean(ITLASANYConstants.TLA_SANY_DO_LEVEL_CHECKING));
		lstLibraries.setItems(convertPathToStrings(manager.getLibraries()));
	}
	
	/**
	 * @see org.eclipse.jface.preference.IPreferencePage#performOk()
	 */
	public boolean performOk() 
	{
		manager.setLibraries(lstLibraries.getItems());
		getPreferenceStore().setValue(ITLASANYConstants.TLA_SANY_DO_DEBUGGING, 			btnBeVerbose.getSelection());
		getPreferenceStore().setValue(ITLASANYConstants.TLA_SANY_DO_SEMANTIC_ANALYSIS, 	btnDoSemantic.getSelection());
		getPreferenceStore().setValue(ITLASANYConstants.TLA_SANY_DO_STATS, 				btnGenerateStats.getSelection());
		getPreferenceStore().setValue(ITLASANYConstants.TLA_SANY_DO_LEVEL_CHECKING, 	btnRunLevelChecking.getSelection());
		return super.performOk();
	}
	
	
	/**
	 * @see org.eclipse.jface.preference.PreferencePage#performApply()
	 */
    protected void performApply() 
    {
        performOk();
    }
    /**
     * @see org.eclipse.jface.preference.PreferencePage#createContents(org.eclipse.swt.widgets.Composite)
     */
    protected Control createContents(Composite parent) 
    {
        Composite mainComposite = new Composite(parent, SWT.NULL);

        GridLayout mainLayout = new GridLayout();
		mainComposite.setLayout(mainLayout);			
		 
		mainComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));

		Label	listCaption = new Label(mainComposite, SWT.NULL);
		listCaption.setText("Defined user TLA+ module libraries:");
		GridData listCaptionLayoutData = new GridData();
		listCaptionLayoutData.horizontalSpan = 2;
		listCaption.setLayoutData(listCaptionLayoutData);
		
		lstLibraries = new List(mainComposite, SWT.BORDER);
		GridData listLayoutData = new GridData(GridData.FILL_BOTH);
		lstLibraries.setLayoutData(listLayoutData);

		Composite buttonComposite = new Composite( mainComposite,SWT.NULL );
		RowLayout buttonLayout = new RowLayout(SWT.HORIZONTAL);
		buttonLayout.pack = false;
		buttonComposite.setLayout(buttonLayout);

		Button addButton = new Button(buttonComposite, SWT.PUSH );
		addButton.setText("Add...");
		addButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent event) 
			{
			    DirectoryDialog dialog = new DirectoryDialog(getShell());
			    dialog.setText("Select library directory");
			    String selected = dialog.open();
			    if (selected != null) 
			    {
			        
			        lstLibraries.add(new Path(selected).addTrailingSeparator().toString(), lstLibraries.getItemCount());
			    }
			}
		});
		
		Button removeButton = new Button(buttonComposite, SWT.PUSH );
		removeButton.setText("Remove"); 
		removeButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent event) {
				lstLibraries.remove(lstLibraries.getSelectionIndex());
			}
		});

		Group analyserOptionsGroup = new Group(mainComposite, SWT.NULL);
		analyserOptionsGroup.setText("Analyzer options:");
		analyserOptionsGroup.setLayout( new GridLayout() );
		GridData optionLayoutData = new GridData(GridData.FILL_HORIZONTAL);
		analyserOptionsGroup.setLayoutData(optionLayoutData);

		btnDoSemantic = new Button( analyserOptionsGroup, SWT.CHECK );
		btnDoSemantic.setText("Run analysis");
		btnDoSemantic.addSelectionListener(new SelectionListener()
		        {
		    		/**
		    		 * @see org.eclipse.swt.events.SelectionListener#widgetSelected(org.eclipse.swt.events.SelectionEvent)
		    		 */
		            public void widgetSelected(SelectionEvent e) 
		            {
		                if (btnDoSemantic.getSelection())
		                    btnRunLevelChecking.setEnabled(true);
		                else
		                    btnRunLevelChecking.setEnabled(false);
		            }
		            /**
		             * @see org.eclipse.swt.events.SelectionListener#widgetDefaultSelected(org.eclipse.swt.events.SelectionEvent)
		             */
		            public void widgetDefaultSelected(SelectionEvent e) 
		            {
		                if (btnDoSemantic.getSelection())
		                    btnRunLevelChecking.setEnabled(true);
		                else
		                    btnRunLevelChecking.setEnabled(false);
	            	}
		        }
		);
		btnRunLevelChecking = new Button( analyserOptionsGroup, SWT.CHECK );
		btnRunLevelChecking.setText("Run level checking");

		btnBeVerbose = new Button( analyserOptionsGroup, SWT.CHECK );
		btnBeVerbose.setText("Be &verbose");
		
		
		btnGenerateStats = new Button( analyserOptionsGroup, SWT.CHECK );
		btnGenerateStats.setText("Generate &statitics");
		
		initValues();
		
		return mainComposite;
    }
    
    private String[] convertPathToStrings(IPath[] paths)
    {
        
	    String[] names = new String[paths.length];
	    for (int i=0; i < paths.length; i++)
	    {
	        names[i] = paths[i].toOSString(); 
	    }
	    return names;
    }

}

/*
 * $Log: TLASyntacticAnalyzerPreferencePage.java,v $
 * Revision 1.1  2005/08/22 15:43:31  szambrovski
 * sf cvs init
 *
 * Revision 1.2  2004/10/13 09:46:02  sza
 * plugin integration
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.1  2004/10/12 09:55:11  sza
 * additions
 *
 * Revision 1.2  2004/10/07 00:05:53  sza
 * method renaming
 *
 * Revision 1.1  2004/10/06 01:02:29  sza
 * initial commit
 *
 * Revision 1.1  2004/10/06 00:59:04  sza
 * initial commit
 *
 *
 */