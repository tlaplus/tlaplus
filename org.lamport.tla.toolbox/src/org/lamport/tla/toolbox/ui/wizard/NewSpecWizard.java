package org.lamport.tla.toolbox.ui.wizard;

import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;

/**
 * A wizard for creation of new specifications
 * 
 * @author zambrovski
 */
public class NewSpecWizard extends Wizard implements INewWizard
{

    private IStructuredSelection selection;
    private NewSpecWizardPage page;

    private String specName;
	private String rootFilename;
	private boolean importExisting;

	/*
     * (non-Javadoc)
     * @see org.eclipse.jface.wizard.Wizard#performFinish()
     */
    public boolean performFinish()
    {

        rootFilename = page.getRootFilename();
        specName = page.getSpecName();
        importExisting = page.importExisting();

        return true;
    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.ui.IWorkbenchWizard#init(org.eclipse.ui.IWorkbench,
     * org.eclipse.jface.viewers.IStructuredSelection)
     */
    public void init(IWorkbench workbench, IStructuredSelection selection)
    {
        this.selection = selection;
    }

    /**
     * Adding the page to the wizard.
     */
    public void addPages()
    {
        page = new NewSpecWizardPage();
        addPage(page);
    }

    public ISelection getSelection()
    {
        return this.selection;
    }

	/**
	 * @return the specName
	 */
	public String getSpecName() {
		return specName;
	}

	/**
	 * @return the rootFilename
	 */
	public String getRootFilename() {
		return rootFilename;
	}

    /**
	 * @return the importExisting
	 */
	public boolean isImportExisting() {
		return importExisting;
	}
}
