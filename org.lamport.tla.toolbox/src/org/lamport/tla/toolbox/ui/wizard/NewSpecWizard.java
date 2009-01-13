package org.lamport.tla.toolbox.ui.wizard;

import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;

/**
 * A wizard for creation of new specifications
 * 
 * @author zambrovski
 */
public class NewSpecWizard extends Wizard implements INewWizard
{

    private IStructuredSelection selection;
    private NewSpecWizardPage    page;
    private Spec                 spec = null;

    public NewSpecWizard()
    {
        super();
    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.jface.wizard.Wizard#performFinish()
     */
    public boolean performFinish()
    {
        // create new spec
        spec = Spec.createNewSpec(page.getSpecName(), page.getRootFilename());
        // add spec to the spec manager
        Activator.getSpecManager().addSpec(spec);

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

    
    public Spec getSpec()
    {
        return this.spec;
    }
}
