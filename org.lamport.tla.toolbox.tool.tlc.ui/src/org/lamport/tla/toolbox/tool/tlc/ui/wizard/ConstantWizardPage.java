package org.lamport.tla.toolbox.tool.tlc.ui.wizard;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Text;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ConstantWizardPage extends WizardPage
{
    private Assignment assignment;
    private LabeledListComposite paramComposite;
    private Text text;

    public ConstantWizardPage(String action, String description, Assignment assignement)
    {
        super("ConstantWizardPage");
        setTitle(action);
        setDescription(description);
        this.assignment = assignement;
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.dialogs.IDialogPage#createControl(org.eclipse.swt.widgets.Composite)
     */
    public void createControl(Composite parent)
    {
        Composite container = new Composite(parent, SWT.NULL);
        GridLayout layout = new GridLayout(2, false);
        container.setLayout(layout);

        if (assignment.getParams().length > 0) 
        {
           paramComposite = new LabeledListComposite(container, assignment.getLabel(), assignment.getParams()); 
        }
        text = new Text(container, SWT.NONE);
        text.setText(assignment.getRight());
        setControl(container);
    }

    /**
     * The assignment with modified params and right part 
     * @return
     */
    public Assignment getAssignment()
    {
        return this.assignment;
    }

    public void dispose()
    {
        this.assignment.setParams(paramComposite.getValues());
        this.assignment.setRight(text.getText());
        super.dispose();
    }
    
    
}
