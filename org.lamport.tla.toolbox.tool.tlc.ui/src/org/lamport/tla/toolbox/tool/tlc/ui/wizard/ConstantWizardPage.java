package org.lamport.tla.toolbox.tool.tlc.ui.wizard;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
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
        container.setLayoutData(new GridData(SWT.LEFT, SWT.TOP, true, true));
        GridLayout layout = new GridLayout(2, false);
        container.setLayout(layout);
        GridData gd;

        paramComposite = new LabeledListComposite(container, assignment.getLabel(), assignment.getParams()); 
        gd = new GridData(SWT.LEFT, SWT.TOP, false, true);
        paramComposite.setLayoutData(gd);

        text = new Text(container, SWT.BORDER | SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);
        text.setText(assignment.getRight());
        gd = new GridData(SWT.RIGHT, SWT.TOP, true, true);
        gd.minimumWidth = 500;
        gd.minimumHeight = 100;
        text.setLayoutData(gd);
        
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
    
    public boolean finish()
    {
        return false;
    }

    public void dispose()
    {
        if (assignment.getParams().length > 0) 
        {
            this.assignment.setParams(paramComposite.getValues());
        }

        this.assignment.setRight(text.getText());
        super.dispose();
    }
    
    
}
