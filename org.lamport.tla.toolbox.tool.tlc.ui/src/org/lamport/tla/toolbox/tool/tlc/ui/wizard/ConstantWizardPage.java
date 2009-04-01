package org.lamport.tla.toolbox.tool.tlc.ui.wizard;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
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
    private Text source;
    private Button makeModelValue;

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

        // TODO replace by Source Viewer
        source = new Text(container, SWT.BORDER | SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);
        source.setText(assignment.getRight());
        gd = new GridData(SWT.RIGHT, SWT.TOP, true, true);
        gd.minimumWidth = 500;
        gd.minimumHeight = 100;
        source.setLayoutData(gd);

        // constant, not an operator
        if (!paramComposite.hasParameters())
        {
            makeModelValue = new Button(container, SWT.CHECK);
            makeModelValue.setText("Make a Model Value");
            makeModelValue.addSelectionListener(new SelectionAdapter() {
                public void widgetSelected(SelectionEvent e)
                {
                    source.setEnabled(!makeModelValue.getSelection());
                }
            });
            gd = new GridData(SWT.LEFT, SWT.TOP, false, false);
            gd.horizontalSpan = 2;
            makeModelValue.setLayoutData(gd);
            makeModelValue.setSelection(assignment.isModelValue());

            source.setEnabled(!makeModelValue.getSelection());
        }

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
        this.assignment.setModelValue(makeModelValue.getSelection());
        if (!this.assignment.isModelValue())
        {
            if (paramComposite.hasParameters())
            {
                this.assignment.setParams(paramComposite.getValues());
            }
            this.assignment.setRight(source.getText());
        }
        super.dispose();
    }

}
