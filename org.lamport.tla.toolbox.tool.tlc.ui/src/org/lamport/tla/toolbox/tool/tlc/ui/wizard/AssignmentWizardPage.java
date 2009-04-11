package org.lamport.tla.toolbox.tool.tlc.ui.wizard;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class AssignmentWizardPage extends WizardPage
{
    private Assignment assignment;
    private LabeledListComposite paramComposite;
    private Text source;
    private Button makeModelValue;
    private final int fieldFlags;
    private Button makeSetModelValues;
    private Button makeSymmetricalSet;
    private Button ordinaryValue;
    private Combo typeCombo;
    private Label label;

    public AssignmentWizardPage(String action, String description, Assignment assignement, int fieldFlags)
    {
        super("AssignmentWizardPage");
        this.fieldFlags = fieldFlags;
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

        // constant, no parameters
        if (!paramComposite.hasParameters())
        {

            // both bits set, make a radio list
            if ((fieldFlags & AssignmentWizard.MAKE_MODEL_VALUE & AssignmentWizard.MAKE_SET_MODEL_VALUE) 
                    == (AssignmentWizard.MAKE_MODEL_VALUE & AssignmentWizard.MAKE_SET_MODEL_VALUE))
            {
                ordinaryValue = new Button(container, SWT.RADIO);
                ordinaryValue.setText("Ordinary assignment");
                gd = new GridData(SWT.LEFT, SWT.TOP, false, false);
                gd.horizontalSpan = 2;
                ordinaryValue.setLayoutData(gd);
                
                makeModelValue = new Button(container, SWT.RADIO);
                makeModelValue.setText("Model value");
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

                makeSetModelValues = new Button(container, SWT.RADIO);
                makeSetModelValues.setText("Set of model values");
                makeSetModelValues.addSelectionListener(new SelectionAdapter() 
                {
                    public void widgetSelected(SelectionEvent e)
                    {
                        makeSymmetricalSet.setEnabled(makeSetModelValues.getSelection());
                        typeCombo.setEnabled(makeSetModelValues.getSelection());
                        label.setEnabled(makeSetModelValues.getSelection());
                    }
                });
                gd = new GridData(SWT.LEFT, SWT.TOP, false, false);
                gd.horizontalSpan = 2;
                makeSetModelValues.setLayoutData(gd);
                
                makeSymmetricalSet = new Button(container, SWT.CHECK);
                makeSymmetricalSet.setText("Symmetrical");
                gd = new GridData(SWT.LEFT, SWT.TOP, false, false);
                gd.horizontalSpan = 2;
                gd.horizontalIndent = 10;
                makeSymmetricalSet.setLayoutData(gd);
                makeSymmetricalSet.setEnabled(makeSetModelValues.getSelection());
                
                label = new Label(container, SWT.NONE);
                label.setText("Type:");
                gd = new GridData(SWT.LEFT, SWT.TOP, false, false);
                gd.horizontalIndent = 10;
                label.setLayoutData(gd);
                label.setEnabled(makeSetModelValues.getSelection());
                
                typeCombo = new Combo(container, SWT.BORDER);
                typeCombo.add("no type");
                typeCombo.add("A");
                typeCombo.add("B");
                gd = new GridData(SWT.LEFT, SWT.TOP, false, false);
                typeCombo.setLayoutData(gd);
                typeCombo.setText("no type");
                typeCombo.setEnabled(makeSetModelValues.getSelection());
                
            }

        } else
        {

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
        if (makeModelValue != null)
        {
            this.assignment.setModelValue(makeModelValue.getSelection());
        }
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
