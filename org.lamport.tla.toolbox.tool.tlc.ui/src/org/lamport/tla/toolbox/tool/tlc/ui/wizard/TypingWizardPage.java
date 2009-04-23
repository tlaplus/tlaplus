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
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;
import org.lamport.tla.toolbox.tool.tlc.model.TypedSet;

/**
 * A wizard page for typing sets of model values
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TypingWizardPage extends WizardPage
{

    private Combo typeCombo;
    private Button optionUntyped;
    private Button optionTyped;
    private Label label;

    /**
     * Constructor of the page 
     */
    protected TypingWizardPage(String action, String description)
    {
        super("TypingWizardPage");
        setTitle(action);
        setDescription(description);
        setMessage("The provided set of model values is untyped. It is recommended to use typed model values.\n" +
        		"Do you want to type the set of model values?");
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

        // untyped option
        optionUntyped = new Button(container, SWT.RADIO);
        optionUntyped.setText("Let untyped");
        gd = new GridData(SWT.LEFT, SWT.TOP, false, false);
        gd.horizontalSpan = 2;
        optionUntyped.setLayoutData(gd);

        // typed option
        optionTyped = new Button(container, SWT.RADIO);
        optionTyped.setText("Make typed:");
        optionTyped.addSelectionListener(new SelectionAdapter()
        {
            public void widgetSelected(SelectionEvent e)
            {
                typeCombo.setEnabled(optionTyped.getSelection());
                label.setEnabled(optionTyped.getSelection());
            }
        });
        gd = new GridData(SWT.LEFT, SWT.TOP, false, false);
        gd.horizontalSpan = 2;
        optionTyped.setLayoutData(gd);
        
        // label for type selection
        label = new Label(container, SWT.NONE);
        label.setText("Type:");
        gd = new GridData(SWT.LEFT, SWT.TOP, false, false);
        gd.horizontalIndent = 10;
        label.setLayoutData(gd);
        
        // type combo box
        typeCombo = new Combo(container, SWT.BORDER);

        // add letters (assumes A-Z...a-z)
        for (char i = 'A'; i < 'z'; i++)
        {
            if (Character.isLetter(i))
            {
                typeCombo.add("" + i);
            }
        }
        gd = new GridData(SWT.LEFT, SWT.TOP, false, false);
        typeCombo.setLayoutData(gd);
        
        // select the typed option
        optionTyped.setSelection(true);
        typeCombo.setText("A");
        //setUntypedOption();
        setControl(container);
    }

    public void dispose()
    {
        // evaluate the selected option and change the MVs
        // only if current page was selected 
        // if the page is not selected, it is constructed but not shown
        if (isCurrentPage() && optionTyped.getSelection()) 
        {
            // retrieve the type letter
            String type = typeCombo.getText();
            // get the MV set
            Assignment assignment = ((AssignmentWizard)getWizard()).getFormula();
            // parse the set
            TypedSet set = TypedSet.parseSet(assignment.getRight());
            // set type
            set.setType(type);
            // set the content back
            assignment.setRight(set.toString());
        }
        super.dispose();
    }
}
