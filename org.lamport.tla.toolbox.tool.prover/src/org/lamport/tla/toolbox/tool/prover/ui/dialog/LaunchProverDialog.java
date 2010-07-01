package org.lamport.tla.toolbox.tool.prover.ui.dialog;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.window.IShellProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Text;

public class LaunchProverDialog extends Dialog
{

    private List list1;
    private List list2;
    private List list3;
    /**
     * The widget where the user can enter in arbitrary command line arguments
     * for the tlapm.
     */
    private Text text;

    public LaunchProverDialog(IShellProvider parentShell)
    {
        super(parentShell);
        setBlockOnOpen(true);
    }

    protected Control createDialogArea(Composite parent)
    {

        Composite composite = new Composite(parent, SWT.NONE);
        composite.setLayoutData(new GridData());
        composite.setLayout(new GridLayout(1, true));
        Label label = new Label(composite, SWT.NONE);
        label.setText("Enter the command line arguments to launch the prover.");

        // list1 = new List(composite, SWT.NONE);
        // list2 = new List(composite, SWT.NONE);
        // list3 = new List(composite, SWT.NONE);
        text = new Text(composite, SWT.SINGLE);
        text.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
        return composite;

    }

    protected void okPressed()
    {
        /*
         * Launch the prover with the arguments given.
         */
        String command = text.getText();
        super.okPressed();
    }

}
