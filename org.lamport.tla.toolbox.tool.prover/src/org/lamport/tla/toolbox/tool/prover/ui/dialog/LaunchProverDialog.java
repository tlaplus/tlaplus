package org.lamport.tla.toolbox.tool.prover.ui.dialog;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.window.IShellProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

/**
 * A dialog that allows the user to launch the prover
 * with a general set of options selected.
 * 
 * @author Daniel Ricketts
 *
 */
public class LaunchProverDialog extends Dialog
{

    /**
     * The widget where the user can enter in arbitrary command line arguments
     * for the tlapm.
     */
    private Text text;
    private Button button1;
    private Button button2;
    private Button button3;
    private Button button4;
    private Button button5;

    /**
     * Creates a general prover launch dialog that allows
     * the user to launch the prover with any possible set
     * of options. See {@link #open()} for opening the 
     * dialog.
     * 
     * @param parentShell
     */
    public LaunchProverDialog(IShellProvider parentShell)
    {
        super(parentShell);
        setBlockOnOpen(true);
    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.jface.dialogs.Dialog#createDialogArea(org.eclipse.swt.widgets.Composite)
     */
    protected Control createDialogArea(Composite parent)
    {

        /*
         * The creates the composite that contains all widgets
         * within the dialog. It has a grid layout for its children
         * widgets with two columns.
         */
        Composite topComposite = new Composite(parent, SWT.NONE);
        GridData gd = new GridData();
        topComposite.setLayoutData(gd);
        topComposite.setLayout(new GridLayout(2, true));

        /*
         * This creates the label for the text field for
         * entering command line arguments. It is set to span
         * both columns.
         */
        Label label = new Label(topComposite, SWT.NONE);
        label.setText("Enter the command line arguments to launch the prover.");
        gd = new GridData();
        // spans both columns
        gd.horizontalSpan = 2;
        label.setLayoutData(gd);

        /*
         * This creates the text field for entering arbitrary
         * command line arguments. It is set to span both columns.
         */
        text = new Text(topComposite, SWT.SINGLE);
        gd = new GridData(SWT.FILL, SWT.FILL, true, true);
        // spans both columns
        gd.horizontalSpan = 2;
        text.setLayoutData(gd);

        /*
         * Below the text field there will be two columns of options
         * that the user should select if he doesn't want to use
         * the text field. Both of these columns are organized into
         * their own separate group. Group is a subclass of composite
         * that provides a border. Within this group, we create a
         * composite for each column, named
         * left and right.
         */
        Group nonCommandLineGroup = new Group(topComposite, SWT.NONE);
        gd = new GridData();
        // spans both columns
        gd.horizontalSpan = 2;
        nonCommandLineGroup.setLayoutData(gd);
        nonCommandLineGroup.setLayout(new GridLayout(2, true));
        // sets the title of the group
        nonCommandLineGroup.setText("Or choose from this list of options for launching the prover:");

        /*
         * Now we create the left column composite and fill it
         * with widgets.
         */
        Composite left = new Composite(nonCommandLineGroup, SWT.NONE);
        gd = new GridData();
        left.setLayoutData(gd);
        left.setLayout(new GridLayout(1, true));

        /*
         * Now we create some regular old check boxes.
         */
        button4 = new Button(left, SWT.CHECK);
        button4.setText("Isaprove");
        button5 = new Button(left, SWT.CHECK);
        button5.setText("No proving");

        /*
         * We create a set of three mutually exclusive options.
         * Buttons are made mutually exclusive by setting
         * the style bit SWT.RADIO. I believe that for all radio buttons that
         * are immediate children of a given composite, at most one
         * is selectable at a given time. Thus, we put the three
         * mutually exclusive options in a composite. A group is a
         * subclass of composite that has a border.
         */
        Group mutex = new Group(left, SWT.NONE);
        mutex.setLayout(new GridLayout(1, false));
        // sets the title of the group
        mutex.setText("Choose only one of the following options:");

        button1 = new Button(mutex, SWT.RADIO);
        button1.setText("Isaprove");
        button2 = new Button(mutex, SWT.RADIO);
        button2.setText("Option 2");
        button3 = new Button(mutex, SWT.RADIO);
        button3.setText("Option 3");

        /*
         * Now we create the composite for the right column
         * and fill it with widgets.
         */
        Composite right = new Composite(nonCommandLineGroup, SWT.NONE);
        gd = new GridData();
        right.setLayoutData(gd);
        right.setLayout(new GridLayout(1, true));

        return topComposite;

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
