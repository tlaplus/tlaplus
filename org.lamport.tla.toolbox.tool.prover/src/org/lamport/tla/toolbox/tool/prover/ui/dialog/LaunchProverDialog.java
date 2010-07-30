package org.lamport.tla.toolbox.tool.prover.ui.dialog;

import java.util.ArrayList;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.window.IShellProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.tool.prover.ProverPreferenceInitializer;
import org.lamport.tla.toolbox.tool.prover.job.ITLAPMOptions;
import org.lamport.tla.toolbox.tool.prover.job.ProverJob;
import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;

/**
 * A dialog that allows the user to launch the prover
 * with a general set of options selected.
 * 
 * The method {@link #createDialogArea(Composite)} creates
 * the widgets that makes up the dialog and initializes their
 * values. The method {@link #okPressed()} does the work for
 * storing the values in the dialog and launching the prover
 * when the user presses OK.
 * 
 * The default values for the options in this dialog are set in
 * the method {@link ProverPreferenceInitializer#initializeDefaultPreferences()}.
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
    private Text extraOptionsText;
    private Button button1;
    private Button button2;
    private Button button3;
    /**
     * Button that should be checked if
     * the user wants the PM to
     * be launched with the
     * {@link ITLAPMOptions#TOOLBOX} option.
     */
    private Button toolboxMode;
    /**
     * Button that should be checked if
     * the user wants the PM to be launched
     * for status checking only.
     */
    private Button noProving;
    /**
     * Button that should be checked if the user
     * wants the PM to be launched with
     * the option {@link ITLAPMOptions#PARANOID}.
     */
    private Button paranoid;
    /**
     * The widget for entering the number of threads.
     */
    private Text numThreadsText;

    /******************************************************
     * The following are the keys for storing             *
     * the values of the dialog when the user presses OK  *
     * so that they can be restored the next time the     *
     * user opens the dialog.                             *
     ******************************************************/
    public static final String EXTRA_OPTIONS_KEY = "extra_options";
    public static final String TOOLBOX_MODE_KEY = "toolbox_mode";
    public static final String STATUS_CHECK_KEY = "status_check";
    public static final String PARANOID_KEY = "paranoid";
    public static final String NUM_THREADS_KEY = "num_threads";

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
         * We need the preference store for retrieving
         * the of the dialog widgets from the last time
         * the dialog was launched.
         */
        IPreferenceStore store = ProverUIActivator.getDefault().getPreferenceStore();

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
        extraOptionsText = new Text(topComposite, SWT.SINGLE);
        gd = new GridData(SWT.FILL, SWT.FILL, true, true);
        // spans both columns
        gd.horizontalSpan = 2;
        extraOptionsText.setLayoutData(gd);
        extraOptionsText.setText(store.getString(EXTRA_OPTIONS_KEY));

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
        nonCommandLineGroup.setText("And/Or choose from this list of options for launching the prover:");

        /*
         * Now we create the left column composite and fill it
         * with widgets.
         */
        Composite left = new Composite(nonCommandLineGroup, SWT.NONE);
        gd = new GridData();
        left.setLayoutData(gd);
        left.setLayout(new GridLayout(1, true));

        /*
         * Now we create some regular old check boxes
         * for launching in toolbox mode and checking
         * status.
         */
        toolboxMode = new Button(left, SWT.CHECK);
        toolboxMode.setText(" Launch in toolbox mode");
        toolboxMode.setSelection(store.getBoolean(TOOLBOX_MODE_KEY));
        noProving = new Button(left, SWT.CHECK);
        noProving.setText(" No proving");
        noProving.setSelection(store.getBoolean(STATUS_CHECK_KEY));
        /*
         * Add a listener that disables the paranoid button
         * whenever the no proving button is selected.
         */
        noProving.addSelectionListener(new SelectionListener() {

            public void widgetSelected(SelectionEvent e)
            {
                if (paranoid != null)
                {
                    paranoid.setEnabled(!noProving.getSelection());
                }
            }

            public void widgetDefaultSelected(SelectionEvent e)
            {
                if (paranoid != null)
                {
                    paranoid.setEnabled(!noProving.getSelection());
                }
            }
        });

        /*
         * We create a set of three mutually exclusive options.
         * Buttons are made mutually exclusive by setting
         * the style bit SWT.RADIO. I believe that for all radio buttons that
         * are immediate children of a given composite, at most one
         * is selectable at a given time. Thus, we put the three
         * mutually exclusive options in a composite. A group is a
         * subclass of composite that has a border.
         * 
         * I don't know if this is useful for prover options, but
         * just in case, I put it here.
         */
        Group mutex = new Group(left, SWT.NONE);
        mutex.setLayout(new GridLayout(1, false));
        // sets the title of the group
        mutex.setText("Choose only one of the following options:");

        button1 = new Button(mutex, SWT.RADIO);
        button1.setText("Option 1");
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

        /*
         * Create the label and check button for paranoid proving.
         * These two widgets are contained within a composite.
         */
        Composite paranoidComposite = new Composite(right, SWT.NONE);
        gd = new GridData();
        paranoidComposite.setLayoutData(gd);
        paranoidComposite.setLayout(new GridLayout(2, false));
        Label paranoidLabel = new Label(paranoidComposite, SWT.NONE);
        paranoidLabel.setText("Paranoid checking ");
        paranoid = new Button(paranoidComposite, SWT.CHECK);
        paranoid.setSelection(store.getBoolean(PARANOID_KEY));

        /*
         * Create the widget for entering the number of threads.
         * This widget will be a composite consisting of a Label
         * and a Text.
         */
        Composite threadsComposite = new Composite(right, SWT.NONE);
        gd = new GridData();
        threadsComposite.setLayoutData(gd);
        threadsComposite.setLayout(new GridLayout(2, false));
        Label threadsLabel = new Label(threadsComposite, SWT.NONE);
        threadsLabel.setText("Number of threads : ");
        numThreadsText = new Text(threadsComposite, SWT.SINGLE);
        numThreadsText.setText(store.getString(NUM_THREADS_KEY));

        return topComposite;

    }

    /**
     * This method is called by eclipse when the user presses OK.
     * The current state of the dialog is saved in preferences
     * so that it can be restored next time, and the PM is launched
     * with the selected options.
     */
    protected void okPressed()
    {
        /*
         * Save the selections in the plugin's preference store so that they can be
         * restored next time the dialog is opened.
         */
        IPreferenceStore store = ProverUIActivator.getDefault().getPreferenceStore();
        store.setValue(EXTRA_OPTIONS_KEY, extraOptionsText.getText());
        store.setValue(TOOLBOX_MODE_KEY, toolboxMode.getSelection());
        store.setValue(STATUS_CHECK_KEY, noProving.getSelection());
        store.setValue(PARANOID_KEY, paranoid.getSelection());
        store.setValue(NUM_THREADS_KEY, numThreadsText.getText());

        /*
         * Launch the prover with the arguments given.
         */
        ArrayList command = new ArrayList();

        if (paranoid.isEnabled() && paranoid.getSelection())
        {
            command.add(ITLAPMOptions.PARANOID);
        }

        if (numThreadsText.getText().trim().length() > 0)
        {
            try
            {
                int numThreads = Integer.parseInt(numThreadsText.getText().trim());
                command.add(ITLAPMOptions.THREADS);
                command.add("" + numThreads);
            } catch (NumberFormatException e)
            {
                /*
                 * If the user enters something that is not an integer
                 * in number of threads and presses OK then this will show
                 * an error dialog. By returning on this method after showing the error dialog,
                 * the user will be returned to the original launch prover dialog and
                 * will have an opportunity to correct his mistake or cancel.
                 */
                MessageDialog.openError(getShell(), "Number of threads error.",
                        "The string in the number of threads field is not an integer.");
                return;
            }
        }

        String[] extraOptions = extraOptionsText.getText().trim().split(" ");
        for (int i = 0; i < extraOptions.length; i++)
        {
            command.add(extraOptions[i]);
        }

        TLAEditor editor = EditorUtil.getActiveTLAEditor();
        Assert.isNotNull(editor,
                "User attempted to run general prover dialog without a tla editor active. This is a bug.");

        ProverJob proverJob = new ProverJob(((FileEditorInput) editor.getEditorInput()).getFile(),
                ((ITextSelection) editor.getSelectionProvider().getSelection()).getOffset(), noProving.getSelection(),
                (String[]) command.toArray(new String[command.size()]), toolboxMode.getSelection());
        proverJob.setUser(true);
        proverJob.schedule();

        super.okPressed();
    }

}
