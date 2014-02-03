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
import org.lamport.tla.toolbox.tool.prover.ui.preference.ProverSecondPreferencePage;
import org.lamport.tla.toolbox.tool.prover.ui.util.ProverHelper;

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

    /*
     * Buttons that control what prover to use.
     */
    private Button isatool;
    private Button isacheck;
    private Button noisa;
    /**
     * Button that should be checked if
     * the user wants the PM to be launched
     * for status checking only.
     */
    private Button noProving;
    /**
     * Button that should be checked if
     * the user wants the PM to
     * be launched with the
     * {@link ITLAPMOptions#TOOLBOX} option.
     */
    private Button toolboxMode;

    /**
     * Button that should be checked if the user
     * wants the PM to be launched with
     * the option {@link ITLAPMOptions#PARANOID}.
     */
    private Button paranoid;
    /**
     * The widget for entering the number of threads.
     */
    // private Text numThreadsText;

    /**
     * Button to be checked for normal fingerprint use.
     */
    private Button fpNormal;
    /**
     * Button to be checked to erase all fingerprints and
     * start fresh.
     */
    private Button fpForgetAll;
    /**
     * Button to be checked to erase all fingerprints in
     * the currently selected region.
     */
    private Button fpForgetCurrent;

    /******************************************************
     * The following are the keys for storing             *
     * the values of the dialog when the user presses OK  *
     * so that they can be restored the next time the     *
     * user opens the dialog.                             *
     ******************************************************/
    public static final String EXTRA_OPTIONS_KEY = "extra_options";
    public static final String TOOLBOX_MODE_KEY = "toolbox_mode";
    public static final String ISATOOL_KEY = "isatool";
    public static final String STATUS_CHECK_KEY = "status_check";
    public static final String ISACHECK_KEY = "isacheck";
    public static final String NOISA_KEY = "noisa";
    public static final String PARANOID_KEY = "paranoid";
    // public static final String NUM_THREADS_KEY = "num_threads";
    public static final String FP_NORMAL_KEY = "fpnormal";
    public static final String FP_FORGET_ALL_KEY = "fpforgetall";
    public static final String FP_FORGET_CURRENT_KEY = "fpforgetcurrent";

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
        label.setText("Enter the prover options.");
        gd = new GridData();
        // spans both columns
        gd.horizontalSpan = 2;
        label.setLayoutData(gd);

        /*
         * This creates the text field for entering arbitrary
         * command line arguments. It is set to span both columns.
         */
        // extraOptionsText = new Text(topComposite, SWT.SINGLE);
        // gd = new GridData(SWT.FILL, SWT.FILL, true, true);
        // // spans both columns
        // gd.horizontalSpan = 2;
        // extraOptionsText.setLayoutData(gd);
        // extraOptionsText.setText(store.getString(EXTRA_OPTIONS_KEY));

        /*
         * Below the text field there will be two columns of options
         * that the user should select if he doesn't want to use
         * the text field. These two columns are organized into
         * a Group. Group is a subclass of composite
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
        // nonCommandLineGroup.setText("And/Or choose from this list of options for launching the prover:");

        /*
         * Now we create the left column composite and fill it
         * with widgets.
         */
        Composite left = new Composite(nonCommandLineGroup, SWT.NONE);
        gd = new GridData();
        left.setLayoutData(gd);
        left.setLayout(new GridLayout(1, true));

        /*
         * Now we create some regular old check boxes in the left column
         * for launching in toolbox mode and checking
         * status.
         */
        toolboxMode = new Button(left, SWT.CHECK);
        toolboxMode.setText(" Launch in toolbox mode");
        toolboxMode.setSelection(store.getBoolean(TOOLBOX_MODE_KEY));

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
        Group proverGroup = new Group(left, SWT.NONE);
        proverGroup.setLayout(new GridLayout(1, false));
        // sets the title of the group
        proverGroup.setText("Choose prover(s) to use:");

        isatool = new Button(proverGroup, SWT.RADIO);
        isatool.setText(" Use Isabelle only if necessary.");
        isatool.setSelection(store.getBoolean(ISATOOL_KEY));

        noProving = new Button(proverGroup, SWT.RADIO);
        noProving.setText(" No proving.");
        noProving.setSelection(store.getBoolean(STATUS_CHECK_KEY));

        isacheck = new Button(proverGroup, SWT.RADIO);
        isacheck.setText(" Check Zenon proofs with Isabelle.");
        isacheck.setSelection(store.getBoolean(ISACHECK_KEY));

        noisa = new Button(proverGroup, SWT.RADIO);
        noisa.setText(" Do not use Isabelle.");
        noisa.setSelection(store.getBoolean(NOISA_KEY));

        Group fpGroup = new Group(left, SWT.NONE);
        fpGroup.setLayout(new GridLayout(1, false));
        // sets the title of the group
        fpGroup.setText("Using previous results:");

        fpNormal = new Button(fpGroup, SWT.RADIO);
        fpNormal.setText(" Use previous results.");
        fpNormal.setSelection(store.getBoolean(FP_NORMAL_KEY));

        fpForgetAll = new Button(fpGroup, SWT.RADIO);
        fpForgetAll.setText(" Forget all previous results.");
        fpForgetAll.setSelection(store.getBoolean(FP_FORGET_ALL_KEY));

        fpForgetCurrent = new Button(fpGroup, SWT.RADIO);
        fpForgetCurrent.setText(" Forget currently selected previous results.");
        fpForgetCurrent.setSelection(store.getBoolean(FP_FORGET_CURRENT_KEY));

        /*
         * Add a listener that disables the paranoid button
         * whenever the no proving button is selected.  Unfortunately,
         * this doesn't disable when the dialog is first created and
         * "no proving" is selected.
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
         * Now we create the composite for the right column
         * and fill it with widgets.
         */
        Composite right = new Composite(nonCommandLineGroup, SWT.NONE);
        gd = new GridData();
        right.setLayoutData(gd);
        right.setLayout(new GridLayout(1, true));

        /*
         * Create a check button for paranoid proving.
         * These two widgets are contained within a composite.
         */
        paranoid = new Button(right, SWT.CHECK);
        paranoid.setText("Paranoid checking");
        paranoid.setSelection(store.getBoolean(PARANOID_KEY));
        paranoid.setEnabled(!noProving.getSelection());

        /*
         * Create the widget for entering the number of threads.
         * This widget will be a composite consisting of a Label
         * and a Text.
         */
        Composite threadsComposite = new Composite(right, SWT.NONE);
        gd = new GridData();
        threadsComposite.setLayoutData(gd);
        threadsComposite.setLayout(new GridLayout(2, false));
        // Label threadsLabel = new Label(threadsComposite, SWT.NONE);
        // threadsLabel.setText("Number of threads : ");
        // numThreadsText = new Text(threadsComposite, SWT.SINGLE);
        // numThreadsText.setText(store.getString(NUM_THREADS_KEY));

        /**
         * Field for additional command-line arguments
         */
        label = new Label(topComposite, SWT.NONE);
        label.setText("Enter additional tlapm command-line arguments.");
        gd = new GridData();
        // spans both columns
        gd.horizontalSpan = 2;
        label.setLayoutData(gd);

        extraOptionsText = new Text(topComposite, SWT.SINGLE);
        gd = new GridData(SWT.FILL, SWT.FILL, true, true);
        // spans both columns
        gd.horizontalSpan = 2;
        extraOptionsText.setLayoutData(gd);
        extraOptionsText.setText(store.getString(EXTRA_OPTIONS_KEY));

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
        store.setValue(ISATOOL_KEY, isatool.getSelection());
        store.setValue(STATUS_CHECK_KEY, noProving.getSelection());
        store.setValue(ISACHECK_KEY, isacheck.getSelection());
        store.setValue(NOISA_KEY, noisa.getSelection());
        store.setValue(PARANOID_KEY, paranoid.getSelection());
        // store.setValue(NUM_THREADS_KEY, numThreadsText.getText());
        store.setValue(FP_NORMAL_KEY, fpNormal.getSelection());
        store.setValue(FP_FORGET_ALL_KEY, fpForgetAll.getSelection());
        store.setValue(FP_FORGET_CURRENT_KEY, fpForgetCurrent.getSelection());

        /*
         * Launch the prover with the arguments given.
         * 
         * The list command will accumate a list of the arguments
         * to be given to the PM. First, we add the options from the
         * button widgets, and then we add any options the user has entered
         * in the text field at the top of the dialog. Of course, this could
         * be redundant,  so maybe there should be some check for that.
         */
        ArrayList command = new ArrayList();

        /**
         * Set option for which prover to use.  Note that the no --proving option
         * is added by the ProverJob constructor, and the "Don't use Isabelle"
         * option is indicated by the absence of a command-line option.
         */
        if (isatool.getSelection())
        {
        	// Removed by Damien. This is now the default for the PM, so we don't
        	// need to pass anything. Note that this means the "Do not use Isabelle"
        	// button is obsolete: it does the same thing as "Use Isabelle only if
        	// necessary".
            //command.add(ITLAPMOptions.ISAPROVE);
        } else if (isacheck.getSelection())
        {
            command.add(ITLAPMOptions.ISACHECK);
        }

        /*
         * Set option for fingerprint use.  Note that normal fingerprint
         * use is specified by no fingerprint option.
         */
        if (fpForgetAll.getSelection())
        {
            command.add(ITLAPMOptions.FORGET_ALL);
        } else if (fpForgetCurrent.getSelection())
        {
            command.add(ITLAPMOptions.FORGET_CURRENT);
        }
        if (paranoid.isEnabled() && paranoid.getSelection())
        {
            command.add(ITLAPMOptions.PARANOID);
        }

        /*
         * Add threads option, if there is one.
         */
        ProverHelper.setThreadsOption(command);

        /*
         * Add solver option, if there is one.
         */
        ProverHelper.setSolverOption(command);

        /*
         * This adds the extra options from the text field at the top
         * of the dialog.
         */

        /*
         * Add --safefp option, if there is one.
         */
        ProverHelper.setSafeFPOption(command);

        /* Split the string given by the user into an array of strings.
         * The string is split on every space that is not within a pair of
         * single-quote characters. Unlike the shell, we do not allow
         * backslash-escapes, and we do not trigger an error in case of
         * unclosed quote. This means there is no way to have a single-quote
         * inside an argument.
         * The parsing is done with a simple 3-state automaton.
         */
        String extraOptions = extraOptionsText.getText();
        StringBuilder argument = new StringBuilder();
        int state = 0;
        for (int j = 0; j < extraOptions.length(); j++)
        {
        	char c = extraOptions.charAt(j);
        	switch (state){
        	case 0: // "space" state: between arguments
        		if (c == ' '){
        			// skip
        		}else if (c == '\''){
        			state = 2;
        		}else{
        			argument.append (c);
        			state = 1;
        		}
        		break;
        	case 1: // "unquoted" state: inside an argument but outside quotes
        		if (c == ' '){
        			command.add(argument.toString());
        			argument.setLength(0);
        			state = 0;
         		}else if (c == '\''){
        			state = 2;
        		}else{
        			argument.append (c);
        		}
        		break;
        	case 2: // "quoted" state : inside quotes
        		if (c == '\''){
        			state = 1;
        		}else{
        			argument.append (c);
        		}
        		break;
        	}
        }
        if (state == 1 || state == 2){
        	command.add(argument.toString());
        }

        TLAEditor editor = EditorUtil.getActiveTLAEditor();
        Assert.isNotNull(editor,
                "User attempted to run general prover dialog without a tla editor active. This is a bug.");

        /*
         * This launches the prover.
         */
        ProverJob proverJob = new ProverJob(((FileEditorInput) editor.getEditorInput()).getFile(),
                ((ITextSelection) editor.getSelectionProvider().getSelection()).getOffset(), noProving.getSelection(),
                (String[]) command.toArray(new String[command.size()]), toolboxMode.getSelection());
        proverJob.setUser(true);
        proverJob.schedule();

        super.okPressed();
    }

}
