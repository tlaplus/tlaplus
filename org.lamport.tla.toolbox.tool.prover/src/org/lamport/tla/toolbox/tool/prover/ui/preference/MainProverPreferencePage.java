package org.lamport.tla.toolbox.tool.prover.ui.preference;

import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.FileFieldEditor;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;
import org.lamport.tla.toolbox.tool.prover.ui.util.TLAPMExecutableLocator;

public class MainProverPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
	public static final String EXECUTABLE_LOCATION_KEY = "tlapm_filepath";
    public static final String NUM_THREADS_KEY = "num_threads";
    public static final String SOLVER_KEY = "solver";
    public static final String SAFEFP_KEY = "safefp";

    
    private TLAPMLocationEditor locationFieldEditor;
    private Label tlapmWarningLabel;
    
	public MainProverPreferencePage() {
        super(GRID);
        setPreferenceStore(ProverUIActivator.getDefault().getPreferenceStore());
    }

	public void init(final IWorkbench workbench) { }

	@Override
	protected void createFieldEditors() {
		final Composite parent = getFieldEditorParent();
		
		locationFieldEditor = new TLAPMLocationEditor(EXECUTABLE_LOCATION_KEY, "Location of tlapm", parent);
		addField(locationFieldEditor);
		tlapmWarningLabel = new Label(getFieldEditorParent(), SWT.CENTER);
        GridData gd = new GridData();
        gd.horizontalSpan = 3;  // Because this is the max of all field editor component counts
        gd.horizontalAlignment = SWT.CENTER;
        gd.grabExcessHorizontalSpace = true;
        gd.exclude = true;
        tlapmWarningLabel.setLayoutData(gd);
        tlapmWarningLabel.setForeground(tlapmWarningLabel.getDisplay().getSystemColor(SWT.COLOR_RED));
        tlapmWarningLabel.setText("The tlapm executable is not present or cannot be found.");
        tlapmWarningLabel.setVisible(false);
		
        Label lbl = new Label(getFieldEditorParent(), SWT.NONE);
        gd = new GridData();
        gd.horizontalSpan = 3;
        lbl.setLayoutData(gd);
        
        lbl = new Label(getFieldEditorParent(), SWT.NONE);
        lbl.setLayoutData(gd);
        lbl.setText("Advanced Execution Preferences");

        addField(new ThreadsFieldEditor(NUM_THREADS_KEY, "  Num. of Threads", parent));
        addField(new SolverFieldEditor(SOLVER_KEY, "  SMT Solver", parent));
        addField(new BooleanFieldEditor(SAFEFP_KEY, "Do not trust previous results from earlier versions of provers.",
        		parent));
	}
	
	@Override
	public void setVisible(final boolean flag) {
		if (flag) {
			final TLAPMExecutableLocator locator = TLAPMExecutableLocator.INSTANCE;
			
			updateLocationWarningLabelForPath(locator.getTLAPMPath());
			
			final String pathPreference = ProverUIActivator.getDefault().getPreferenceStore().getString(MainProverPreferencePage.EXECUTABLE_LOCATION_KEY);
			if ((pathPreference.trim().length() == 0) && locator.tlapmDoesExist()) {
				locationFieldEditor.setStringValue(locator.getTLAPMPath().toFile().getAbsolutePath());
			}
		}
		
		super.setVisible(flag);
	}
	
	private void updateLocationWarningLabelForPath(final IPath path) {
		if (TLAPMExecutableLocator.pathForExecutableIsUsable(path)) {
			final GridData gd = (GridData)tlapmWarningLabel.getLayoutData();
			tlapmWarningLabel.setVisible(false);
			gd.exclude = true;
			// in case there is copy-set-ing
			tlapmWarningLabel.setLayoutData(gd);
			
			tlapmWarningLabel.getParent().layout(true, true);
		} else {
			showTLAPMWarningLabel();
		}
	}
	
	private void showTLAPMWarningLabel() {
		final GridData gd = (GridData)tlapmWarningLabel.getLayoutData();
		
		tlapmWarningLabel.setVisible(true);
		gd.exclude = false;
		// in case there is copy-set-ing
		tlapmWarningLabel.setLayoutData(gd);
		
		tlapmWarningLabel.getParent().layout(true, true);
	}

	
	private static class SolverFieldEditor extends StringFieldEditor {
		public SolverFieldEditor(final String name, final String labelText, final Composite parent) {
			super(name, labelText, parent);
		}

		@Override
		public boolean doCheckState() {
			/*
			 * Changed by DD: accept any string. String value = this.getStringValue();
			 * return value.indexOf('"') == -1;
			 */
			return true;
		}
	}

	
	// this is really IntegerFieldEditor - except it allows us to have a blank as a non-specification instead of a zero
	//		or other nonsense value which conveys the wrong idea to the user.
	private static class ThreadsFieldEditor extends StringFieldEditor {
		public ThreadsFieldEditor(final String name, final String labelText, final Composite parent) {
			super(name, labelText, parent);
		}

		@Override
		public boolean doCheckState() {
			final String value = this.getStringValue().trim();
			if (value.length() == 0) {
				return true;
			}
			
			try {
				final int numThreads = Integer.parseInt(value);
				return numThreads > 0;
			} catch (NumberFormatException e) {
				return false;
			}
		}
	}
	
	
	private class TLAPMLocationEditor extends FileFieldEditor {
		public TLAPMLocationEditor(final String name, final String labelText, final Composite parent) {
			super(name, labelText, parent);
			
			setErrorMessage("Selected file must be an executable.");
		}
		
		// The superclass' implementation of checkState prevents us from getting messaged in doCheckState() in certain
		//		failure cases - so we take our cue from this.
		@Override
	    protected void showErrorMessage(final String msg) {
			showTLAPMWarningLabel();
			
			super.showErrorMessage(msg);
		}

		@Override
		public boolean doCheckState() {
			final String textFieldValue = getStringValue().trim();
			final IPath path = new Path(textFieldValue);
			
			updateLocationWarningLabelForPath(path);

			return (textFieldValue.length() == 0) || TLAPMExecutableLocator.pathForExecutableIsUsable(path);
		}
	}
}
