package org.lamport.tla.toolbox.tool.tlc.ui.dialog;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariable;

/**
 * The genesis of this dialog is https://github.com/tlaplus/tlaplus/issues/274 and then further modified to support
 * https://github.com/tlaplus/tlaplus/issues/360
 */
public class ErrorViewTraceFilterDialog extends Dialog {
	public enum MutatedFilter {
		NO_FILTER, CHANGED_ALL_FRAMES, CHANGED_CHANGED_FRAMES;
	}
	
	
	private static final String[] MUTATED_VARIABLE_SELECTIONS = { "Show all variables",
																  "Show only changed variables",
																  "Show only changed variables in changed frames" };
	
	
	private CheckboxTableViewer tableViewer;
	
	private final List<TLCVariable> variables;
	private final HashSet<TLCVariable> selection;
	
	private Combo mutatedVariablesCombo;
	private MutatedFilter selectedFilter;
	
	/**
	 * @param parentShell
	 * @param variableList a copy of this list will be made
	 */
	public ErrorViewTraceFilterDialog(final Shell parentShell, final List<TLCVariable> variableList) {
		super(parentShell);
		
		variables = new ArrayList<>(variableList);
		selection = new HashSet<>();
	}
	
	public Set<TLCVariable> getSelection() {
		return selection;
	}
	
	public void setSelection(final Set<TLCVariable> newSelection) {
		selection.clear();
		
		if ((newSelection == null) || (newSelection.size() == 0)) {
			return;
		}
		
		selection.addAll(newSelection);
		if (tableViewer != null) {
			tableViewer.setAllChecked(false);
			selection.stream().forEach((element) -> tableViewer.setChecked(element, true));
		}
	}
	
	public MutatedFilter getMutatedFilterSelection() {
		return selectedFilter;
	}
	
    @Override
    protected final Control createDialogArea(final Composite parent) {
    	final Composite container = (Composite) super.createDialogArea(parent);
    	GridLayout gl = new GridLayout(2, false);
    	gl.verticalSpacing = 9;
    	container.setLayout(gl);

    	
    	
    	Label l = new Label(container, SWT.LEFT);
    	l.setText("Selected variables and expressions will be hidden from the error trace.");
    	l.setFont(JFaceResources.getFontRegistry().get(JFaceResources.DIALOG_FONT));
    	GridData gd = new GridData();
    	gd.horizontalSpan = 2;
    	l.setLayoutData(gd);
    	

    	
    	tableViewer = CheckboxTableViewer.newCheckList(container, SWT.BORDER | SWT.V_SCROLL | SWT.SINGLE);
    	tableViewer.setContentProvider(new ArrayContentProvider());
    	tableViewer.setLabelProvider(new ColumnLabelProvider() {
    		@Override
    		public String getText(final Object element) {
    			return ((TLCVariable)element).getName();
    		}
    	});
    	tableViewer.setInput(variables);
		selection.stream().forEach((element) -> tableViewer.setChecked(element, true));
    	gd = new GridData();
    	gd.horizontalAlignment = SWT.FILL;
    	gd.grabExcessHorizontalSpace = true;
    	gd.minimumWidth = 333;
    	tableViewer.getTable().setLayoutData(gd);
    	
    	
    	final Composite buttonPane = new Composite(container, SWT.NONE);
    	gl = new GridLayout(1, false);
    	buttonPane.setLayout(gl);
    	
    	Button b = new Button(buttonPane, SWT.PUSH);
    	b.setText("Select All");
    	gd = new GridData();
    	gd.horizontalAlignment = SWT.FILL;
    	gd.grabExcessHorizontalSpace = true;
    	b.setLayoutData(gd);
    	b.addSelectionListener(new SelectionAdapter() {
    		@Override
    		public void widgetSelected(final SelectionEvent se) {
    			tableViewer.setAllChecked(true);
    		}
    	});
    	
    	b = new Button(buttonPane, SWT.PUSH);
    	b.setText("Deselect All");
    	gd = new GridData();
    	gd.horizontalAlignment = SWT.FILL;
    	gd.grabExcessHorizontalSpace = true;
    	b.setLayoutData(gd);
    	b.addSelectionListener(new SelectionAdapter() {
    		@Override
    		public void widgetSelected(final SelectionEvent se) {
    			tableViewer.setAllChecked(false);
    		}
    	});
    	
    	
    	final Composite mutatedVariablesComboPane = new Composite(container, SWT.NONE);
    	gd = new GridData();
    	gd.horizontalAlignment = SWT.FILL;
    	gd.grabExcessHorizontalSpace = true;
    	gd.horizontalSpan = 2;
    	mutatedVariablesComboPane.setLayoutData(gd);
    	gl = new GridLayout(2, false);
    	mutatedVariablesComboPane.setLayout(gl);
    	
    	l = new Label(mutatedVariablesComboPane, SWT.LEFT);
    	l.setText("Filter by change:");
    	l.setFont(JFaceResources.getFontRegistry().get(JFaceResources.DIALOG_FONT));
    	
    	mutatedVariablesCombo = new Combo(mutatedVariablesComboPane, SWT.READ_ONLY);
    	mutatedVariablesCombo.setItems(MUTATED_VARIABLE_SELECTIONS);
    	gd = new GridData();
    	gd.horizontalAlignment = SWT.FILL;
    	gd.grabExcessHorizontalSpace = true;
    	mutatedVariablesCombo.setLayoutData(gd);
    	mutatedVariablesCombo.setText(MUTATED_VARIABLE_SELECTIONS[0]);
    	
        return container;
    }

    @Override
    protected void okPressed() {
    	selection.clear();
    	
		Arrays.stream(tableViewer.getCheckedElements()).forEach((element) -> selection.add((TLCVariable)element));
		selectedFilter = MutatedFilter.values()[mutatedVariablesCombo.getSelectionIndex()];
		
        super.okPressed();
    }
    
    @Override
    protected void createButtonsForButtonBar(Composite parent) {
        createButton(parent, IDialogConstants.OK_ID, IDialogConstants.OK_LABEL, true);
    }
    
	@Override
	protected void configureShell(Shell shell) {
		super.configureShell(shell);
		shell.setText("Error Trace Filter");
	}
}
