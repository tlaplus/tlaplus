/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Loki de Qualer - initial API and implementation
 *   Markus Alexander Kuppe - Rewrite of ErrorViewTraceFilterDialog 
 ******************************************************************************/
package org.lamport.tla.toolbox.tool.tlc.ui.dialog;

import java.util.Arrays;
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
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;

public class ExtraModulesDialog extends Dialog {
	private CheckboxTableViewer tableViewer;
	
	private final Set<String> modules;
	private final Set<String> selection;
	
	/**
	 * @param parentShell
	 * @param modules a copy of this list will be made
	 * @param previouslySelectedModuleNames 
	 */
	public ExtraModulesDialog(final Shell parentShell, final Set<String> modules, Set<String> previouslySelectedModuleNames) {
		super(parentShell);
		
		this.modules = modules;
		this.selection = previouslySelectedModuleNames;
	}
	
	public Set<String> getSelection() {
		return selection;
	}
	
    @Override
    protected final Control createDialogArea(final Composite parent) {
    	final Composite container = (Composite) super.createDialogArea(parent);
    	GridLayout gl = new GridLayout(2, false);
    	gl.verticalSpacing = 9;
    	container.setLayout(gl);

    	
    	
    	final Label l = new Label(container, SWT.LEFT);
    	l.setText("Selected modules to be made available in trace expressions.");
    	l.setFont(JFaceResources.getFontRegistry().get(JFaceResources.DIALOG_FONT));
    	GridData gd = new GridData();
    	gd.horizontalSpan = 2;
    	l.setLayoutData(gd);
    	

    	
    	tableViewer = CheckboxTableViewer.newCheckList(container, SWT.BORDER | SWT.V_SCROLL | SWT.SINGLE);
    	tableViewer.setContentProvider(new ArrayContentProvider());
    	tableViewer.setLabelProvider(new ColumnLabelProvider() {
    		@Override
    		public String getText(final Object element) {
    			return (String) element;
    		}
    	});
    	tableViewer.setInput(modules);
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
    	
    	
        return container;
    }

    @Override
    protected void okPressed() {
    	selection.clear();
    	
		Arrays.stream(tableViewer.getCheckedElements()).forEach((element) -> selection.add((String)element));
		
        super.okPressed();
    }
    
    @Override
    protected void createButtonsForButtonBar(Composite parent) {
        createButton(parent, IDialogConstants.OK_ID, IDialogConstants.OK_LABEL, true);
    }
    
	@Override
	protected void configureShell(Shell shell) {
		super.configureShell(shell);
		shell.setText("Extra Modules");
	}
}
