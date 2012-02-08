/*******************************************************************************
 * Copyright (c) 2010, 2011, 2012 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *     Microsoft Corp. - Adoptions for TLA+ Toolbox
 *******************************************************************************/
package org.lamport.tla.toolbox.ui.preference;

import java.io.File;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.KeyAdapter;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.DirectoryDialog;
import org.eclipse.swt.widgets.Table;
import org.eclipse.ui.PlatformUI;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.IParseConstants;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.ToolboxJob;

/**
 * A {@link Composite} that can be embedded inside a {@link PreferencePage}. It
 * allows to add, remove and edit directories that are used as TLA+ library
 * paths. The paths are visualized in a {@link CheckboxTableViewer}, allowing
 * users to temporarily de-select library paths.
 */
public class LibraryPathComposite {
	public static final String LIBRARY_PATH_LOCATION_PREFIX = "TLA_LIBRARY_PATH";
	public static final String LOCATION_DELIM = "|";
	public static final String STATE_DELIM = "*";
	public static final String ESCAPE_REGEX = "\\";
	
	private final LinkedList<String> fLocationList = new LinkedList<String>();
	private final PreferencePage preferencePage;

	private CheckboxTableViewer fTableViewer;
	private Button moveUpButton;
	private Button moveDownButton;

	/**
	 * Column provider for the use scan table
	 */
	class TableColumnLabelProvider extends ColumnLabelProvider {

		Image archive = null;

		/*
		 * (non-Javadoc)
		 * 
		 * @see org.eclipse.jface.viewers.BaseLabelProvider#dispose()
		 */
		public void dispose() {
			if (archive != null) {
				archive.dispose();
			}
			super.dispose();
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see
		 * org.eclipse.jface.viewers.ColumnLabelProvider#getImage(java.lang.
		 * Object)
		 */
		public Image getImage(Object element) {
			File file = new File(element.toString());
			if (file.isDirectory()) {
				return PlatformUI.getWorkbench().getSharedImages()
						.getImage(org.eclipse.ui.ISharedImages.IMG_OBJ_FOLDER);
			}
			if (archive == null) {
				ImageDescriptor image = PlatformUI.getWorkbench()
						.getEditorRegistry().getImageDescriptor(file.getName());
				archive = image.createImage();
			}
			return archive;
		}
	}

	public LibraryPathComposite(final PreferencePage preferencePage) {
		this.preferencePage = preferencePage;
		
		Composite parent = (Composite) preferencePage.getControl();

		Composite comp = SWTFactory.createComposite(parent, 2, 1,
				GridData.FILL_HORIZONTAL, 0, 0);

		SWTFactory
				.createWrapLabel(
						comp,
						"Add, remove or edit TLA+ library path locations. Unchecked locations will not be used, order reflects in the search order (Spec specific library path locations replace the general library path locations).",
						2, 250);
		SWTFactory.createVerticalSpacer(comp, 1);
		SWTFactory.createWrapLabel(comp, "&TLA+ library path locations:", 2);

		Table table = new Table(comp, SWT.FULL_SELECTION | SWT.MULTI
				| SWT.BORDER | SWT.CHECK | SWT.V_SCROLL);
		table.setLayoutData(new GridData(GridData.FILL_BOTH));
		GridData gd = (GridData) table.getLayoutData();
		gd.widthHint = 250;
		table.addKeyListener(new KeyAdapter() {
			public void keyReleased(KeyEvent e) {
				if (e.stateMask == SWT.NONE && e.keyCode == SWT.DEL) {
					removeLocation();
				}
			}
		});
		fTableViewer = new CheckboxTableViewer(table);
		fTableViewer.setLabelProvider(new TableColumnLabelProvider());
		fTableViewer.setContentProvider(new ArrayContentProvider());

		Composite bcomp = SWTFactory.createComposite(comp, 1, 1,
				GridData.FILL_VERTICAL | GridData.VERTICAL_ALIGN_BEGINNING, 0,
				0);
		moveUpButton = SWTFactory.createPushButton(bcomp,
				"&Move up", null);
		moveUpButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {
				move(true);
			}
		});
		moveDownButton = SWTFactory.createPushButton(bcomp,
				"Mo&ve down", null);
		moveDownButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {
				move(false);
			}
		});

		SWTFactory.createHorizontalSpacer(bcomp, 1);

		Button button = SWTFactory.createPushButton(bcomp,
				"Add Dire&ctory...", null);
		button.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {
				String loc = getDirectory(null);
				if (loc != null) {
					addLocation(loc);
				}
			}
		});

		final Button editbutton = SWTFactory.createPushButton(bcomp,
				"&Edit Location...", null);
		editbutton.setEnabled(false);
		editbutton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {
				edit();
			}
		});
		final Button remove = SWTFactory.createPushButton(bcomp,
				"&Remove", null);
		remove.setEnabled(false);
		remove.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {
				removeLocation();
			}
		});

		fTableViewer
				.addSelectionChangedListener(new ISelectionChangedListener() {
					public void selectionChanged(SelectionChangedEvent event) {
						IStructuredSelection selection = (IStructuredSelection) fTableViewer
								.getSelection();
						remove.setEnabled(!selection.isEmpty());
						editbutton.setEnabled(selection.size() == 1);
						
						updateEnablementMoveButtons(selection);
					}
				});
		fTableViewer.addDoubleClickListener(new IDoubleClickListener() {
			public void doubleClick(DoubleClickEvent event) {
				edit();
			}
		});
		
		performInit();
		Dialog.applyDialogFont(comp);
	}


	private void updateEnablementMoveButtons(IStructuredSelection selection) {
		moveUpButton.setEnabled(fLocationList.indexOf(selection
				.getFirstElement()) != 0);
		moveDownButton.setEnabled(fLocationList
				.indexOf(selection.getFirstElement()) != fLocationList
				.size() - 1);
	}
	
	/**
	 * Save changes to the preferences
	 */
	public void applyChanges() {
		final StringBuffer locations = new StringBuffer();
		for (Iterator<String> iterator = fLocationList.iterator(); iterator.hasNext();) {
			Object location = iterator.next();
			locations.append(location);
			locations.append(STATE_DELIM);
			locations.append(fTableViewer.getChecked(location));
			locations.append(LOCATION_DELIM);
		}
		
		if (hasLocationsChanges(locations.toString())) {
			final Spec spec = Activator.getSpecManager().getSpecLoaded();
			if (spec != null){
				if (MessageDialog
						.openQuestion(
								this.preferencePage.getShell(),
								"Locations changed",
								"TLA library path locations have changed. Reparsing is required for the changes to take effect.\nReparse now?")) {

					final Job j = new ToolboxJob("") {
						protected IStatus run(IProgressMonitor monitor) {
							ToolboxHandle.parseModule(spec.getRootFile(),
									monitor, true, true);
							return Status.OK_STATUS;
						}
					};
					j.schedule();
				} else {
                    spec.setStatus(IParseConstants.UNPARSED);
				}
			}
		}
		
		this.preferencePage.getPreferenceStore().setValue(LIBRARY_PATH_LOCATION_PREFIX, locations.toString());
	}
	
	/**
	 * Detects changes to the use scan locations
	 * @param newLocations
	 * @return if there have been changes to the use scan entries
	 */
	private boolean hasLocationsChanges(String newLocations) {
		String oldLocations = this.preferencePage.getPreferenceStore().getString(LIBRARY_PATH_LOCATION_PREFIX);
		
		if (oldLocations != null && oldLocations.equalsIgnoreCase(newLocations)) {
			return false;
		}
		
		List<String> oldCheckedElements = new ArrayList<String>();
		if (oldLocations != null && oldLocations.length() > 0) {
			String[] locations = oldLocations.split(ESCAPE_REGEX + LOCATION_DELIM);
			for (int i = 0; i < locations.length; i++) {
				String values[] = locations[i].split(ESCAPE_REGEX + STATE_DELIM);
				if (Boolean.valueOf(values[1]).booleanValue()) {
					oldCheckedElements.add(values[0]);
				}
			}			
		}
		Object[] newCheckedLocations = fTableViewer.getCheckedElements();
		if (newCheckedLocations.length != oldCheckedElements.size()) {
			return true;
		}
		for (int i = 0; i < newCheckedLocations.length; i++) {
			if (!oldCheckedElements.contains(newCheckedLocations[i])) {
				return true;
			}
		}
		return false;
	}
	
	/**
	 * Initializes the page
	 */
	public void performInit() {
		fLocationList.clear();

		String location = this.preferencePage.getPreferenceStore().getString(LIBRARY_PATH_LOCATION_PREFIX);
		
		List<String> checkedLocations = new ArrayList<String>();
		if (location != null && location.length() > 0) {
			String[] locations = location.split(ESCAPE_REGEX + LOCATION_DELIM);
			for (int i = 0; i < locations.length; i++) {
				String values[] = locations[i].split(ESCAPE_REGEX + STATE_DELIM);
				fLocationList.add(values[0]);
				if (Boolean.valueOf(values[1]).booleanValue())
					checkedLocations.add(values[0]);
			}			
			fLocationList.remove(""); //$NON-NLS-1$
		}
		fTableViewer.setInput(fLocationList);
		fTableViewer.setCheckedElements(checkedLocations.toArray(new String[checkedLocations.size()]));
		fTableViewer.refresh();
		
		this.preferencePage.setErrorMessage(null);
	}

	/**
	 * Validates that the scan are all still valid
	 */
	private void validateLocations() {
		if (fLocationList.size() > 0) {
			String loc = null;
			for (Iterator<String> iterator = fLocationList.iterator(); iterator
					.hasNext();) {
				loc = (String) iterator.next();
				if (!ResourceHelper.isValidLibraryLocation(loc)) {
					this.preferencePage.setErrorMessage("{0} is not a valid library path location");
					this.preferencePage.setValid(false);
					return;
				}
			}
		}
		this.preferencePage.setValid(true);
		this.preferencePage.setErrorMessage(null);
	}

	/**
	 * Moves entries in the table
	 * 
	 * @param moveUp
	 */
	void move(boolean moveUp) {
		final ISelection selection = fTableViewer.getSelection();
		if (selection instanceof IStructuredSelection) {
			final IStructuredSelection ss = (IStructuredSelection) selection;
			final String selected = (String) ss.getFirstElement();

			int index = fLocationList.indexOf(selected);
			if (moveUp && index - 1 >= 0) {
				fLocationList.remove(index);
				fLocationList.add(index - 1, selected);
				fTableViewer.refresh();
				updateEnablementMoveButtons(ss);
			} else if (!moveUp && index + 1 < fLocationList.size()) {
				fLocationList.remove(index);
				fLocationList.add(index + 1, selected);
				fTableViewer.refresh();
				updateEnablementMoveButtons(ss);
			}
		}
	}

	/**
	 * Allows users to select a directory with a use scan in it
	 * 
	 * @param prevLocation
	 * @return the new directory or <code>null</code> if the dialog was
	 *         cancelled
	 */
	String getDirectory(String prevLocation) {
		DirectoryDialog dialog = new DirectoryDialog(this.preferencePage.getShell());
		dialog.setMessage("Select the library path location");
		if (prevLocation != null) {
			dialog.setFilterPath(prevLocation);
		}
		return dialog.open() + File.separator;
	}

	/**
	 * Adds the given location to the table
	 * 
	 * @param location
	 */
	void addLocation(String location) {
		if (fLocationList.contains(location)) {
			return;
		}
		fLocationList.add(location);
		fTableViewer.refresh();
		fTableViewer.setChecked(location, true);
		fTableViewer.setSelection(new StructuredSelection(location));
		// do the whole pass in case you have more than one invalid location
		validateLocations();
	}

	/**
	 * Allows you to edit the location of the scan
	 */
	void edit() {
		IStructuredSelection selection = (IStructuredSelection) fTableViewer
				.getSelection();
		String location = selection.getFirstElement().toString();
		File file = new File(location);
		String newloc = null;
		if (file.isDirectory()) {
			newloc = getDirectory(location);
		}
		if (newloc != null) {
			fLocationList.remove(location);
			addLocation(newloc);
		}
	}

	/**
	 * Removes the selected locations
	 */
	void removeLocation() {
		IStructuredSelection selection = (IStructuredSelection) fTableViewer
				.getSelection();
		fLocationList.removeAll(selection.toList());
		fTableViewer.refresh();
		validateLocations();
	}
}
