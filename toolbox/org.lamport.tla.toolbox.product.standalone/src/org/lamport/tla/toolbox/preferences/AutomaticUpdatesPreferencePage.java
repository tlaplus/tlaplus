/*******************************************************************************
 *  Copyright (c) 2007, 2016 IBM Corporation and others.
 *  All rights reserved. This program and the accompanying materials
 *  are made available under the terms of the Eclipse Public License v1.0
 *  which accompanies this distribution, and is available at
 *  http://www.eclipse.org/legal/epl-v10.html
 * 
 *  Contributors:
 *     IBM Corporation - initial API and implementation
 *     Johannes Michler <orgler@gmail.com> - Bug 321568 -  [ui] Preference for automatic-update-reminder doesn't work in multilanguage-environments
 *     Christian Georgi <christian.georgi@sap.com> - Bug 432887 - Setting to show update wizard w/o notification popup
 *     Mikael Barbero (Eclipse Foundation) - Bug 498116
 *******************************************************************************/
package org.lamport.tla.toolbox.preferences;

import java.net.URI;
import java.text.DateFormat;
import java.util.Calendar;
import java.util.Date;
import java.util.Locale;

import org.eclipse.core.runtime.IProduct;
import org.eclipse.core.runtime.Platform;
import org.eclipse.equinox.internal.p2.ui.ProvUI;
import org.eclipse.equinox.internal.p2.ui.ProvUIActivator;
import org.eclipse.equinox.internal.p2.ui.sdk.scheduler.AutomaticUpdateMessages;
import org.eclipse.equinox.internal.p2.ui.sdk.scheduler.AutomaticUpdatePlugin;
import org.eclipse.equinox.internal.p2.ui.sdk.scheduler.AutomaticUpdateScheduler;
import org.eclipse.equinox.internal.p2.ui.sdk.scheduler.AutomaticUpdatesPopup;
import org.eclipse.equinox.internal.p2.ui.sdk.scheduler.IAutomaticUpdaterHelpContextIds;
import org.eclipse.equinox.internal.p2.ui.sdk.scheduler.LastAutoCheckForUpdateMemo;
import org.eclipse.equinox.internal.p2.ui.sdk.scheduler.PreferenceConstants;
import org.eclipse.equinox.p2.repository.artifact.IArtifactRepositoryManager;
import org.eclipse.equinox.p2.repository.metadata.IMetadataRepositoryManager;
import org.eclipse.equinox.p2.ui.ProvisioningUI;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.layout.GridDataFactory;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.osgi.util.NLS;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.PlatformUI;

/**
 * Preference page for automated updates.
 * 
 * @since 3.4
 * 
 */
@SuppressWarnings("restriction")
public class AutomaticUpdatesPreferencePage extends PreferencePage implements IWorkbenchPreferencePage {

	private Button enabledCheck;
	private Button enabledBeta;
	private Button showUpdateWizard;
	private Button onStartupRadio, onFuzzyScheduleRadio;
	private Combo fuzzyRecurrenceCombo;
	private Button searchOnlyRadio, searchAndDownloadRadio;
	private Button remindOnceRadio, remindScheduleRadio;
	private Combo remindElapseCombo;
	private Group updateScheduleGroup, downloadGroup, remindGroup;

	private URI uri;
	private IMetadataRepositoryManager metadataRepositoryManager;
	private IArtifactRepositoryManager artifactRepositoryManager;

	public void init(IWorkbench workbench) {
		final ProvisioningUI ui = ProvUIActivator.getDefault().getProvisioningUI();
		uri = URI.create("http://lamport.org/tlatoolbox/ci/toolboxUpdate/");
		artifactRepositoryManager = ProvUI.getArtifactRepositoryManager(ui.getSession());
		metadataRepositoryManager = ProvUI.getMetadataRepositoryManager(ui.getSession());
	}

	protected Control createContents(Composite parent) {
		PlatformUI.getWorkbench().getHelpSystem().setHelp(parent, IAutomaticUpdaterHelpContextIds.AUTOMATIC_UPDATES_PREFERENCE_PAGE);

		Composite container = new Composite(parent, SWT.NULL);
		GridLayout layout = new GridLayout();
		layout.marginWidth = layout.marginHeight = 0;
		container.setLayout(layout);

		enabledCheck = new Button(container, SWT.CHECK);
		enabledCheck.setText(AutomaticUpdateMessages.AutomaticUpdatesPreferencePage_findUpdates);

		createSpacer(container, 1);
		
		container = new Composite(parent, SWT.NULL);
		layout = new GridLayout();
		layout.marginWidth = layout.marginHeight = 0;
		container.setLayout(layout);

		enabledBeta = new Button(container, SWT.CHECK);
		enabledBeta.setText("Receive experimental features for the TLA Toolbox.");

		createSpacer(container, 1);

		updateScheduleGroup = new Group(container, SWT.NONE);
		updateScheduleGroup.setText(NLS.bind(AutomaticUpdateMessages.AutomaticUpdatesPreferencePage_UpdateSchedule, lastCheckForUpdateDateString()));
		layout = new GridLayout();
		layout.numColumns = 3;
		updateScheduleGroup.setLayout(layout);
		GridData gd = new GridData(GridData.FILL_HORIZONTAL);
		updateScheduleGroup.setLayoutData(gd);

		onStartupRadio = new Button(updateScheduleGroup, SWT.RADIO);
		IProduct product = Platform.getProduct();
		String productName = product != null && product.getName() != null ? product.getName() : AutomaticUpdateMessages.AutomaticUpdatesPreferencePage_GenericProductName;
		onStartupRadio.setText(NLS.bind(AutomaticUpdateMessages.AutomaticUpdatesPreferencePage_findOnStart, productName));
		gd = new GridData();
		gd.horizontalSpan = 3;
		onStartupRadio.setLayoutData(gd);
		onStartupRadio.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {
				pageChanged();
			}
		});

		onFuzzyScheduleRadio = new Button(updateScheduleGroup, SWT.RADIO);
		onFuzzyScheduleRadio.setText(AutomaticUpdateMessages.AutomaticUpdatesPreferencePage_findOnSchedule);
		gd = new GridData();
		gd.horizontalSpan = 3;
		onFuzzyScheduleRadio.setLayoutData(gd);
		onFuzzyScheduleRadio.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {
				pageChanged();
			}
		});

		fuzzyRecurrenceCombo = new Combo(updateScheduleGroup, SWT.READ_ONLY);
		fuzzyRecurrenceCombo.setItems(AutomaticUpdateScheduler.FUZZY_RECURRENCE);
		gd = new GridData();
		gd.widthHint = 200;
		gd.horizontalIndent = 30;
		gd.horizontalSpan = 3;
		fuzzyRecurrenceCombo.setLayoutData(gd);

		createSpacer(container, 1);

		downloadGroup = new Group(container, SWT.NONE);
		downloadGroup.setText(AutomaticUpdateMessages.AutomaticUpdatesPreferencePage_downloadOptions);
		layout = new GridLayout();
		layout.numColumns = 3;
		downloadGroup.setLayout(layout);
		gd = new GridData(GridData.FILL_HORIZONTAL);
		downloadGroup.setLayoutData(gd);

		searchOnlyRadio = new Button(downloadGroup, SWT.RADIO);
		searchOnlyRadio.setText(AutomaticUpdateMessages.AutomaticUpdatesPreferencePage_searchAndNotify);
		gd = new GridData();
		gd.horizontalSpan = 3;
		searchOnlyRadio.setLayoutData(gd);
		searchOnlyRadio.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {
				pageChanged();
			}
		});

		searchAndDownloadRadio = new Button(downloadGroup, SWT.RADIO);
		searchAndDownloadRadio.setText(AutomaticUpdateMessages.AutomaticUpdatesPreferencePage_downloadAndNotify);
		gd = new GridData();
		gd.horizontalSpan = 3;
		searchAndDownloadRadio.setLayoutData(gd);
		searchAndDownloadRadio.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {
				pageChanged();
			}
		});

		createSpacer(container, 1);

		remindGroup = new Group(container, SWT.NONE);
		remindGroup.setText(AutomaticUpdateMessages.AutomaticUpdatesPreferencePage_RemindGroup);
		layout = new GridLayout();
		layout.numColumns = 3;
		remindGroup.setLayout(layout);
		gd = new GridData(GridData.FILL_HORIZONTAL);
		remindGroup.setLayoutData(gd);

		remindOnceRadio = new Button(remindGroup, SWT.RADIO);
		remindOnceRadio.setText(AutomaticUpdateMessages.AutomaticUpdatesPreferencePage_RemindOnce);
		gd = new GridData();
		gd.horizontalSpan = 3;
		remindOnceRadio.setLayoutData(gd);
		remindOnceRadio.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {
				pageChanged();
			}
		});

		remindScheduleRadio = new Button(remindGroup, SWT.RADIO);
		remindScheduleRadio.setText(AutomaticUpdateMessages.AutomaticUpdatesPreferencePage_RemindSchedule);
		gd = new GridData();
		gd.horizontalSpan = 3;
		remindScheduleRadio.setLayoutData(gd);
		remindScheduleRadio.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {
				pageChanged();
			}
		});

		remindElapseCombo = new Combo(remindGroup, SWT.READ_ONLY);
		remindElapseCombo.setItems(AutomaticUpdatesPopup.ELAPSED_LOCALIZED_STRINGS);

		gd = new GridData();
		gd.widthHint = 200;
		gd.horizontalIndent = 30;
		gd.horizontalSpan = 3;
		remindElapseCombo.setLayoutData(gd);

		showUpdateWizard = new Button(remindGroup, SWT.CHECK);
		showUpdateWizard.setText(AutomaticUpdateMessages.AutomaticUpdatesPreferencePage_directlyShowUpdateWizard);
		GridDataFactory.fillDefaults().span(3, 1).grab(true, false).applyTo(showUpdateWizard);

		initialize();

		enabledCheck.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {
				pageChanged();
			}
		});

		enabledBeta.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {
				pageChanged();
			}
		});
		
		Dialog.applyDialogFont(container);
		return container;
	}

	private static String lastCheckForUpdateDateString() {
		Date lastCheckDate = new LastAutoCheckForUpdateMemo(AutomaticUpdatePlugin.getDefault().getAgentLocation()).read();
		if (lastCheckDate == null) {
			return AutomaticUpdateMessages.AutomaticUpdatesPreferencePage_never;
		}

		DateFormat formatter = DateFormat.getDateTimeInstance(DateFormat.DEFAULT, DateFormat.SHORT, Locale.getDefault());
		return formatter.format(lastCheckDate);
	}

	protected void createSpacer(Composite composite, int columnSpan) {
		Label label = new Label(composite, SWT.NONE);
		GridData gd = new GridData();
		gd.horizontalSpan = columnSpan;
		label.setLayoutData(gd);
	}

	private void initialize() {
		IPreferenceStore pref = AutomaticUpdatePlugin.getDefault().getPreferenceStore();
		enabledCheck.setSelection(pref.getBoolean(PreferenceConstants.PREF_AUTO_UPDATE_ENABLED));
		enabledBeta.setSelection(artifactRepositoryManager.isEnabled(uri));
		setSchedule(pref.getString(PreferenceConstants.PREF_AUTO_UPDATE_SCHEDULE));

		fuzzyRecurrenceCombo.setText(AutomaticUpdateScheduler.FUZZY_RECURRENCE[getFuzzyRecurrence(pref, false)]);

		remindScheduleRadio.setSelection(pref.getBoolean(PreferenceConstants.PREF_REMIND_SCHEDULE));
		remindOnceRadio.setSelection(!pref.getBoolean(PreferenceConstants.PREF_REMIND_SCHEDULE));
		remindElapseCombo.setText(AutomaticUpdatesPopup.getElapsedTimeString(pref.getString(PreferenceConstants.PREF_REMIND_ELAPSED)));
		searchOnlyRadio.setSelection(!pref.getBoolean(PreferenceConstants.PREF_DOWNLOAD_ONLY));
		searchAndDownloadRadio.setSelection(pref.getBoolean(PreferenceConstants.PREF_DOWNLOAD_ONLY));
		showUpdateWizard.setSelection(pref.getBoolean(PreferenceConstants.PREF_SHOW_UPDATE_WIZARD));

		pageChanged();
	}

	private void setSchedule(String value) {
		if (value.equals(PreferenceConstants.PREF_UPDATE_ON_STARTUP)) {
			onStartupRadio.setSelection(true);
		} else {
			onFuzzyScheduleRadio.setSelection(true);
		}
	}

	void pageChanged() {
		boolean master = enabledCheck.getSelection();
		updateScheduleGroup.setEnabled(master);
		onStartupRadio.setEnabled(master);
		onFuzzyScheduleRadio.setEnabled(master);
		fuzzyRecurrenceCombo.setEnabled(master && onFuzzyScheduleRadio.getSelection());
		downloadGroup.setEnabled(master);
		searchOnlyRadio.setEnabled(master);
		searchAndDownloadRadio.setEnabled(master);
		remindGroup.setEnabled(master);
		remindScheduleRadio.setEnabled(master);
		remindOnceRadio.setEnabled(master);
		remindElapseCombo.setEnabled(master && remindScheduleRadio.getSelection());
		showUpdateWizard.setEnabled(master);
		
		boolean beta = enabledBeta.getSelection();
		artifactRepositoryManager.setEnabled(uri, beta);
		metadataRepositoryManager.setEnabled(uri, beta);
	}

	protected void performDefaults() {
		super.performDefaults();
		IPreferenceStore pref = AutomaticUpdatePlugin.getDefault().getPreferenceStore();
		enabledCheck.setSelection(pref.getDefaultBoolean(PreferenceConstants.PREF_AUTO_UPDATE_ENABLED));
		
		enabledBeta.setSelection(false);
		artifactRepositoryManager.setEnabled(uri, false);
		metadataRepositoryManager.setEnabled(uri, false);

		setSchedule(pref.getDefaultString(PreferenceConstants.PREF_AUTO_UPDATE_SCHEDULE));

		remindOnceRadio.setSelection(!pref.getDefaultBoolean(PreferenceConstants.PREF_REMIND_SCHEDULE));
		remindScheduleRadio.setSelection(pref.getDefaultBoolean(PreferenceConstants.PREF_REMIND_SCHEDULE));
		remindElapseCombo.setText(AutomaticUpdatesPopup.getElapsedTimeString(pref.getDefaultString(PreferenceConstants.PREF_REMIND_ELAPSED)));

		searchOnlyRadio.setSelection(!pref.getDefaultBoolean(PreferenceConstants.PREF_DOWNLOAD_ONLY));
		searchAndDownloadRadio.setSelection(pref.getDefaultBoolean(PreferenceConstants.PREF_DOWNLOAD_ONLY));

		showUpdateWizard.setSelection(pref.getDefaultBoolean(PreferenceConstants.PREF_SHOW_UPDATE_WIZARD));

		pageChanged();
	}

	/**
	 * Method declared on IPreferencePage. Subclasses should override
	 */
	public boolean performOk() {
		IPreferenceStore pref = AutomaticUpdatePlugin.getDefault().getPreferenceStore();
		pref.setValue(PreferenceConstants.PREF_AUTO_UPDATE_ENABLED, enabledCheck.getSelection());
		
		artifactRepositoryManager.setEnabled(uri, enabledBeta.getSelection());
		metadataRepositoryManager.setEnabled(uri, enabledBeta.getSelection());

		if (onStartupRadio.getSelection()) {
			pref.setValue(PreferenceConstants.PREF_AUTO_UPDATE_SCHEDULE, PreferenceConstants.PREF_UPDATE_ON_STARTUP);
		} else if (onFuzzyScheduleRadio.getSelection()) {
			pref.setValue(PreferenceConstants.PREF_AUTO_UPDATE_SCHEDULE, PreferenceConstants.PREF_UPDATE_ON_FUZZY_SCHEDULE);
			new LastAutoCheckForUpdateMemo(AutomaticUpdatePlugin.getDefault().getAgentLocation()).readAndStoreIfAbsent(Calendar.getInstance().getTime());
		} else {
			pref.setValue(PreferenceConstants.PREF_AUTO_UPDATE_SCHEDULE, PreferenceConstants.PREF_UPDATE_ON_SCHEDULE);
		}

		if (remindScheduleRadio.getSelection()) {
			pref.setValue(PreferenceConstants.PREF_REMIND_SCHEDULE, true);
			pref.setValue(PreferenceConstants.PREF_REMIND_ELAPSED, AutomaticUpdatesPopup.ELAPSED_VALUES[remindElapseCombo.getSelectionIndex()]);
		} else {
			pref.setValue(PreferenceConstants.PREF_REMIND_SCHEDULE, false);
		}

		pref.setValue(AutomaticUpdateScheduler.P_FUZZY_RECURRENCE, fuzzyRecurrenceCombo.getText());

		pref.setValue(PreferenceConstants.PREF_DOWNLOAD_ONLY, searchAndDownloadRadio.getSelection());

		pref.setValue(PreferenceConstants.PREF_SHOW_UPDATE_WIZARD, showUpdateWizard.getSelection());

		AutomaticUpdatePlugin.getDefault().savePreferences();
		AutomaticUpdatePlugin.getDefault().getScheduler().rescheduleUpdate();
		return true;
	}

	private int getFuzzyRecurrence(IPreferenceStore pref, boolean useDefault) {
		String day = useDefault ? pref.getDefaultString(AutomaticUpdateScheduler.P_FUZZY_RECURRENCE) : pref.getString(AutomaticUpdateScheduler.P_FUZZY_RECURRENCE);
		for (int i = 0; i < AutomaticUpdateScheduler.FUZZY_RECURRENCE.length; i++)
			if (AutomaticUpdateScheduler.FUZZY_RECURRENCE[i].equals(day))
				return i;
		return 0;
	}
}
