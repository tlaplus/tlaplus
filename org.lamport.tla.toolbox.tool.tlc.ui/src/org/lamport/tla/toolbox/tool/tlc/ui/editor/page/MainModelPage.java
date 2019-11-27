package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import java.net.Inet4Address;
import java.net.Inet6Address;
import java.net.InetAddress;
import java.net.NetworkInterface;
import java.net.SocketException;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.Enumeration;
import java.util.List;
import java.util.Set;
import java.util.Vector;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;

import javax.mail.internet.AddressException;
import javax.mail.internet.InternetAddress;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CTabFolder;
import org.eclipse.swt.custom.StackLayout;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.KeyAdapter;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Layout;
import org.eclipse.swt.widgets.Spinner;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.IMessageManager;
import org.eclipse.ui.forms.SectionPart;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.editor.IFormPage;
import org.eclipse.ui.forms.events.HyperlinkAdapter;
import org.eclipse.ui.forms.events.HyperlinkEvent;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Hyperlink;
import org.eclipse.ui.forms.widgets.Section;
import org.eclipse.ui.forms.widgets.TableWrapData;
import org.eclipse.ui.forms.widgets.TableWrapLayout;
import org.lamport.tla.toolbox.tool.tlc.launch.IConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.model.TypedSet;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.DataBindingManager;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.advanced.AdvancedTLCOptionsPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.results.EvaluateConstantExpressionPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.results.ResultPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.ValidateableConstantSectionPart;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.ValidateableSectionPart;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.ValidateableTableSectionPart;
import org.lamport.tla.toolbox.tool.tlc.ui.preference.ITLCPreferenceConstants;
import org.lamport.tla.toolbox.tool.tlc.ui.util.DirtyMarkingListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.util.SemanticHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.HelpButton;
import org.lamport.tla.toolbox.util.IHelpConstants;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.ModuleNode;
import util.TLCRuntime;

/**
 * Main model page represents information for most users <br>
 * This class is a a sub-class of the BasicFormPage and is used to represent the
 * first tab of the multi-page-editor which is used to edit the model files.
 * 
 * 
 * @author Simon Zambrovski This is the FormPage class for the Model Overview
 *         tabbed page of the model editor.
 */
public class MainModelPage extends BasicFormPage implements IConfigurationConstants, IConfigurationDefaults {
	public static final String ID = "MainModelPage";
	public static final String CUSTOM_TLC_PROFILE_PREFERENCE_VALUE = "local custom";

	static final String CLOUD_CONFIGURATION_KEY = "jclouds";

	private static final String TITLE = "Model Overview";

	private static final String INIT_NEXT_COMBO_LABEL = "Initial predicate and next-state";
	private static final String TEMPORAL_FORMULA_COMBO_LABEL = "Temporal formula";
	private static final String NO_SPEC_COMBO_LABEL = "No behavior spec";
	private static final String[] VARIABLE_BEHAVIOR_COMBO_ITEMS = { INIT_NEXT_COMBO_LABEL, TEMPORAL_FORMULA_COMBO_LABEL,
			NO_SPEC_COMBO_LABEL };
	private static final String[] NO_VARIABLE_BEHAVIOR_COMBO_ITEMS = { NO_SPEC_COMBO_LABEL };

	private static final String TLC_PROFILE_LOCAL_SEPARATOR = "\u2014\u2014 Local \u2014\u2014";
	private static final String TLC_PROFILE_REMOTE_SEPARATOR = "\u2014\u2014 Remote \u2014\u2014";
	private static final String CUSTOM_TLC_PROFILE_DISPLAY_NAME = "Custom";

	private static final String[] TLC_PROFILE_DISPLAY_NAMES;

	private static final DecimalFormat MEMORY_FORMAT = new DecimalFormat("#,###");

	static {
		final TLCConsumptionProfile[] profiles = TLCConsumptionProfile.values();
		final int size = profiles.length;

		TLC_PROFILE_DISPLAY_NAMES = new String[size + 2];
		TLC_PROFILE_DISPLAY_NAMES[0] = TLC_PROFILE_LOCAL_SEPARATOR;
		int indexIncrement = 1;
		boolean haveStartedRemoteProfiles = false;
		for (int i = 0; i < size; i++) {
			if (profiles[i].profileIsForRemoteWorkers() && !haveStartedRemoteProfiles) {
				TLC_PROFILE_DISPLAY_NAMES[i + indexIncrement] = TLC_PROFILE_REMOTE_SEPARATOR;
				haveStartedRemoteProfiles = true;
				indexIncrement++;
			}

			TLC_PROFILE_DISPLAY_NAMES[i + indexIncrement] = profiles[i].getDisplayName();
		}
	}

	static public String generateMemoryDisplayText(final int percentage, final long megabytes) {
		return percentage + "%" + " (" + MEMORY_FORMAT.format(megabytes) + " mb)";
	}

	
	private Combo behaviorCombo;
	private int previousBehaviorComboSelection;
	private SourceViewer commentsSource;

	private SourceViewer initFormulaSource;
	private SourceViewer nextFormulaSource;
	// private SourceViewer fairnessFormulaSource;
	private SourceViewer specSource;
	private Button checkDeadlockButton;

	private Combo tlcProfileCombo;
	private AtomicInteger lastSelectedTLCProfileIndex;
	private Label tlcResourceSummaryLabel;
	private Hyperlink tlcTuneHyperlink;
	// We cache this since want to reference it frequently on heap slider drag
	private AtomicBoolean currentProfileIsAdHoc;

	// We keep certain items of UI state derived from the model here and reference
	// it from the loadData of pages
	// which need not necessarily be open, and should they be opened after the model
	// editor's state has been
	// modified but not saved, would get incorrect data.
	private AtomicInteger workerThreadCount;
	private AtomicInteger heapPercentage;
	private AtomicBoolean workerValueCanBeModified;
	private AtomicBoolean heapPercentageCanBeModified;

	/**
	 * Widgets related to distributed mode configuration
	 */
	private Spinner distributedFPSetCountSpinner;
	private Spinner distributedNodesCountSpinner;
	private Text resultMailAddressText;
	private Combo networkInterfaceCombo;

	private TableViewer invariantsTable;
	private TableViewer propertiesTable;
	private TableViewer constantTable;
	
    protected HyperlinkAdapter advancedModelOptionsOpener = new HyperlinkAdapter() {
        public void linkActivated(final HyperlinkEvent he) {
        	getModelEditor().addOrShowAdvancedModelPage();
        }
    };
	protected HyperlinkAdapter advancedTLCOptionsOpener = new HyperlinkAdapter() {
		public void linkActivated(final HyperlinkEvent he) {
			getModelEditor().addOrShowAdvancedTLCOptionsPage();
		}
	};
	protected HyperlinkAdapter resultsPageOpener = new HyperlinkAdapter() {
		public void linkActivated(final HyperlinkEvent he) {
			getModelEditor().addOrShowResultsPage();
		}
	};

	/**
	 * Stacked composites for displaying options based on user selection in combo
	 * boxes
	 */
	private Composite behaviorOptions;
	private Composite distributedOptions;

	/**
	 * constructs the main model page
	 * 
	 * @param editor
	 */
	public MainModelPage(final FormEditor editor) {
		super(editor, MainModelPage.ID, MainModelPage.TITLE,
				"icons/full/model_options_" + IMAGE_TEMPLATE_TOKEN + ".png");
		helpId = IHelpConstants.MAIN_MODEL_PAGE;

		currentProfileIsAdHoc = new AtomicBoolean(false);
		workerValueCanBeModified = new AtomicBoolean(true);
		heapPercentageCanBeModified = new AtomicBoolean(true);
	}

	/**
	 * @see BasicFormPage#loadData()
	 */
	@Override
	protected void loadData() throws CoreException {
		final Model model = getModel();
		final int specType = model.getAttribute(MODEL_BEHAVIOR_SPEC_TYPE, MODEL_BEHAVIOR_TYPE_DEFAULT);

		// set up the radio buttons
		setSpecSelection(specType);

		// closed spec
		String modelSpecification = model.getAttribute(MODEL_BEHAVIOR_CLOSED_SPECIFICATION, EMPTY_STRING);
		Document closedDoc = new Document(modelSpecification);
		this.specSource.setDocument(closedDoc);

		// init
		String modelInit = model.getAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT, EMPTY_STRING);
		Document initDoc = new Document(modelInit);
		this.initFormulaSource.setDocument(initDoc);

		// next
		String modelNext = model.getAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT, EMPTY_STRING);
		Document nextDoc = new Document(modelNext);
		this.nextFormulaSource.setDocument(nextDoc);

		// fairness
		// String modelFairness =
		// model.getAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_FAIRNESS,
		// EMPTY_STRING);
		// Document fairnessDoc = new Document(modelFairness);
		// this.fairnessFormulaSource.setDocument(fairnessDoc);

		// check deadlock
		boolean checkDeadlock = model.getAttribute(MODEL_CORRECTNESS_CHECK_DEADLOCK,
				MODEL_CORRECTNESS_CHECK_DEADLOCK_DEFAULT);
		this.checkDeadlockButton.setSelection(checkDeadlock);

		// invariants
		List<String> serializedList = model.getAttribute(MODEL_CORRECTNESS_INVARIANTS, new Vector<String>());
		FormHelper.setSerializedInput(invariantsTable, serializedList);

		// properties
		serializedList = model.getAttribute(MODEL_CORRECTNESS_PROPERTIES, new Vector<String>());
		FormHelper.setSerializedInput(propertiesTable, serializedList);

		// constants from the model
		List<String> savedConstants = model.getAttribute(MODEL_PARAMETER_CONSTANTS, new Vector<String>());
		FormHelper.setSerializedInput(constantTable, savedConstants);
		if (!savedConstants.isEmpty()) {
			expandSection(SEC_WHAT_IS_THE_MODEL);
		}

		final int threadCount;
		final int memoryPercentage;
		currentProfileIsAdHoc.set(false);
        final IPreferenceStore prefStore = TLCUIActivator.getDefault().getPreferenceStore();
		if (model.hasAttribute(TLC_RESOURCES_PROFILE)) {
			final String tlcProfile = model.getAttribute(TLC_RESOURCES_PROFILE, (String) null);

			if (tlcProfile.equals(CUSTOM_TLC_PROFILE_PREFERENCE_VALUE)) {
				threadCount = model.getAttribute(LAUNCH_NUMBER_OF_WORKERS,
						prefStore.getInt(ITLCPreferenceConstants.I_TLC_DEFAULT_WORKERS_COUNT));
				final int defaultMaxHeapSize = prefStore.getInt(ITLCPreferenceConstants.I_TLC_MAXIMUM_HEAP_SIZE_DEFAULT);
				memoryPercentage = model.getAttribute(LAUNCH_MAX_HEAP_SIZE, defaultMaxHeapSize);

				setTLCProfileComboSelection(CUSTOM_TLC_PROFILE_DISPLAY_NAME);
			} else {
				final TLCConsumptionProfile profile = TLCConsumptionProfile.getProfileWithPreferenceValue(tlcProfile);

				setTLCProfileComboSelection(profile.getDisplayName());

				if (profile.profileIsForRemoteWorkers()) {
					final String configuration = profile.getConfigurationKey(); // currentProfileIsAdHoc
					final boolean isAdHoc = configuration
							.equals(TLCConsumptionProfile.REMOTE_AD_HOC.getConfigurationKey());

					currentProfileIsAdHoc.set(isAdHoc);
					moveToTopOfDistributedOptionsStack(configuration, false, isAdHoc);

					if (configuration.equals(CLOUD_CONFIGURATION_KEY)) {
						final String email = model.getAttribute(LAUNCH_DISTRIBUTED_RESULT_MAIL_ADDRESS,
								LAUNCH_DISTRIBUTED_RESULT_MAIL_ADDRESS_DEFAULT);
						resultMailAddressText.setText(email);
					}
				} else {
					moveToTopOfDistributedOptionsStack(LAUNCH_DISTRIBUTED_NO, true, true);
				}

				threadCount = profile.getWorkerThreads();
				memoryPercentage = currentProfileIsAdHoc.get()
						? model.getAttribute(LAUNCH_MAX_HEAP_SIZE, profile.getMemoryPercentage())
						: profile.getMemoryPercentage();
			}
		} else { // for pre-1.6.0 models...
			String remoteWorkers = LAUNCH_DISTRIBUTED_NO;

			try {
				remoteWorkers = model.getAttribute(LAUNCH_DISTRIBUTED, LAUNCH_DISTRIBUTED_DEFAULT);
			} catch (CoreException e) { // for very old models
				if (model.getAttribute(LAUNCH_DISTRIBUTED, false)) {
					remoteWorkers = TLCConsumptionProfile.REMOTE_AD_HOC.getConfigurationKey();
					currentProfileIsAdHoc.set(true);
				}
			}

			if (remoteWorkers.equals(LAUNCH_DISTRIBUTED_NO)) {
				moveToTopOfDistributedOptionsStack(LAUNCH_DISTRIBUTED_NO, true, true);
				threadCount = model.getAttribute(LAUNCH_NUMBER_OF_WORKERS,
						prefStore.getInt(ITLCPreferenceConstants.I_TLC_DEFAULT_WORKERS_COUNT));
				final int defaultMaxHeapSize = prefStore.getInt(ITLCPreferenceConstants.I_TLC_MAXIMUM_HEAP_SIZE_DEFAULT);
				memoryPercentage = model.getAttribute(LAUNCH_MAX_HEAP_SIZE, defaultMaxHeapSize);

				setTLCProfileComboSelection(CUSTOM_TLC_PROFILE_DISPLAY_NAME);
			} else {
				final TLCConsumptionProfile profile = TLCConsumptionProfile
						.getProfileWithPreferenceValue(remoteWorkers);
				final String configuration = profile.getConfigurationKey();
				final boolean isAdHoc = configuration.equals(TLCConsumptionProfile.REMOTE_AD_HOC.getConfigurationKey());

				currentProfileIsAdHoc.set(isAdHoc);
				moveToTopOfDistributedOptionsStack(configuration, false, isAdHoc);

				if (configuration.equals(CLOUD_CONFIGURATION_KEY)) {
					final String email = model.getAttribute(LAUNCH_DISTRIBUTED_RESULT_MAIL_ADDRESS,
							LAUNCH_DISTRIBUTED_RESULT_MAIL_ADDRESS_DEFAULT);
					resultMailAddressText.setText(email);
				}

				threadCount = 0;

				if (isAdHoc) {
					final int defaultMaxHeapSize = prefStore.getInt(ITLCPreferenceConstants.I_TLC_MAXIMUM_HEAP_SIZE_DEFAULT);
					memoryPercentage = model.getAttribute(LAUNCH_MAX_HEAP_SIZE, defaultMaxHeapSize);
				} else {
					memoryPercentage = 0;
				}

				setTLCProfileComboSelection(profile.getDisplayName());
			}
		}
		workerThreadCount = new AtomicInteger(threadCount);
		heapPercentage = new AtomicInteger(memoryPercentage);

		// distribute FPSet count
		distributedFPSetCountSpinner.setSelection(
				model.getAttribute(LAUNCH_DISTRIBUTED_FPSET_COUNT, LAUNCH_DISTRIBUTED_FPSET_COUNT_DEFAULT));

		// distribute FPSet count
		distributedNodesCountSpinner.setSelection(
				model.getAttribute(LAUNCH_DISTRIBUTED_NODES_COUNT, LAUNCH_DISTRIBUTED_NODES_COUNT_DEFAULT));

		// comments/description/notes
		String commentsStr = model.getAttribute(MODEL_COMMENTS, EMPTY_STRING);
		commentsSource.setDocument(new Document(commentsStr));
		if (!EMPTY_STRING.equals(commentsStr)) {
			expandSection(SEC_COMMENTS);
		}

		updateTLCResourcesLabel();
	}

	/**
	 * @param noSpec if false, the spec choice at index 0 of the combobox will be
	 *               chosen; in the case of the spec having no variables defined,
	 *               this will again be a no-behavior-spec
	 */
	public void setNoBehaviorSpec(final boolean noSpec) {
		if (noSpec) {
			previousBehaviorComboSelection = behaviorCombo.getSelectionIndex();
			setSpecSelection(MODEL_BEHAVIOR_TYPE_NO_SPEC);			
		} else {
			behaviorCombo.select(previousBehaviorComboSelection);
			moveToTopOfBehaviorOptionsStack(behaviorCombo.getText());
		}
		final DataBindingManager dm = getDataBindingManager();
		dm.getSection(dm.getSectionForAttribute(MODEL_BEHAVIOR_NO_SPEC)).markDirty();
		
		validatePage(false);
	}
	
	/**
	 * This switches the behavior combo to be Init-Next behavior and potentially sets the Init and Next values in the
	 * 	UI text areas.
	 * 
	 * @param initFormula if non-null, this will be set into the Init text area
	 * @param nextFormula if non-null, this will be set into the Next text area
	 */
	public void setInitNextBehavior(final String initFormula, final String nextFormula) {
		boolean setDirty = setSpecSelection(MODEL_BEHAVIOR_TYPE_SPEC_INIT_NEXT);
		
		if (initFormula != null) {
			initFormulaSource.setDocument(new Document(initFormula));
			setDirty = true;
		}
		
		if (nextFormula != null) {
			nextFormulaSource.setDocument(new Document(nextFormula));
			setDirty = true;
		}
		
		if (setDirty) {
			final DataBindingManager dm = getDataBindingManager();
			dm.getSection(dm.getSectionForAttribute(MODEL_BEHAVIOR_NO_SPEC)).markDirty();
			
			validatePage(false);
		}
	}
	
	@Override
	public void validatePage(boolean switchToErrorPage) {
		if (getManagedForm() == null) {
			return;
		}

		final DataBindingManager dm = getDataBindingManager();
		final IMessageManager mm = getManagedForm().getMessageManager();
		mm.setAutoUpdate(false);
		
		final ModelEditor modelEditor = (ModelEditor) getEditor();

		// The following comment was apparently written by Simon:
		// delete the messages
		// this is now done in validateRunnable
		// in ModelEditor
		// resetAllMessages(false);
		// validateRunnable is in ModelEditor. I believe it is executed only when
		// the user executes the Run or Validate Model command.
		// Errors that the validatePage method checks for should be cleared
		// whenever the method is called. However, calling resetAllMessages
		// seems to be the wrong way to do it because error messages from all
		// pages are reported on each page. Hence, that would require validating
		// all pages whenever any one is validated. See the
		// ModelEditor.removeErrorMessage
		// method for a further discussion of this problem.
		// Comments added by LL on 21 Mar 2013.

		// getting the root module node of the spec
		// this can be null!
		ModuleNode rootModuleNode = SemanticHelper.getRootModuleNode();

		// setup the names from the current page
		getLookupHelper().resetModelNames(this);

		// constants in the table
		List<Assignment> constants = getConstants();
		// merge constants with currently defined in the specobj, if any
		final String sectionId = dm.getSectionForAttribute(MODEL_PARAMETER_CONSTANTS);
		if (rootModuleNode != null) {
			List<Assignment> toDelete = ModelHelper.mergeConstantLists(constants,
					ModelHelper.createConstantsList(rootModuleNode));
			if (!toDelete.isEmpty()) {
				// if constants have been removed, these should be deleted from
				// the model too
				SectionPart constantSection = dm.getSection(sectionId);
				if (constantSection != null) {
					// mark the constants dirty
					constantSection.markDirty();
				}
			}
			constantTable.setInput(constants);
		}

		// The following string is used to test whether two differently-typed model
		// values appear in symmetry sets (sets of model values declared to be
		// symmetric).
		// It is set to the type of the first typed model value found in a symmetry set.
		String symmetryType = null;
		final Control widget = UIHelper.getWidget(dm.getAttributeControl(MODEL_PARAMETER_CONSTANTS));
		for (int i = 0; i < constants.size(); i++) {
			Assignment constant = (Assignment) constants.get(i);

			List<String> values = Arrays.asList(constant.getParams());
			// check parameters
			validateId(sectionId, widget, values, "param1_", "A parameter name");

			// the constant is still in the list
			String label = constant.getLabel();
			if (constant.getRight() == null || EMPTY_STRING.equals(constant.getRight())) {
				// right side of assignment undefined
				modelEditor.addErrorMessage(label, "Provide a value for constant " + label,
						this.getId(), IMessageProvider.ERROR,
						widget);
				setComplete(false);
				expandSection(sectionId);

			} else { // Following added by LL on 21 Mar 2013
				modelEditor.removeErrorMessage(label,
						widget);
				if (constant.isSetOfModelValues()) {
					TypedSet modelValuesSet = TypedSet.parseSet(constant.getRight());

					if (constant.isSymmetricalSet()) {
						if (hasLivenessProperty()) {
							modelEditor.addErrorMessage(constant.getLabel(), String.format(
									"%s declared to be symmetric while one or more temporal formulas are set to be checked.\n"
											+ "If the temporal formula is a liveness property, liveness checking might fail to find\n"
											+ "violations. The Model Checking Result page will show a warning during TLC startup if\n"
											+ "any one of the temporal formulas is a liveness property.",
									constant.getLabel()), this.getId(), IMessageProvider.INFORMATION,
									UIHelper.getWidget(dm.getAttributeControl(MODEL_PARAMETER_CONSTANTS)));
							expandSection(dm.getSectionForAttribute(MODEL_PARAMETER_CONSTANTS));
							expandSection(dm.getSectionForAttribute(MODEL_CORRECTNESS_PROPERTIES));
						}

						boolean hasTwoTypes = false; // set true if this symmetry set has two differently-typed model
						// values.
						String typeString = null; // set to the type of the first typed model value in this symmetry
						// set.
						if (modelValuesSet.hasType()) {
							typeString = modelValuesSet.getType();
						} else {
							for (int j = 0; j < modelValuesSet.getValues().length; j++) {
								String thisTypeString = TypedSet.getTypeOfId(modelValuesSet.getValues()[j]);
								if (thisTypeString != null) {
									if (typeString != null && !typeString.equals(thisTypeString)) {
										hasTwoTypes = true;
									} else {
										typeString = thisTypeString;
									}
								}
							}
						}
						if (hasTwoTypes
								|| (symmetryType != null && typeString != null && !typeString.equals(symmetryType))) {
							modelEditor.addErrorMessage(constant.getLabel(),
									"Two differently typed model values used in symmetry sets.",
									this.getId()/* constant */, IMessageProvider.ERROR,
									UIHelper.getWidget(dm.getAttributeControl(MODEL_PARAMETER_CONSTANTS)));
							setComplete(false);
							expandSection(dm.getSectionForAttribute(MODEL_PARAMETER_CONSTANTS));
						} else {
							if (typeString != null) {
								symmetryType = typeString;
							}
						}

						// symmetry can be used for only one set of model values

					}
					if (modelValuesSet.getValueCount() > 0) {
						// there were values defined
						// check if those are numbers?
						/*
						 * if (modelValuesSet.hasANumberOnlyValue()) { mm.addMessage("modelValues1",
						 * "A model value can not be an number", modelValuesSet, IMessageProvider.ERROR,
						 * constantTable.getTable()); setComplete(false); }
						 */

						List<String> mvList = modelValuesSet.getValuesAsList();
						// check list of model values
						validateUsage(sectionId, widget, mvList, "modelValues2_", "A model value",
								"Constant Assignment", true);
						// check if the values are correct ids
						validateId(sectionId, widget, mvList, "modelValues2_", "A model value");

						// get widget for model values assigned to constant
						// check if model values are config file keywords
						for (int j = 0; j < mvList.size(); j++) {
							String value = (String) mvList.get(j);
							if (SemanticHelper.isConfigFileKeyword(value)) {
								modelEditor.addErrorMessage(value,
										"The toolbox cannot handle the model value " + value + ".", this.getId(),
										IMessageProvider.ERROR, widget);
								setComplete(false);
							}
						}
					} else {
						// This made an error by LL on 15 Nov 2009
						modelEditor.addErrorMessage(label, "The set of model values should not be empty.",
								this.getId(), IMessageProvider.ERROR,
								widget);
						setComplete(false);
					}
				}
			}

			// the constant identifier is a config file keyword
			if (SemanticHelper.isConfigFileKeyword(label)) {
				modelEditor.addErrorMessage(label,
						"The toolbox cannot handle the constant identifier " + label + ".", this.getId(),
						IMessageProvider.ERROR, widget);
				setComplete(false);
			}
		}

		// iterate over the constants again, and check if the parameters are used as
		// Model Values
		for (int i = 0; i < constants.size(); i++) {
			Assignment constant = (Assignment) constants.get(i);
			List<String> values = Arrays.asList(constant.getParams());
			// check list of parameters
			validateUsage(sectionId, widget, values, "param1_", "A parameter name", "Constant Assignment",
					false);
		}

		// IP/network address correct?
		final int networkAddressIndex = this.networkInterfaceCombo.getSelectionIndex();
		if (networkAddressIndex < 0) {
			// Bogus input
			modelEditor.addErrorMessage("strangeAddress1",
					String.format(
							"Found the manually inserted master's network address %s. "
									+ "This is usually unnecessary and hints at a misconfiguration. "
									+ "Make sure your computer running the TLC master is reachable at address %s.",
							this.networkInterfaceCombo.getText(), this.networkInterfaceCombo.getText()),
					this.getId(), IMessageProvider.WARNING, networkInterfaceCombo);
			expandSection(SEC_HOW_TO_RUN);
		}

		// The following code added by LL and DR on 10 Sep 2009.
		// Reset the enabling and selection of spec type depending on the number number
		// of variables in the spec.
		// This code needs to be modified when we modify the model launcher
		// to allow the No Spec option to be selected when there are variables.
		if (rootModuleNode != null) {
			final Control errorMsgControl = UIHelper
					.getWidget(getDataBindingManager().getAttributeControl(MODEL_BEHAVIOR_NO_SPEC));
			final String errorMsgKey = MODEL_BEHAVIOR_NO_SPEC + "ErrorMsgKey";
			if (rootModuleNode.getVariableDecls().length == 0) {
				setHasVariables(false);
				modelEditor.addErrorMessage(errorMsgKey,
						"\"What is the behavior spec?\" automatically set to \"No Behavior Spec\" because spec has no declared variables.",
						this.getId(), IMessageProvider.INFORMATION, errorMsgControl);

				// set selection to the NO SPEC field
				if (!NO_SPEC_COMBO_LABEL.equals(behaviorCombo.getText())) {
					// mark dirty so that changes must be written to config file
					setSpecSelection(MODEL_BEHAVIOR_TYPE_NO_SPEC);
					dm.getSection(dm.getSectionForAttribute(MODEL_BEHAVIOR_NO_SPEC)).markDirty();

				}
			} else {
				setHasVariables(true);
				modelEditor.removeErrorMessage(errorMsgKey, errorMsgControl);

				// if there are variables, the user
				// may still want to choose no spec
				// so the selection is not changed
				//
				// if (noSpecRadio.getSelection())
				// {
				// // mark dirty so that changes must be written to config file
				// dm.getSection(dm.getSectionForAttribute(MODEL_BEHAVIOR_CLOSED_SPECIFICATION)).markDirty();
				// // set selection to the default
				// setSpecSelection(MODEL_BEHAVIOR_TYPE_DEFAULT);
				// }
			}
		}

		// This code disables or enables sections
		// depending on whether whether no spec is selected
		// or not.
		// This must occur after the preceeding code in case
		// that code changes the selection.
		final Section whatToCheckSection = dm.getSection(SEC_WHAT_TO_CHECK).getSection();
		final ResultPage rp = (ResultPage) modelEditor.findPage(ResultPage.ID);
		final EvaluateConstantExpressionPage ecep
				= (rp != null) ? (EvaluateConstantExpressionPage) modelEditor.findPage(EvaluateConstantExpressionPage.ID)
							   : null;

		final Set<Section> resultPageSections = (rp != null) ? rp.getSections(SEC_GENERAL, SEC_STATISTICS) : null;

		final String hint = " (\"What is the behavior spec?\" above has no behavior spec)";
		final String hintResults = " (\"What is the behavior spec?\" on \"Model Overview\" page has no behavior spec)";
		if (NO_SPEC_COMBO_LABEL.equals(behaviorCombo.getText())) {
			whatToCheckSection
					.setText(!whatToCheckSection.getText().endsWith(hint) ? whatToCheckSection.getText() + hint
							: whatToCheckSection.getText());
			whatToCheckSection.setExpanded(false);
			whatToCheckSection.setEnabled(false);

			if (resultPageSections != null) {
				resultPageSections.forEach((section) -> {
					section.setText(!section.getText().endsWith(hintResults) ? section.getText() + hintResults
							: section.getText());
					section.setEnabled(false);
					compensateForExpandableCompositesPoorDesign(section, false);
				});
			}
			
			if (ecep != null) {
				ecep.setNoBehaviorSpecToggleState(true);
			} else if (rp != null) {
				rp.setNoBehaviorSpecToggleState(true);
			}
		} else {
			whatToCheckSection.setText(whatToCheckSection.getText().replace(hint, ""));
			whatToCheckSection.setExpanded(true);
			whatToCheckSection.setEnabled(true);

			if (resultPageSections != null) {
				resultPageSections.forEach((section) -> {
					section.setText(section.getText().replace(hintResults, ""));
					section.setEnabled(true);
					compensateForExpandableCompositesPoorDesign(section, true);
				});
			}
			
			if (ecep != null) {
				ecep.setNoBehaviorSpecToggleState(false);
			} else if (rp != null) {
				rp.setNoBehaviorSpecToggleState(false);
			}
		}

		// The following code is not needed now because we automatically change
		// the selection to No Spec if there are no variables.
		//
		// if (selectedAttribute != null) {
		// // the user selected to use a spec
		// // check if there are variables declared
		// if (rootModuleNode != null
		// && rootModuleNode.getVariableDecls().length == 0) {
		// // no variables => install an error
		// mm.addMessage("noVariables",
		// "There were no variables declared in the root module",
		// null, IMessageProvider.ERROR, UIHelper.getWidget(dm
		// .getAttributeControl(selectedAttribute)));
		// setComplete(false);
		// expandSection(dm.getSectionForAttribute(selectedAttribute));
		// }
		// }

		// check if the selected fields are filled
		final Control initTA = UIHelper.getWidget(dm.getAttributeControl(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT));
		final Control nextTA = UIHelper.getWidget(dm.getAttributeControl(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT));
		final Control specTA = UIHelper.getWidget(dm.getAttributeControl(MODEL_BEHAVIOR_CLOSED_SPECIFICATION));
		modelEditor.removeErrorMessage("noInit", initTA);
		modelEditor.removeErrorMessage("noNext", nextTA);
		modelEditor.removeErrorMessage("noSpec", specTA);
		if (TEMPORAL_FORMULA_COMBO_LABEL.equals(behaviorCombo.getText())
				&& (specSource.getDocument().get().trim().length() == 0)) {
			modelEditor.addErrorMessage("noSpec", "The formula must be provided", this.getId(), IMessageProvider.ERROR,
					specTA);
			setComplete(false);
			expandSection(dm.getSectionForAttribute(MODEL_BEHAVIOR_CLOSED_SPECIFICATION));
		} else if (INIT_NEXT_COMBO_LABEL.equals(behaviorCombo.getText())) {
			final String init = initFormulaSource.getDocument().get().trim();
			final String next = nextFormulaSource.getDocument().get().trim();

			if (init.length() == 0) {
				modelEditor.addErrorMessage("noInit", "The Init formula must be provided", this.getId(),
						IMessageProvider.ERROR, initTA);
				setComplete(false);
				expandSection(dm.getSectionForAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT));
			}
			if (next.length() == 0) {
				modelEditor.addErrorMessage("noNext", "The Next formula must be provided", this.getId(),
						IMessageProvider.ERROR, nextTA);
				setComplete(false);
				expandSection(dm.getSectionForAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT));
			}
		}

		final Control emails = UIHelper.getWidget(dm.getAttributeControl(LAUNCH_DISTRIBUTED_RESULT_MAIL_ADDRESS));
		modelEditor.removeErrorMessage("email address invalid", emails);
		modelEditor.removeErrorMessage("email address missing", emails);
		// Verify that the user provided email address is valid and can be used to send
		// the model checking result to.
		final TLCConsumptionProfile profile = getSelectedTLCProfile();
		if ((profile != null) && CLOUD_CONFIGURATION_KEY.equals(profile.getConfigurationKey())) {
			final String text = resultMailAddressText.getText();

			try {
				InternetAddress.parse(text, true);
			} catch (AddressException exp) {
				modelEditor.addErrorMessage("email address invalid",
						"For Cloud TLC to work please enter a valid email address.", this.getId(),
						IMessageProvider.ERROR, emails);
				setComplete(false);
				expandSection(SEC_HOW_TO_RUN);
			}
			if ("".equals(text.trim())) {
				modelEditor.addErrorMessage("email address missing",
						"For Cloud TLC to work please enter an email address.", this.getId(), IMessageProvider.ERROR,
						emails);
				setComplete(false);
				expandSection(SEC_HOW_TO_RUN);
			}
		}

		mm.setAutoUpdate(true);

		super.validatePage(switchToErrorPage);
	}
	
	public boolean hasLivenessProperty() {
		return ((CheckboxTableViewer) propertiesTable).getCheckedElements().length > 0;
	}

	public boolean workerCountCanBeModified() {
		return workerValueCanBeModified.get();
	}

	public int getWorkerCount() {
		return workerThreadCount.get();
	}

	public void setWorkerCount(final int count) {
		workerThreadCount.set(count);

		setTLCProfileComboSelection(CUSTOM_TLC_PROFILE_DISPLAY_NAME);

		updateTLCResourcesLabel();
	}

	public boolean heapPercentageCanBeModified() {
		return heapPercentageCanBeModified.get();
	}

	public int getHeapPercentage() {
		return heapPercentage.get();
	}

	public void setHeapPercentage(final int percentage) {
		heapPercentage.set(percentage);

		if (!currentProfileIsAdHoc.get()) {
			setTLCProfileComboSelection(CUSTOM_TLC_PROFILE_DISPLAY_NAME);
		}

		updateTLCResourcesLabel();
	}

	/**
	 * This method is used to enable and disable UI widgets depending on the fact if
	 * the specification has variables.
	 * 
	 * @param hasVariables true if the spec contains variables
	 */
	private void setHasVariables(final boolean hasVariables) {
		String[] newItems = null;

		if (hasVariables) {
			if (behaviorCombo.indexOf(INIT_NEXT_COMBO_LABEL) == -1) {
				newItems = VARIABLE_BEHAVIOR_COMBO_ITEMS;
			}
		} else {
			if (behaviorCombo.indexOf(INIT_NEXT_COMBO_LABEL) != -1) {
				newItems = NO_VARIABLE_BEHAVIOR_COMBO_ITEMS;
			}
		}

		if (newItems != null) {
			final String currentSelection = behaviorCombo.getText();

			behaviorCombo.removeAll();
			behaviorCombo.setItems(newItems);

			final int index = behaviorCombo.indexOf(currentSelection);
			if (index != -1) {
				behaviorCombo.select(index);
			}
		}
	}

	/**
	 * This method sets the selection on the
	 * 
	 * @param selectedFormula
	 * @return true if the selection changed
	 */
	private boolean setSpecSelection(int specType) {
		int index = -1;

		switch (specType) {
			case MODEL_BEHAVIOR_TYPE_NO_SPEC:
				index = behaviorCombo.indexOf(NO_SPEC_COMBO_LABEL);
				break;
			case MODEL_BEHAVIOR_TYPE_SPEC_CLOSED:
				index = behaviorCombo.indexOf(TEMPORAL_FORMULA_COMBO_LABEL);
				break;
			case MODEL_BEHAVIOR_TYPE_SPEC_INIT_NEXT:
				index = behaviorCombo.indexOf(INIT_NEXT_COMBO_LABEL);
				break;
			default:
				throw new IllegalArgumentException("Wrong spec type, this is a bug");
		}
		
		if ((index != -1) && (index != behaviorCombo.getSelectionIndex())) {
			behaviorCombo.select(index);
			moveToTopOfBehaviorOptionsStack(behaviorCombo.getText());
			
			return true;
		}
		
		return false;
	}
	
	private int getModelConstantForSpecSelection() {
		final String selectedBehavior = behaviorCombo.getText();
		final int specType;
		
		if (TEMPORAL_FORMULA_COMBO_LABEL.equals(selectedBehavior)) {
			specType = MODEL_BEHAVIOR_TYPE_SPEC_CLOSED;
		} else if (INIT_NEXT_COMBO_LABEL.equals(selectedBehavior)) {
			specType = MODEL_BEHAVIOR_TYPE_SPEC_INIT_NEXT;
		} else if (NO_SPEC_COMBO_LABEL.equals(selectedBehavior)) {
			specType = MODEL_BEHAVIOR_TYPE_NO_SPEC;
		} else {
			specType = MODEL_BEHAVIOR_TYPE_DEFAULT;
		}
		
		return specType;
	}

	/**
	 * Save data back to model
	 */
	public void commit(boolean onSave) {
		final Model model = getModel();
		final String comments = FormHelper.trimTrailingSpaces(commentsSource.getDocument().get());
		model.setAttribute(MODEL_COMMENTS, comments);

		// TLCUIActivator.getDefault().logDebug("Main page commit");
		// closed formula
		String closedFormula = FormHelper.trimTrailingSpaces(this.specSource.getDocument().get());
		model.setAttribute(MODEL_BEHAVIOR_CLOSED_SPECIFICATION, closedFormula);

		// init formula
		String initFormula = FormHelper.trimTrailingSpaces(this.initFormulaSource.getDocument().get());
		model.setAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT, initFormula);

		// next formula
		String nextFormula = FormHelper.trimTrailingSpaces(this.nextFormulaSource.getDocument().get());
		model.setAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT, nextFormula);

		// fairness formula
		// String fairnessFormula =
		// FormHelper.trimTrailingSpaces(this.fairnessFormulaSource.getDocument().get());
		// model.setAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_FAIRNESS,
		// fairnessFormula);

		// mode
		model.setAttribute(MODEL_BEHAVIOR_SPEC_TYPE, getModelConstantForSpecSelection());

		// check deadlock
		boolean checkDeadlock = this.checkDeadlockButton.getSelection();
		model.setAttribute(MODEL_CORRECTNESS_CHECK_DEADLOCK, checkDeadlock);

		final TLCConsumptionProfile profile = getSelectedTLCProfile();
		final String profileValue = (profile != null) ? profile.getPreferenceValue()
				: CUSTOM_TLC_PROFILE_PREFERENCE_VALUE;

		model.setAttribute(TLC_RESOURCES_PROFILE, profileValue);

		model.setAttribute(LAUNCH_NUMBER_OF_WORKERS, workerThreadCount.get());
		model.setAttribute(LAUNCH_MAX_HEAP_SIZE, heapPercentage.get());

		// run in distributed mode
		if ((profile != null) && profile.profileIsForRemoteWorkers()) {
			model.setAttribute(LAUNCH_DISTRIBUTED, profile.getPreferenceValue());
		} else {
			model.setAttribute(LAUNCH_DISTRIBUTED, LAUNCH_DISTRIBUTED_NO);
		}

		String resultMailAddress = this.resultMailAddressText.getText();
		model.setAttribute(LAUNCH_DISTRIBUTED_RESULT_MAIL_ADDRESS, resultMailAddress);

		// distributed FPSet count
		model.setAttribute(LAUNCH_DISTRIBUTED_FPSET_COUNT, distributedFPSetCountSpinner.getSelection());

		// distributed FPSet count
		model.setAttribute(LAUNCH_DISTRIBUTED_NODES_COUNT, distributedNodesCountSpinner.getSelection());

		// network interface
		String iface = "";
		final int index = this.networkInterfaceCombo.getSelectionIndex();
		if (index == -1) {
			// Normally, the user selects an address from the provided list.
			// This branch handles the case where the user manually entered an
			// address. We don't verify it though.
			iface = this.networkInterfaceCombo.getText();
		} else {
			iface = this.networkInterfaceCombo.getItem(index);
		}
		model.setAttribute(LAUNCH_DISTRIBUTED_INTERFACE, iface);

		// invariants
		List<String> serializedList = FormHelper.getSerializedInput(invariantsTable);
		model.setAttribute(MODEL_CORRECTNESS_INVARIANTS, serializedList);

		// properties
		serializedList = FormHelper.getSerializedInput(propertiesTable);
		model.setAttribute(MODEL_CORRECTNESS_PROPERTIES, serializedList);

		// constants
		List<String> constants = FormHelper.getSerializedInput(constantTable);
		model.setAttribute(MODEL_PARAMETER_CONSTANTS, constants);

		// variables
		String variables = ModelHelper.createVariableList(SemanticHelper.getRootModuleNode());
		model.setAttribute(MODEL_BEHAVIOR_VARS, variables);

		super.commit(onSave);
	}

	@SuppressWarnings("unchecked")
	public List<Assignment> getConstants() {
		final List<Assignment> constants = (List<Assignment>) constantTable.getInput();
		if (constants == null) {
			return new ArrayList<>();
		}
		return constants;
	}
	
	/**
	 * Creates the UI This method is called to create the widgets and arrange them
	 * on the page
	 * 
	 * Its helpful to know what the standard SWT widgets look like. Pictures can be
	 * found at http://www.eclipse.org/swt/widgets/
	 * 
	 * Layouts are used throughout this method. A good explanation of layouts is
	 * given in the article
	 * http://www.eclipse.org/articles/article.php?file=Article-Understanding-Layouts/index.html
	 */
	@Override
	protected void createBodyContent(IManagedForm managedForm) {
		DataBindingManager dm = getDataBindingManager();
		int sectionFlags = Section.TITLE_BAR | Section.DESCRIPTION | Section.TREE_NODE;
		FormToolkit toolkit = managedForm.getToolkit();
		Composite body = managedForm.getForm().getBody();

		GridLayout gl;
		GridData gd;
		TableWrapData twd;

		Section section;

		installTopMargin(body);

		TableWrapLayout twl = new TableWrapLayout();
		twl.leftMargin = 0;
		twl.rightMargin = 0;
		twl.numColumns = 2;
		body.setLayout(twl);

		/*
		 * Comments/notes section spanning two columns
		 */

		section = FormHelper.createSectionComposite(body, "Model description", "", toolkit, sectionFlags,
				getExpansionListener());
		twd = new TableWrapData();
		twd.colspan = 2;
		twd.grabHorizontal = true;
		twd.align = TableWrapData.FILL;
		section.setLayoutData(twd);

		// No need for a ValidatableSectionPart for the model description as there is
		// nothing to validate when the free-form text gets changed. The model
		// validation can be expensive especially when re-executed over and over again
		// on every keystroke.
		final SectionPart commentsPart = new SectionPart(section);
        getDataBindingManager().bindSection(commentsPart, SEC_COMMENTS, getId());
		managedForm.addPart(commentsPart);
		final DirtyMarkingListener commentsListener = new DirtyMarkingListener(commentsPart, true);

		final Composite commentsArea = (Composite) section.getClient();
		commentsArea.setLayout(new TableWrapLayout());

		commentsSource = FormHelper.createFormsSourceViewer(toolkit, commentsArea, SWT.V_SCROLL | SWT.WRAP);
		// layout of the source viewer
		twd = new TableWrapData(TableWrapData.FILL_GRAB);
		twd.heightHint = 60;
		commentsSource.addTextListener(commentsListener);
		commentsSource.getTextWidget().setLayoutData(twd);
		commentsSource.getTextWidget().addFocusListener(focusListener);
		toolkit.paintBordersFor(commentsArea);

		dm.bindAttribute(MODEL_COMMENTS, commentsSource, commentsPart);

		

		Composite linkLineComposite = new Composite(body, SWT.NONE);
		twd = new TableWrapData();
		twd.colspan = 2;
		twd.grabHorizontal = true;
		twd.align = TableWrapData.RIGHT;
		linkLineComposite.setLayoutData(twd);
		linkLineComposite.setBackground(body.getDisplay().getSystemColor(SWT.COLOR_WHITE));
		gl = new GridLayout(1, false);
		gl.marginWidth = 0;
		gl.marginRight = 36;
		gl.horizontalSpacing = 0;
		linkLineComposite.setLayout(gl);
		Hyperlink hyper = toolkit.createHyperlink(linkLineComposite, "Additional Spec Options", SWT.NONE);
		hyper.addHyperlinkListener(advancedModelOptionsOpener);
		Font baseFont = JFaceResources.getFontRegistry().getBold(JFaceResources.DIALOG_FONT);
		FontData[] baseFD = baseFont.getFontData();
		FontData biggerLinkFD = new FontData(baseFD[0].getName(), baseFD[0].getHeight() + 1, baseFD[0].getStyle());
		Font biggerLinkFont = new Font(body.getDisplay(), biggerLinkFD);
		hyper.setFont(biggerLinkFont);

		
		/*
		 * Because the two Composite objects `left' and `right' are added to the object
		 * `body' in this order, `left' is displayed to the left of `right'.
		 */
		// left
		final Composite left = toolkit.createComposite(body);
		gl = new GridLayout(1, false);
		gl.marginHeight = 0;
		gl.marginWidth = 0;
		left.setLayout(gl);
		twd = new TableWrapData(TableWrapData.FILL_GRAB);
		twd.grabHorizontal = true;
		left.setLayoutData(twd);

		// right
		final Composite right = toolkit.createComposite(body);
		gl = new GridLayout(1, false);
		gl.marginHeight = 0;
		gl.marginWidth = 0;
		right.setLayout(gl);
		twd = new TableWrapData(TableWrapData.FILL_GRAB);
		twd.grabHorizontal = true;
		right.setLayoutData(twd);

		// ------------------------------------------
		// what is the spec

		section = FormHelper.createSectionComposite(left, "What is the behavior spec?", "", toolkit,
				sectionFlags | Section.EXPANDED, getExpansionListener());
		// only grab horizontal space
		gd = new GridData();
		gd.horizontalAlignment = SWT.FILL;
		gd.grabExcessHorizontalSpace = true;
		gd.horizontalIndent = 0;
		gd.verticalIndent = 0;
		section.setLayoutData(gd);

		Composite behaviorArea = (Composite) section.getClient();
		behaviorArea.setLayout(new GridLayout(1, false));

		ValidateableSectionPart behaviorPart = new ValidateableSectionPart(section, this, SEC_WHAT_IS_THE_SPEC);
		managedForm.addPart(behaviorPart);
		DirtyMarkingListener whatIsTheSpecListener = new DirtyMarkingListener(behaviorPart, true);

		behaviorCombo = new Combo(behaviorArea, SWT.READ_ONLY);
		behaviorCombo.setItems(VARIABLE_BEHAVIOR_COMBO_ITEMS);
		behaviorCombo.addFocusListener(focusListener);
		behaviorCombo.addSelectionListener(whatIsTheSpecListener);
		behaviorCombo.addSelectionListener(new SelectionListener() {
			public void widgetSelected(final SelectionEvent se) {
				moveToTopOfBehaviorOptionsStack(behaviorCombo.getText());
			}

			public void widgetDefaultSelected(final SelectionEvent se) { }
		});
		gd = new GridData();
		gd.horizontalAlignment = SWT.FILL;
		gd.grabExcessHorizontalSpace = true;
		behaviorCombo.setLayoutData(gd);
		dm.bindAttribute(MODEL_BEHAVIOR_NO_SPEC, behaviorCombo, behaviorPart);

		behaviorOptions = new Composite(behaviorArea, SWT.NONE);
		StackLayout stackLayout = new StackLayout();
		behaviorOptions.setLayout(stackLayout);

		final Composite noSpecComposite = new Composite(behaviorOptions, SWT.NONE);
		behaviorOptions.setData(NO_SPEC_COMBO_LABEL, noSpecComposite);
		gd = new GridData();
		gd.horizontalAlignment = SWT.FILL;
		gd.grabExcessHorizontalSpace = true;
		gd.minimumHeight = 1;
		behaviorOptions.setLayoutData(gd);
		stackLayout.topControl = noSpecComposite;

		// split formula option
		final Composite initNextComposite = new Composite(behaviorOptions, SWT.NONE);
		behaviorOptions.setData(INIT_NEXT_COMBO_LABEL, initNextComposite);
		initNextComposite.setLayout(new GridLayout(2, false));
		gd = new GridData();
		gd.horizontalAlignment = SWT.FILL;
		gd.grabExcessHorizontalSpace = true;
		initNextComposite.setLayoutData(gd);

		// init
		toolkit.createLabel(initNextComposite, "Init:");
		initFormulaSource = FormHelper.createFormsSourceViewer(toolkit, initNextComposite,
				SWT.NONE | SWT.MULTI | SWT.V_SCROLL | SWT.BORDER);
		gd = new GridData();
		gd.horizontalAlignment = SWT.FILL;
		gd.grabExcessHorizontalSpace = true;
		gd.heightHint = 48;
		StyledText st = initFormulaSource.getTextWidget();
		st.setLayoutData(gd);
		st.addModifyListener(whatIsTheSpecListener);
		st.addFocusListener(focusListener);
		st.addTraverseListener((event) -> {
			event.doit = true;
		});
		dm.bindAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT, initFormulaSource, behaviorPart);

		// next
		toolkit.createLabel(initNextComposite, "Next:");
		nextFormulaSource = FormHelper.createFormsSourceViewer(toolkit, initNextComposite,
				SWT.NONE | SWT.MULTI | SWT.V_SCROLL | SWT.BORDER);
		gd = new GridData();
		gd.horizontalAlignment = SWT.FILL;
		gd.grabExcessHorizontalSpace = true;
		gd.heightHint = 48;
		st = nextFormulaSource.getTextWidget();
		st.setLayoutData(gd);
		st.addModifyListener(whatIsTheSpecListener);
		st.addFocusListener(focusListener);
		st.addTraverseListener((event) -> {
			event.doit = true;
		});
		dm.bindAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT, nextFormulaSource, behaviorPart);

		// fairness
		// toolkit.createLabel(behaviorArea, "Fairness:");
		// fairnessFormulaSource = FormHelper.createSourceViewer(toolkit,
		// behaviorArea, SWT.NONE | SWT.SINGLE);
		// gd = new GridData(GridData.FILL_HORIZONTAL);
		// gd.heightHint = 18;
		// fairnessFormulaSource.getTextWidget().setLayoutData(gd);
		// fairnessFormulaSource.getTextWidget().addModifyListener(whatIsTheSpecListener);
		// fairnessFormulaSource.getTextWidget().addModifyListener(widgetActivatingListener);
		// dm.bindAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_FAIRNESS,
		// fairnessFormulaSource, behaviorPart);

		// closed formula option
		final Composite temporalFormulaComposite = new Composite(behaviorOptions, SWT.NONE);
		behaviorOptions.setData(TEMPORAL_FORMULA_COMBO_LABEL, temporalFormulaComposite);
		temporalFormulaComposite.setLayout(new GridLayout(1, true));
		gd = new GridData();
		gd.horizontalAlignment = SWT.FILL;
		gd.grabExcessHorizontalSpace = true;
		temporalFormulaComposite.setLayoutData(gd);

		specSource = FormHelper.createFormsSourceViewer(toolkit, temporalFormulaComposite, SWT.V_SCROLL | SWT.BORDER);
		gd = new GridData();
		gd.horizontalAlignment = SWT.FILL;
		gd.verticalAlignment = SWT.FILL;
		gd.grabExcessHorizontalSpace = true;
		gd.grabExcessVerticalSpace = true;
		gd.minimumHeight = 55;
		specSource.getTextWidget().setLayoutData(gd);
		specSource.getTextWidget().addModifyListener(whatIsTheSpecListener);
		dm.bindAttribute(MODEL_BEHAVIOR_CLOSED_SPECIFICATION, specSource, behaviorPart);

		// ------------------------------------------
		// what to check
		section = FormHelper.createSectionComposite(body, "What to check?", "", toolkit,
				(sectionFlags & ~Section.DESCRIPTION | Section.EXPANDED), getExpansionListener());
		// only grab horizontal space
		twd = new TableWrapData();
		twd.colspan = 2;
		twd.grabHorizontal = true;
		twd.align = TableWrapData.FILL;
		section.setLayoutData(twd);

		Composite toBeCheckedArea = (Composite) section.getClient();
		gl = new GridLayout(1, false);
		gl.verticalSpacing = 0;
		toBeCheckedArea.setLayout(gl);

		checkDeadlockButton = toolkit.createButton(toBeCheckedArea, "Deadlock", SWT.CHECK);

		ValidateableSectionPart toBeCheckedPart = new ValidateableSectionPart(section, this, SEC_WHAT_TO_CHECK);
		managedForm.addPart(toBeCheckedPart);
		DirtyMarkingListener whatToCheckListener = new DirtyMarkingListener(toBeCheckedPart, true);
		checkDeadlockButton.addSelectionListener(whatToCheckListener);

		// Invariants
		ValidateableTableSectionPart invariantsPart = new ValidateableTableSectionPart(toBeCheckedArea, "Invariants",
				"Formulas true in every reachable state.", toolkit, sectionFlags, this, SEC_WHAT_TO_CHECK_INVARIANTS);
		managedForm.addPart(invariantsPart);
		invariantsTable = invariantsPart.getTableViewer();
		dm.bindAttribute(MODEL_CORRECTNESS_INVARIANTS, invariantsTable, invariantsPart);

		// Properties
		ValidateableTableSectionPart propertiesPart = new ValidateableTableSectionPart(toBeCheckedArea, "Properties",
				"Temporal formulas true for every possible behavior.", toolkit, sectionFlags, this,
				SEC_WHAT_TO_CHECK_PROPERTIES);
		managedForm.addPart(propertiesPart);
		propertiesTable = propertiesPart.getTableViewer();
		dm.bindAttribute(MODEL_CORRECTNESS_PROPERTIES, propertiesTable, propertiesPart);

		// ------------------------------------------
		// what is the model

		// Constants
		ValidateableConstantSectionPart constantsPart = new ValidateableConstantSectionPart(right, "What is the model?",
				"Specify the values of declared constants.", toolkit, sectionFlags, this, SEC_WHAT_IS_THE_MODEL);
		gd = new GridData(GridData.FILL_HORIZONTAL);
		gd.horizontalIndent = 0;
		gd.verticalIndent = 0;
		constantsPart.getSection().setLayoutData(gd);
		managedForm.addPart(constantsPart);
		constantTable = constantsPart.getTableViewer();
		dm.bindAttribute(MODEL_PARAMETER_CONSTANTS, constantTable, constantsPart);
		

		linkLineComposite = new Composite(body, SWT.NONE);
		twd = new TableWrapData();
		twd.colspan = 2;
		twd.grabHorizontal = true;
		twd.align = TableWrapData.RIGHT;
		linkLineComposite.setLayoutData(twd);
		linkLineComposite.setBackground(body.getDisplay().getSystemColor(SWT.COLOR_WHITE));
		gl = new GridLayout(1, false);
		gl.marginWidth = 0;
		gl.marginRight = 36;
		gl.horizontalSpacing = 0;
		linkLineComposite.setLayout(gl);
		hyper = toolkit.createHyperlink(linkLineComposite, "Additional TLC Options", SWT.NONE);
		hyper.addHyperlinkListener(advancedTLCOptionsOpener);
		hyper.setFont(biggerLinkFont);

		// ------------------------------------------
		// run tab
		section = FormHelper.createSectionComposite(body, "How to run?", "", toolkit, sectionFlags,
				getExpansionListener());
		twd = new TableWrapData();
		twd.colspan = 2;
		twd.grabHorizontal = true;
		twd.align = TableWrapData.FILL;
		section.setLayoutData(twd);

		final Composite howToRunArea = (Composite) section.getClient();
		gl = new GridLayout(2, false);
		gl.marginWidth = 0;
		gl.verticalSpacing = 2;
		howToRunArea.setLayout(gl);

		final ValidateableSectionPart howToRunPart = new ValidateableSectionPart(section, this, SEC_HOW_TO_RUN);
		managedForm.addPart(howToRunPart);

		final DirtyMarkingListener howToRunListener = new DirtyMarkingListener(howToRunPart, true);

		toolkit.createLabel(howToRunArea, "System resources dedicated to TLC:");

		tlcProfileCombo = new Combo(howToRunArea, SWT.READ_ONLY);
		tlcProfileCombo.setItems(TLC_PROFILE_DISPLAY_NAMES);
		tlcProfileCombo.addSelectionListener(howToRunListener);
		tlcProfileCombo.addSelectionListener(new SelectionListener() {
			public void widgetSelected(final SelectionEvent se) {
				final String selectedText = tlcProfileCombo.getText();
				final boolean needReset = TLC_PROFILE_LOCAL_SEPARATOR.equals(selectedText)
						|| TLC_PROFILE_REMOTE_SEPARATOR.equals(selectedText);

				if (needReset) {
					tlcProfileCombo.select(lastSelectedTLCProfileIndex.get());
				} else {
					final TLCConsumptionProfile profile = TLCConsumptionProfile.getProfileWithDisplayName(selectedText);

					lastSelectedTLCProfileIndex.set(tlcProfileCombo.getSelectionIndex());

					currentProfileIsAdHoc.set(false);
					if (profile != null) {
						workerThreadCount.set(profile.getWorkerThreads());
						heapPercentage.set(profile.getMemoryPercentage());

						final IFormPage iep = getEditor().findPage(AdvancedTLCOptionsPage.ID);
						if (iep != null) {
							((AdvancedTLCOptionsPage) iep).updateWorkersAndMemory(profile.getWorkerThreads(),
									profile.getMemoryPercentage());
						}

						removeCustomTLCProfileComboItemIfPresent();

						if (profile.profileIsForRemoteWorkers()) {
							final String configuration = profile.getConfigurationKey();
							final boolean isAdHoc = configuration
									.equals(TLCConsumptionProfile.REMOTE_AD_HOC.getConfigurationKey());

							moveToTopOfDistributedOptionsStack(configuration, false, isAdHoc);
							if (isAdHoc) {
								currentProfileIsAdHoc.set(true);
								clearEmailErrors();
							}
						} else {
							moveToTopOfDistributedOptionsStack(LAUNCH_DISTRIBUTED_NO, true, true);
							clearEmailErrors();
						}
					} else {
						moveToTopOfDistributedOptionsStack(LAUNCH_DISTRIBUTED_NO, true, true);
						clearEmailErrors();
					}
				}

				updateTLCResourcesLabel();
			}

			public void widgetDefaultSelected(final SelectionEvent se) {
			}
		});
		gd = new GridData();
		gd.horizontalIndent = 30;
		gd.grabExcessHorizontalSpace = true;
		gd.horizontalAlignment = SWT.FILL;
		tlcProfileCombo.setLayoutData(gd);
		lastSelectedTLCProfileIndex = new AtomicInteger(tlcProfileCombo.getSelectionIndex());

		tlcResourceSummaryLabel = toolkit.createLabel(howToRunArea, "");
		tlcResourceSummaryLabel.setFont(JFaceResources.getFontRegistry().getBold(JFaceResources.DIALOG_FONT));
		gd = new GridData();
		gd.horizontalSpan = 2;
		gd.grabExcessHorizontalSpace = true;
		gd.horizontalAlignment = SWT.CENTER;
		tlcResourceSummaryLabel.setLayoutData(gd);

		linkLineComposite = new Composite(howToRunArea, SWT.NONE);
		gd = new GridData();
		gd.horizontalSpan = 2;
		gd.grabExcessHorizontalSpace = true;
		gd.horizontalAlignment = SWT.CENTER;
		linkLineComposite.setLayoutData(gd);
		gl = new GridLayout(1, false);
		gl.marginWidth = 0;
		gl.horizontalSpacing = 0;
		linkLineComposite.setLayout(gl);
		tlcTuneHyperlink = toolkit.createHyperlink(linkLineComposite, "Tune these parameters and set defaults", SWT.NONE);
		tlcTuneHyperlink.addHyperlinkListener(advancedTLCOptionsOpener);
		baseFont = JFaceResources.getFont(JFaceResources.DIALOG_FONT);
		baseFD = baseFont.getFontData();
		final FontData smaller = new FontData(baseFD[0].getName(), baseFD[0].getHeight() - 2, baseFD[0].getStyle());
		tlcTuneHyperlink.setFont(new Font(body.getDisplay(), smaller));


		/*
		 * Distribution. Help button added by LL on 17 Jan 2013
		 */
		distributedOptions = new Composite(howToRunArea, SWT.NONE);
		stackLayout = new StackLayout();
		distributedOptions.setLayout(stackLayout);

		gd = new GridData();
		gd.horizontalSpan = 2;
		gd.horizontalAlignment = SWT.FILL;
		gd.grabExcessHorizontalSpace = true;
		distributedOptions.setLayoutData(gd);

		// No distribution has no options
		final Composite offComposite = new Composite(distributedOptions, SWT.NONE);
		distributedOptions.setData(LAUNCH_DISTRIBUTED_NO, offComposite);
		stackLayout.topControl = offComposite;

		/*
		 * Composite wrapping number of distributed FPSet and iface when ad hoc selected
		 */
		final Composite adHocOptions = new Composite(distributedOptions, SWT.NONE);
		gl = new GridLayout(2, false);
		gl.marginWidth = 0;
		adHocOptions.setLayout(gl);
		distributedOptions.setData(TLCConsumptionProfile.REMOTE_AD_HOC.getConfigurationKey(), adHocOptions);

		Button helpButton = HelpButton.helpButton(adHocOptions, "model/distributed-mode.html");
		gd = new GridData();
		gd.horizontalSpan = 2;
		gd.horizontalAlignment = SWT.END;
		helpButton.setLayoutData(gd);

		/*
		 * Server interface/hostname (This text shows the hostname detected by the
		 * Toolbox under which TLCServer will listen)
		 */

		// label
		toolkit.createLabel(adHocOptions, "Master's network address:");

		// field
		networkInterfaceCombo = new Combo(adHocOptions, SWT.NONE);
		networkInterfaceCombo.addSelectionListener(howToRunListener);
		networkInterfaceCombo.addFocusListener(focusListener);
		gd = new GridData();
		gd.horizontalIndent = 10;
		gd.grabExcessHorizontalSpace = true;
		gd.horizontalAlignment = SWT.FILL;
		networkInterfaceCombo.setLayoutData(gd);

		networkInterfaceCombo
				.setToolTipText("IP address to which workers (and distributed fingerprint sets) will connect.");
		networkInterfaceCombo.addSelectionListener(howToRunListener);
		networkInterfaceCombo.addFocusListener(focusListener);
		try {
			final Comparator<InetAddress> comparator = new Comparator<InetAddress>() {
				// Try to "guess" the best possible match.
				public int compare(InetAddress o1, InetAddress o2) {
					// IPv4 < IPv6 (v6 is less common even today)
					if (o1 instanceof Inet4Address && o2 instanceof Inet6Address) {
						return -1;
					} else if (o1 instanceof Inet6Address && o2 instanceof Inet4Address) {
						return 1;
					}

					// anything < LoopBack (loopback only useful if master and worker are on the
					// same host)
					if (!o1.isLoopbackAddress() && o2.isLoopbackAddress()) {
						return -1;
					} else if (o1.isLoopbackAddress() && !o2.isLoopbackAddress()) {
						return 1;
					}

					// Public Addresses < Non-private RFC 1918 (I guess this is questionable)
					if (!o1.isSiteLocalAddress() && o2.isSiteLocalAddress()) {
						return -1;
					} else if (o1.isSiteLocalAddress() && !o2.isSiteLocalAddress()) {
						return 1;
					}

					return 0;
				}
			};

			// Get all IP addresses of the host and sort them according to the Comparator.
			final List<InetAddress> addresses = new ArrayList<InetAddress>();
			final Enumeration<NetworkInterface> nets = NetworkInterface.getNetworkInterfaces();
			while (nets.hasMoreElements()) {
				final NetworkInterface iface = (NetworkInterface) nets.nextElement();
				final Enumeration<InetAddress> inetAddresses = iface.getInetAddresses();
				while (inetAddresses.hasMoreElements()) {
					final InetAddress addr = inetAddresses.nextElement();
					// Cannot connect to a multicast address
					if (addr.isMulticastAddress()) {
						continue;
					}
					addresses.add(addr);
				}
			}

			// Add the sorted IP addresses and select the first one which -
			// according to the comparator - is assumed to be the best match.
			Collections.sort(addresses, comparator);
			for (InetAddress inetAddress : addresses) {
				networkInterfaceCombo.add(inetAddress.getHostAddress());
			}
			networkInterfaceCombo.select(0);
		} catch (SocketException e1) {
			e1.printStackTrace();
		}

		dm.bindAttribute(LAUNCH_DISTRIBUTED_INTERFACE, networkInterfaceCombo, howToRunPart);

		/*
		 * Distributed FPSet count
		 */

		// label
		toolkit.createLabel(adHocOptions, "Number of distributed fingerprint sets (zero for single built-in set):");

		// field
		distributedFPSetCountSpinner = new Spinner(adHocOptions, SWT.NONE);
		distributedFPSetCountSpinner.addSelectionListener(howToRunListener);
		distributedFPSetCountSpinner.addFocusListener(focusListener);
		gd = new GridData();
		gd.grabExcessHorizontalSpace = true;
		gd.horizontalIndent = 10;
		gd.widthHint = 40;
		distributedFPSetCountSpinner.setLayoutData(gd);

		distributedFPSetCountSpinner.setMinimum(0);
		distributedFPSetCountSpinner.setMaximum(64); // Haven't really tested this many distributed fpsets
		distributedFPSetCountSpinner.setPageIncrement(1);
		distributedFPSetCountSpinner
				.setToolTipText("Determines how many distributed FPSets will be expected by the TLCServer process");
		distributedFPSetCountSpinner.setSelection(IConfigurationDefaults.LAUNCH_DISTRIBUTED_FPSET_COUNT_DEFAULT);

		dm.bindAttribute(LAUNCH_DISTRIBUTED_FPSET_COUNT, distributedFPSetCountSpinner, howToRunPart);

		/*
		 * Composite wrapping all widgets related to jclouds
		 */
		final Composite jcloudsOptions = new Composite(distributedOptions, SWT.NONE);
		gl = new GridLayout(2, false);
		gl.marginWidth = 0;
		jcloudsOptions.setLayout(gl);

		/*
		 * Distributed nodes count
		 */

		helpButton = HelpButton.helpButton(jcloudsOptions, "cloudtlc/index.html");
		gd = new GridData();
		gd.horizontalSpan = 2;
		gd.horizontalAlignment = SWT.END;
		helpButton.setLayoutData(gd);

		// label
		toolkit.createLabel(jcloudsOptions, "Number of compute nodes to use:");

		// field
		distributedNodesCountSpinner = new Spinner(jcloudsOptions, SWT.NONE);
		distributedNodesCountSpinner.addSelectionListener(howToRunListener);
		distributedNodesCountSpinner.addFocusListener(focusListener);
		gd = new GridData();
		gd.grabExcessHorizontalSpace = true;
		gd.horizontalIndent = 10;
		gd.widthHint = 40;
		distributedNodesCountSpinner.setLayoutData(gd);

		distributedNodesCountSpinner.setMinimum(1);
		distributedNodesCountSpinner.setMaximum(64); // Haven't really tested this many distributed fpsets
		distributedNodesCountSpinner.setPageIncrement(1);
		distributedNodesCountSpinner.setToolTipText(
				"Determines how many compute nodes/VMs will be launched. More VMs means faster results and higher costs.");
		distributedNodesCountSpinner.setSelection(IConfigurationDefaults.LAUNCH_DISTRIBUTED_NODES_COUNT_DEFAULT);

		dm.bindAttribute(LAUNCH_DISTRIBUTED_NODES_COUNT, distributedNodesCountSpinner, howToRunPart);

		/*
		 * Result mail address input
		 */
		toolkit.createLabel(jcloudsOptions, "Result mailto addresses:");
		resultMailAddressText = toolkit.createText(jcloudsOptions, "", SWT.BORDER);
		resultMailAddressText.setMessage("my-name@my-domain.org,alternative-name@alternative-domain.org");
		final String resultAddressTooltip = "A list (comma-separated) of one to N email addresses to send the model checking result to.";
		resultMailAddressText.setToolTipText(resultAddressTooltip);
		resultMailAddressText.addKeyListener(new KeyAdapter() {
			private final ModelEditor modelEditor = (ModelEditor) getEditor();

			@Override
			public void keyPressed(KeyEvent e) {
				super.keyPressed(e);
			}

			@Override
			public void keyReleased(KeyEvent e) {
				super.keyReleased(e);
				try {
					final String text = resultMailAddressText.getText();
					InternetAddress.parse(text, true);
				} catch (AddressException exp) {
					modelEditor.addErrorMessage("emailAddressInvalid", "Invalid email address", getId(),
							IMessageProvider.ERROR, resultMailAddressText);
					return;
				}
				clearEmailErrors();
			}
		});
		gd = new GridData();
		gd.horizontalAlignment = SWT.FILL;
		gd.grabExcessHorizontalSpace = true;
		gd.horizontalIndent = 10;
		gd.minimumWidth = 330;
		resultMailAddressText.setLayoutData(gd);
		resultMailAddressText.addModifyListener(howToRunListener);
		dm.bindAttribute(LAUNCH_DISTRIBUTED_RESULT_MAIL_ADDRESS, resultMailAddressText, howToRunPart);

		distributedOptions.setData(CLOUD_CONFIGURATION_KEY, jcloudsOptions);

	
		linkLineComposite = new Composite(body, SWT.NONE);
		twd = new TableWrapData();
		twd.colspan = 2;
		twd.grabHorizontal = true;
		twd.align = TableWrapData.RIGHT;
		linkLineComposite.setLayoutData(twd);
		linkLineComposite.setBackground(body.getDisplay().getSystemColor(SWT.COLOR_WHITE));
		gl = new GridLayout(1, false);
		gl.marginWidth = 0;
		gl.marginRight = 36;
		gl.horizontalSpacing = 0;
		linkLineComposite.setLayout(gl);
		hyper = toolkit.createHyperlink(linkLineComposite, "Evaluate Constant Expressions", SWT.NONE);
		hyper.addHyperlinkListener(resultsPageOpener);
		hyper.setFont(biggerLinkFont);
		
		
		// add listeners propagating the changes of the elements to the changes
		// of the parts to the list to be activated after the values has been loaded
		dirtyPartListeners.add(commentsListener);
		dirtyPartListeners.add(whatIsTheSpecListener);
		dirtyPartListeners.add(whatToCheckListener);
		dirtyPartListeners.add(howToRunListener);
		
		// add an empty ISelectionProvider; the default selection provider results in an infinite loop if the site
		//		never gets another one set.
		getSite().setSelectionProvider(new ISelectionProvider() {
			@Override
			public void addSelectionChangedListener(final ISelectionChangedListener listener) { }
			@Override
			public ISelection getSelection() {
				return null;
			}
			@Override
			public void removeSelectionChangedListener(final ISelectionChangedListener listener) { }
			@Override
			public void setSelection(final ISelection selection) { }
		});
	}

	private void moveToTopOfDistributedOptionsStack(final String id, final boolean enableWorker,
			final boolean enableMaxHeap) {
		workerValueCanBeModified.set(enableWorker);
		heapPercentageCanBeModified.set(enableMaxHeap);

		final IFormPage iep = getEditor().findPage(AdvancedTLCOptionsPage.ID);
		if (iep != null) {
			((AdvancedTLCOptionsPage) iep).setWorkerAndMemoryEnable(enableWorker, enableMaxHeap);
		}

		moveCompositeWithIdToTopOfStack(id, distributedOptions);

		distributedOptions.getParent().getParent().layout();
	}

	private void moveToTopOfBehaviorOptionsStack(final String id) {
		moveCompositeWithIdToTopOfStack(id, behaviorOptions);
	}

	private void moveCompositeWithIdToTopOfStack(final String id, final Composite parent) {
		final Composite composite = (Composite) parent.getData(id);
		final StackLayout stackLayout = (StackLayout) parent.getLayout();

		stackLayout.topControl = composite;
		parent.layout();
	}

	private TLCConsumptionProfile getSelectedTLCProfile() {
		return TLCConsumptionProfile.getProfileWithDisplayName(tlcProfileCombo.getText());
	}

	private void clearEmailErrors() {
		((ModelEditor) getEditor()).removeErrorMessage("emailAddressInvalid", resultMailAddressText);
	}

	private void setTLCProfileComboSelection(final String displayName) {
		final int index = tlcProfileCombo.indexOf(displayName);

		if (index != -1) {
			tlcProfileCombo.select(index);
			if (!CUSTOM_TLC_PROFILE_DISPLAY_NAME.equals(displayName)) {
				removeCustomTLCProfileComboItemIfPresent();
			}
		} else if (CUSTOM_TLC_PROFILE_DISPLAY_NAME.equals(displayName)) {
			tlcProfileCombo.add(displayName, 1);
			tlcProfileCombo.select(1);
		}

		lastSelectedTLCProfileIndex.set(tlcProfileCombo.getSelectionIndex());
	}

	private void removeCustomTLCProfileComboItemIfPresent() {
		if (tlcProfileCombo.getItem(1).equals(CUSTOM_TLC_PROFILE_DISPLAY_NAME)) {
			tlcProfileCombo.remove(1);
		}
	}

	private void updateTLCResourcesLabel() {
		final TLCConsumptionProfile profile = getSelectedTLCProfile();
		final StringBuilder sb = new StringBuilder();

		if ((profile == null) || !profile.profileIsForRemoteWorkers()
				|| TLCConsumptionProfile.REMOTE_AD_HOC.equals(profile)) {
			if ((profile != null) && profile.profileIsForRemoteWorkers()) {
				sb.append("Allocating ");
			} else {
				final int workerCount = workerThreadCount.get();

				sb.append(workerCount).append(" worker");
				if (workerCount > 1) {
					sb.append('s');
				}

				sb.append(" allocated ");
			}

			sb.append(generateMemoryDisplayText()).append(" of system memory.");
		}

		tlcResourceSummaryLabel.setText(sb.toString());
		tlcTuneHyperlink.setVisible(sb.toString().length() > 0);
	}

	private String generateMemoryDisplayText() {
		final int percentage = heapPercentage.get();
		final long megabytes = TLCRuntime.getInstance().getAbsolutePhysicalSystemMemory(percentage / 100d);

		return generateMemoryDisplayText(percentage, megabytes);
	}

	private void installTopMargin(final Composite body) {
		Composite c = body;
		CTabFolder tabFolder = (c instanceof CTabFolder) ? (CTabFolder) c : null;

		while ((tabFolder == null) && (c.getParent() != null)) {
			c = c.getParent();
			tabFolder = (c instanceof CTabFolder) ? (CTabFolder) c : null;
		}

		if (tabFolder != null) {
			final Layout l = tabFolder.getParent().getLayout();
			if (l instanceof FillLayout) {
				final FillLayout fl = (FillLayout) l;
				fl.marginHeight = 6;
			}
		}
	}
}
