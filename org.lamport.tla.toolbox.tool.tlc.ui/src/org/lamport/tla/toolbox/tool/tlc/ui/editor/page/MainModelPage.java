package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import java.util.Arrays;
import java.util.Calendar;
import java.util.List;
import java.util.Vector;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.PaintEvent;
import org.eclipse.swt.events.PaintListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Scale;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.forms.HyperlinkGroup;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.IMessageManager;
import org.eclipse.ui.forms.SectionPart;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.events.HyperlinkAdapter;
import org.eclipse.ui.forms.events.HyperlinkEvent;
import org.eclipse.ui.forms.widgets.ExpandableComposite;
import org.eclipse.ui.forms.widgets.FormText;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Hyperlink;
import org.eclipse.ui.forms.widgets.ImageHyperlink;
import org.eclipse.ui.forms.widgets.Section;
import org.eclipse.ui.forms.widgets.TableWrapData;
import org.lamport.tla.toolbox.tool.tlc.launch.IConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;
import org.lamport.tla.toolbox.tool.tlc.model.TypedSet;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.DataBindingManager;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.ValidateableConstantSectionPart;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.ValidateableSectionPart;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.ValidateableTableSectionPart;
import org.lamport.tla.toolbox.tool.tlc.ui.preference.ITLCPreferenceConstants;
import org.lamport.tla.toolbox.tool.tlc.ui.util.DirtyMarkingListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.util.SemanticHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.tool.tlc.util.TLCRuntime;
import org.lamport.tla.toolbox.util.IHelpConstants;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.ModuleNode;
import tlc2.TLC;
import tlc2.tool.fp.FPSet;

/**
 * Main model page represents information for most users
 * <br>
 * This class is a a sub-class of the BasicFormPage and is used to represent the first tab of the
 * multi-page-editor which is used to edit the model files.  
 * 
 * 
 * @author Simon Zambrovski
 * @version $Id$
 * This is the FormPage class for the Model Overview tabbed page of
 * the model editor.
 */
@SuppressWarnings("unchecked")
public class MainModelPage extends BasicFormPage implements IConfigurationConstants, IConfigurationDefaults
{
    public static final String ID = "MainModelPage";
    public static final String TITLE = "Model Overview";

    private Button noSpecRadio; // re-added on 10 Sep 2009
    private Button closedFormulaRadio;
    private Button initNextFairnessRadio;
    private SourceViewer initFormulaSource;
    private SourceViewer nextFormulaSource;
    // private SourceViewer fairnessFormulaSource;
    private SourceViewer specSource;
    private Button checkDeadlockButton;
    private Text workers;
    private Scale maxHeapSize;
    private Text fpBits;
    private TableViewer invariantsTable;
    private TableViewer propertiesTable;
    private TableViewer constantTable;
    private ModifyListener widgetActivatingListener = new ModifyListener() {
        // select the section (radio button) the text field belong to
        public void modifyText(ModifyEvent e)
        {
            if (e.widget == specSource.getControl())
            {
                noSpecRadio.setSelection(false);
                closedFormulaRadio.setSelection(true);
                initNextFairnessRadio.setSelection(false);
            } else if (e.widget == initFormulaSource.getControl() || e.widget == nextFormulaSource.getControl()
            /* || e.widget == fairnessFormulaSource.getControl() */)
            {
                noSpecRadio.setSelection(false);
                closedFormulaRadio.setSelection(false);
                initNextFairnessRadio.setSelection(true);
            }
        }
    };

    private ImageHyperlink runLink;
    private ImageHyperlink generateLink;

    /**
     * section expanding adapter
     * {@link Hyperlink#getHref()} must deliver the section id as described in {@link DataBindingManager#bindSection(ExpandableComposite, String, String)}
     */
    protected HyperlinkAdapter sectionExpandingAdapter = new HyperlinkAdapter() {
        public void linkActivated(HyperlinkEvent e)
        {
            String sectionId = (String) e.getHref();
            // first switch to the page (and construct it if not yet
            // constructed)
            getEditor().setActivePage(AdvancedModelPage.ID);
            // then expand the section
            expandSection(sectionId);
        }
    };
    private Button checkpointButton;
    private Text checkpointIdText;

    /*
     * Checkbox and input box for distributed model checking
     * 
     * button: activate distribution
     * text: additional vm arguments (e.g. -Djava.rmi...) 
     * text: pre-flight script
     */
    private Button distributedButton;
    private Text distributedText;
    private Text distributedScriptText;
    private Button browseDistributedScriptButton;
    
    // The widgets to display the checkpoint size and
    // the delete button.
    private FormText chkpointSizeLabel;
    private Text checkpointSizeText;
    private Button chkptDeleteButton;
    
	/**
	 * Used to interpolate y-values for memory scale
	 */
	private final Interpolator linearInterpolator;
	
    /**
     * constructs the main model page 
     * @param editor
     */
    public MainModelPage(FormEditor editor)
    {
        super(editor, MainModelPage.ID, MainModelPage.TITLE);
        this.helpId = IHelpConstants.MAIN_MODEL_PAGE;
        this.imagePath = "icons/full/choice_sc_obj.gif";

		// available system memory
		final long phySysMem = TLCRuntime.getInstance().getAbsolutePhysicalSystemMemory(1.0d);
		
		// 0.) Create LinearInterpolator with two additional points 0,0 and 1,0 which
		int s = 0;
		double[] x = new double[6];
		double[] y = new double[x.length];
		
		// base point
		y[s] = 0d;
		x[s++] = 0d;

		// 1.) Minumum TLC requirements 
		// Use hard-coded minfpmemsize value * 4 * 10 regardless of how big the
		// model is. *4 because .25 mem is used for FPs
		double lowerLimit = ( (TLC.MinFpMemSize / 1024 / 1024 * 4d) / phySysMem) / 2;
		x[s] = lowerLimit;
		y[s++] = 0d;
		
		// a.)
		// Current bloat in software is assumed to grow according to Moore's law => 
		// 2^((Year-1993)/ 2)+2)
		// (1993 as base results from a statistic of windows OS memory requirements)
		final int currentYear = Calendar.getInstance().get(Calendar.YEAR);
		double estimateSoftwareBloatInMBytes = Math.pow(2, ((currentYear - 1993) / 2) + 2);
		
		// 2.) Optimal range 
		x[s] = lowerLimit * 2d;
		y[s++] = 1.0d;
		x[s] = 1.0d - (estimateSoftwareBloatInMBytes / phySysMem);
		y[s++] = 1.0d;
		
		// 3.) Calculate OS reserve
		double upperLimit = 1.0d - (estimateSoftwareBloatInMBytes / phySysMem) / 2;
		x[s] = upperLimit;
		y[s++] = 0d;
		
		// base point
		x[s] = 1d;
		y[s] = 0d;
		
		linearInterpolator = new Interpolator(x, y);
}

    /**
     * @see BasicFormPage#loadData()
     */
    protected void loadData() throws CoreException
    {
        int specType = getConfig().getAttribute(MODEL_BEHAVIOR_SPEC_TYPE, MODEL_BEHAVIOR_TYPE_DEFAULT);

        // set up the radio buttons
        setSpecSelection(specType);

        // closed spec
        String modelSpecification = getConfig().getAttribute(MODEL_BEHAVIOR_CLOSED_SPECIFICATION, EMPTY_STRING);
        Document closedDoc = new Document(modelSpecification);
        this.specSource.setDocument(closedDoc);

        // init
        String modelInit = getConfig().getAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT, EMPTY_STRING);
        Document initDoc = new Document(modelInit);
        this.initFormulaSource.setDocument(initDoc);

        // next
        String modelNext = getConfig().getAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT, EMPTY_STRING);
        Document nextDoc = new Document(modelNext);
        this.nextFormulaSource.setDocument(nextDoc);

        // fairness
        // String modelFairness =
        // getConfig().getAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_FAIRNESS,
        // EMPTY_STRING);
        // Document fairnessDoc = new Document(modelFairness);
        // this.fairnessFormulaSource.setDocument(fairnessDoc);

        // number of workers
        workers.setText("" + getConfig().getAttribute(LAUNCH_NUMBER_OF_WORKERS, LAUNCH_NUMBER_OF_WORKERS_DEFAULT));

        // max JVM heap size
        final int defaultMaxHeapSize = TLCUIActivator.getDefault().getPreferenceStore().getInt(
                ITLCPreferenceConstants.I_TLC_MAXIMUM_HEAP_SIZE_DEFAULT);
        final int maxHeapSizeValue = getConfig().getAttribute(LAUNCH_MAX_HEAP_SIZE, defaultMaxHeapSize);
        maxHeapSize.setSelection(maxHeapSizeValue);
        
        // fpBits
        int defaultFPBits = TLCUIActivator.getDefault().getPreferenceStore().getInt(
                ITLCPreferenceConstants.I_TLC_FPBITS_DEFAULT);
        fpBits.setText("" + getConfig().getAttribute(LAUNCH_FPBITS, defaultFPBits));

        // check deadlock
        boolean checkDeadlock = getConfig().getAttribute(MODEL_CORRECTNESS_CHECK_DEADLOCK,
                MODEL_CORRECTNESS_CHECK_DEADLOCK_DEFAULT);
        this.checkDeadlockButton.setSelection(checkDeadlock);

        // invariants
        List<String> serializedList = getConfig().getAttribute(MODEL_CORRECTNESS_INVARIANTS, new Vector<String>());
        FormHelper.setSerializedInput(invariantsTable, serializedList);

        // properties
        serializedList = getConfig().getAttribute(MODEL_CORRECTNESS_PROPERTIES, new Vector<String>());
        FormHelper.setSerializedInput(propertiesTable, serializedList);

        // constants from the model
        List<String> savedConstants = getConfig().getAttribute(MODEL_PARAMETER_CONSTANTS, new Vector<String>());
        FormHelper.setSerializedInput(constantTable, savedConstants);

        // recover from the checkpoint
        boolean recover = getConfig().getAttribute(LAUNCH_RECOVER, LAUNCH_RECOVER_DEFAULT);
        this.checkpointButton.setSelection(recover);
        
        /*
         * Distributed mode
         */
        final boolean distributed = getConfig().getAttribute(LAUNCH_DISTRIBUTED, LAUNCH_DISTRIBUTED_DEFAULT);
        this.distributedButton.setSelection(distributed);

        final String vmArgs = getConfig().getAttribute(LAUNCH_DISTRIBUTED_ARGS, LAUNCH_DISTRIBUTED_ARGS_DEFAULT);
        this.distributedText.setText(vmArgs);
        
        final String distributedScript = getConfig().getAttribute(LAUNCH_DISTRIBUTED_SCRIPT, LAUNCH_DISTRIBUTED_SCRIPT_DEFAULT);
        this.distributedScriptText.setText(distributedScript);
        
    }

    public void validatePage(boolean switchToErrorPage)
    {
        if (getManagedForm() == null)
        {
            return;
        }

        DataBindingManager dm = getDataBindingManager();
        IMessageManager mm = getManagedForm().getMessageManager();
        ModelEditor modelEditor = (ModelEditor) getEditor();

        // delete the messages
        // this is now done in validateRunnable
        // in ModelEditor
        // resetAllMessages(false);

        // getting the root module node of the spec
        // this can be null!
        ModuleNode rootModuleNode = SemanticHelper.getRootModuleNode();

        // setup the names from the current page
        getLookupHelper().resetModelNames(this);

        // constants in the table
        List<Assignment> constants = (List<Assignment>) constantTable.getInput();
        // merge constants with currently defined in the specobj, if any
        if (rootModuleNode != null)
        {
            List<Assignment> toDelete = ModelHelper.mergeConstantLists(constants, ModelHelper.createConstantsList(rootModuleNode));
            if (!toDelete.isEmpty())
            {
                // if constants have been removed, these should be deleted from
                // the model too
                SectionPart constantSection = dm.getSection(dm.getSectionForAttribute(MODEL_PARAMETER_CONSTANTS));
                if (constantSection != null)
                {
                    // mark the constants dirty
                    constantSection.markDirty();
                }
            }
            constantTable.setInput(constants);
        }

        // The following string is used to test whether two differently-typed model
        // values appear in symmetry sets (sets of model values declared to be symmetric).
        // It is set to the type of the first typed model value found in a symmetry set.
        String symmetryType = null;
        // boolean symmetryUsed = false;
        // iterate over the constants
        for (int i = 0; i < constants.size(); i++)
        {
            Assignment constant = (Assignment) constants.get(i);

            List<String> values = Arrays.asList(constant.getParams());
            // check parameters
            validateId(MODEL_PARAMETER_CONSTANTS, values, "param1_", "A parameter name");

            // the constant is still in the list
            if (constant.getRight() == null || EMPTY_STRING.equals(constant.getRight()))
            {
                // right side of assignment undefined
                modelEditor.addErrorMessage(constant.getLabel(), "Provide a value for constant " + constant.getLabel(),
                        this.getId(), IMessageProvider.ERROR, UIHelper.getWidget(dm
                                .getAttributeControl(MODEL_PARAMETER_CONSTANTS)));
                setComplete(false);
                expandSection(dm.getSectionForAttribute(MODEL_PARAMETER_CONSTANTS));

            } else
            {
                if (constant.isSetOfModelValues())
                {
                    TypedSet modelValuesSet = TypedSet.parseSet(constant.getRight());

                    if (constant.isSymmetricalSet())
                    {
                        boolean hasTwoTypes = false; // set true if this symmetry set has two differently-typed model
                        // values.
                        String typeString = null; // set to the type of the first typed model value in this symmetry
                        // set.
                        if (modelValuesSet.hasType())
                        {
                            typeString = modelValuesSet.getType();
                        } else
                        {
                            for (int j = 0; j < modelValuesSet.getValues().length; j++)
                            {
                                String thisTypeString = TypedSet.getTypeOfId(modelValuesSet.getValues()[j]);
                                if (thisTypeString != null)
                                {
                                    if (typeString != null && !typeString.equals(thisTypeString))
                                    {
                                        hasTwoTypes = true;
                                    } else
                                    {
                                        typeString = thisTypeString;
                                    }
                                }
                            }
                        }
                        if (hasTwoTypes
                                || (symmetryType != null && typeString != null && !typeString.equals(symmetryType)))
                        {
                            modelEditor.addErrorMessage(constant.getLabel(),
                                    "Two differently typed model values used in symmetry sets.",
                                    this.getId()/*constant*/, IMessageProvider.ERROR, UIHelper.getWidget(dm
                                            .getAttributeControl(MODEL_PARAMETER_CONSTANTS)));
                            setComplete(false);
                            expandSection(dm.getSectionForAttribute(MODEL_PARAMETER_CONSTANTS));
                        } else
                        {
                            if (typeString != null)
                            {
                                symmetryType = typeString;
                            }
                        }

                        // symmetry can be used for only one set of model values

                    }
                    if (modelValuesSet.getValueCount() > 0)
                    {
                        // there were values defined
                        // check if those are numbers?
                        /*
                         * if (modelValuesSet.hasANumberOnlyValue()) {
                         * mm.addMessage("modelValues1",
                         * "A model value can not be an number", modelValuesSet,
                         * IMessageProvider.ERROR, constantTable.getTable());
                         * setComplete(false); }
                         */

                        List<String> mvList = modelValuesSet.getValuesAsList();
                        // check list of model values
                        validateUsage(MODEL_PARAMETER_CONSTANTS, mvList, "modelValues2_", "A model value",
                                "Constant Assignment", true);
                        // check if the values are correct ids
                        validateId(MODEL_PARAMETER_CONSTANTS, mvList, "modelValues2_", "A model value");

                        // get widget for model values assigned to constant
                        Control widget = UIHelper.getWidget(dm.getAttributeControl(MODEL_PARAMETER_CONSTANTS));
                        // check if model values are config file keywords
                        for (int j = 0; j < mvList.size(); j++)
                        {
                            String value = (String) mvList.get(j);
                            if (SemanticHelper.isConfigFileKeyword(value))
                            {
                                modelEditor.addErrorMessage(value, "The toolbox cannot handle the model value " + value
                                        + ".", this.getId(), IMessageProvider.ERROR, widget);
                                setComplete(false);
                            }
                        }
                    } else
                    {
                        // This made an error by LL on 15 Nov 2009
                        modelEditor.addErrorMessage(constant.getLabel(),
                                "The set of model values should not be empty.", this.getId(), IMessageProvider.ERROR,
                                UIHelper.getWidget(dm.getAttributeControl(MODEL_PARAMETER_CONSTANTS)));
                        setComplete(false);
                    }
                }
            }

            // the constant identifier is a config file keyword
            if (SemanticHelper.isConfigFileKeyword(constant.getLabel()))
            {
                modelEditor.addErrorMessage(constant.getLabel(), "The toolbox cannot handle the constant identifier "
                        + constant.getLabel() + ".", this.getId(), IMessageProvider.ERROR, UIHelper.getWidget(dm
                        .getAttributeControl(MODEL_PARAMETER_CONSTANTS)));
                setComplete(false);
            }
        }

        // iterate over the constants again, and check if the parameters are used as Model Values
        for (int i = 0; i < constants.size(); i++)
        {
            Assignment constant = (Assignment) constants.get(i);
            List<String> values = Arrays.asList(constant.getParams());
            // check list of parameters
            validateUsage(MODEL_PARAMETER_CONSTANTS, values, "param1_", "A parameter name", "Constant Assignment",
                    false);
        }

        // number of workers
        String numberOfworkers = workers.getText();
        try
        {
            int number = Integer.parseInt(numberOfworkers);
            if (number <= 0)
            {
                modelEditor.addErrorMessage("wrongNumber1", "Number of workers must be a positive integer number", this
                        .getId(), IMessageProvider.ERROR, UIHelper.getWidget(dm
                        .getAttributeControl(LAUNCH_NUMBER_OF_WORKERS)));
                setComplete(false);
                expandSection(SEC_HOW_TO_RUN);
            } else
            {
                if (number > Runtime.getRuntime().availableProcessors())
                {
                    modelEditor.addErrorMessage("strangeNumber1", "Specified number of workers is " + number
                            + ". The number of CPU Cores available on the system is "
                            + Runtime.getRuntime().availableProcessors()
                            + ".\n It is not advisable that the number of workers exceeds the number of CPU Cores.",
                            this.getId(), IMessageProvider.WARNING, UIHelper.getWidget(dm
                                    .getAttributeControl(LAUNCH_NUMBER_OF_WORKERS)));
                    expandSection(SEC_HOW_TO_RUN);
                }
            }
        } catch (NumberFormatException e)
        {
            modelEditor.addErrorMessage("wrongNumber2", "Number of workers must be a positive integer number", this
                    .getId(), IMessageProvider.ERROR, UIHelper.getWidget(dm
                    .getAttributeControl(LAUNCH_NUMBER_OF_WORKERS)));
            setComplete(false);
            expandSection(SEC_HOW_TO_RUN);
        }

        
        // max heap size
		// color the scale according to OS and TLC requirements
        int maxHeapSizeValue = maxHeapSize.getSelection();
		double x = maxHeapSizeValue / 100d;
		float y = (float) linearInterpolator.interpolate(x);
		maxHeapSize.setBackground(new Color(Display.getDefault(), new RGB(
				120 * y, 1 - y, 1f)));
        
        // fpBits
        String fpBitsString = fpBits.getText();
        try {
            int fpBitsNum = Integer.parseInt(fpBitsString);
            if (!FPSet.isValid(fpBitsNum))
            {
                modelEditor.addErrorMessage("wrongNumber3", "fpbits must be a positive integer number smaller than 31", this
                        .getId(), IMessageProvider.ERROR, UIHelper.getWidget(dm
                        .getAttributeControl(LAUNCH_FPBITS)));
                setComplete(false);
                expandSection(SEC_HOW_TO_RUN);
            }
        } catch (NumberFormatException e) {
            modelEditor.addErrorMessage("wrongNumber4", "fpbits must be a positive integer number smaller than 64", this
                    .getId(), IMessageProvider.ERROR, UIHelper.getWidget(dm.getAttributeControl(LAUNCH_FPBITS)));
            setComplete(false);
            expandSection(SEC_HOW_TO_RUN);
		}

        // fill the checkpoints
        updateCheckpoints();

        // recover from checkpoint
        if (checkpointButton.getSelection())
        {
            if (EMPTY_STRING.equals(checkpointIdText.getText()))
            {
                modelEditor.addErrorMessage("noChckpoint", "No checkpoint data found", this.getId(),
                        IMessageProvider.ERROR, UIHelper.getWidget(dm.getAttributeControl(LAUNCH_RECOVER)));
                setComplete(false);
                expandSection(SEC_HOW_TO_RUN);
            }
        }
        
        // The following code added by LL and DR on 10 Sep 2009.
        // Reset the enabling and selection of spec type depending on the number number
        // of variables in the spec.
        // This code needs to be modified when we modify the model launcher
        // to allow the No Spec option to be selected when there are variables.
        if (rootModuleNode != null)
        {
            if (rootModuleNode.getVariableDecls().length == 0)
            {
                setHasVariables(false);

                // set selection to the NO SPEC field
                if (!noSpecRadio.getSelection())
                {
                    // mark dirty so that changes must be written to config file
                    setSpecSelection(MODEL_BEHAVIOR_TYPE_NO_SPEC);
                    dm.getSection(dm.getSectionForAttribute(MODEL_BEHAVIOR_NO_SPEC)).markDirty();

                }
            } else
            {
                setHasVariables(true);

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
        Section whatToCheckSection = dm.getSection(SEC_WHAT_TO_CHECK).getSection();

        if (noSpecRadio.getSelection())
        {
            whatToCheckSection.setExpanded(false);
            whatToCheckSection.setEnabled(false);

        } else
        {
            whatToCheckSection.setExpanded(true);
            whatToCheckSection.setEnabled(true);
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
        if (closedFormulaRadio.getSelection() && specSource.getDocument().get().trim().equals(""))
        {
            modelEditor.addErrorMessage("noSpec", "The formula must be provided", this.getId(), IMessageProvider.ERROR,
                    UIHelper.getWidget(dm.getAttributeControl(MODEL_BEHAVIOR_CLOSED_SPECIFICATION)));
            setComplete(false);
            expandSection(dm.getSectionForAttribute(MODEL_BEHAVIOR_CLOSED_SPECIFICATION));
        } else if (initNextFairnessRadio.getSelection())
        {
            String init = initFormulaSource.getDocument().get().trim();
            String next = nextFormulaSource.getDocument().get().trim();

            if (init.equals(""))
            {
                modelEditor.addErrorMessage("noInit", "The Init formula must be provided", this.getId(),
                        IMessageProvider.ERROR, UIHelper.getWidget(dm
                                .getAttributeControl(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT)));
                setComplete(false);
                expandSection(dm.getSectionForAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT));
            }
            if (next.equals(""))
            {
                modelEditor.addErrorMessage("noNext", "The Next formula must be provided", this.getId(),
                        IMessageProvider.ERROR, UIHelper.getWidget(dm
                                .getAttributeControl(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT)));
                setComplete(false);
                expandSection(dm.getSectionForAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT));
            }
        }
        
        // enablement for distributed input text boxes depends on button
        boolean distributed = this.distributedButton.getSelection();
        this.distributedText.setEnabled(distributed);
        this.distributedScriptText.setEnabled(distributed);
        
        // verify existence of pre-flight script
//       	if(distributed) {
//       		final String scriptPath = distributedScriptText.getText();
//       		if(scriptPath != null && !"".equals(scriptPath)) {
//       			final File f = new File(scriptPath);
//       			if(!f.exists()) {
//                    modelEditor.addErrorMessage("noScript", "No script file found", this.getId(),
//                            IMessageProvider.ERROR, UIHelper.getWidget(dm.getAttributeControl(LAUNCH_DISTRIBUTED_SCRIPT)));
//                    setComplete(false);
//                    expandSection(SEC_HOW_TO_RUN);
//       			}
//       		}
//       	}
//       	

        mm.setAutoUpdate(true);

        super.validatePage(switchToErrorPage);
    }

    /**
     * This method is used to enable and disable UI widgets depending on the fact if the specification 
     * has variables. 
     * @param hasVariables true if the spec contains variables
     */
    private void setHasVariables(boolean hasVariables)
    {

        // the no spec option can be selected if there
        // are variables or no variables
        // this.noSpecRadio.setEnabled(!hasVariables);
        this.closedFormulaRadio.setEnabled(hasVariables);
        this.initNextFairnessRadio.setEnabled(hasVariables);

        // the input fields are enabled only if there are variables
        this.initFormulaSource.getControl().setEnabled(hasVariables);
        this.nextFormulaSource.getControl().setEnabled(hasVariables);
        this.specSource.getControl().setEnabled(hasVariables);
    }

    /**
     * This method sets the selection on the 
     * @param selectedFormula
     */
    private void setSpecSelection(int specType)
    {
        switch (specType) {
        case MODEL_BEHAVIOR_TYPE_NO_SPEC:
            this.noSpecRadio.setSelection(true);
            this.initNextFairnessRadio.setSelection(false);
            this.closedFormulaRadio.setSelection(false);
            break;
        case MODEL_BEHAVIOR_TYPE_SPEC_CLOSED:
            this.noSpecRadio.setSelection(false);
            this.initNextFairnessRadio.setSelection(false);
            this.closedFormulaRadio.setSelection(true);
            break;
        case MODEL_BEHAVIOR_TYPE_SPEC_INIT_NEXT:
            this.noSpecRadio.setSelection(false);
            this.initNextFairnessRadio.setSelection(true);
            this.closedFormulaRadio.setSelection(false);
            break;
        default:
            throw new IllegalArgumentException("Wrong spec type, this is a bug");
        }

    }

    /**
     * Save data back to model
     */
	public void commit(boolean onSave)
    {
        // TLCUIActivator.logDebug("Main page commit");
        // closed formula
        String closedFormula = FormHelper.trimTrailingSpaces(this.specSource.getDocument().get());
        getConfig().setAttribute(MODEL_BEHAVIOR_CLOSED_SPECIFICATION, closedFormula);

        // init formula
        String initFormula = FormHelper.trimTrailingSpaces(this.initFormulaSource.getDocument().get());
        getConfig().setAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT, initFormula);

        // next formula
        String nextFormula = FormHelper.trimTrailingSpaces(this.nextFormulaSource.getDocument().get());
        getConfig().setAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT, nextFormula);

        // fairness formula
        // String fairnessFormula =
        // FormHelper.trimTrailingSpaces(this.fairnessFormulaSource.getDocument().get());
        // getConfig().setAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_FAIRNESS,
        // fairnessFormula);

        // mode
        int specType;
        if (this.closedFormulaRadio.getSelection())
        {
            specType = MODEL_BEHAVIOR_TYPE_SPEC_CLOSED;
        } else if (this.initNextFairnessRadio.getSelection())
        {
            specType = MODEL_BEHAVIOR_TYPE_SPEC_INIT_NEXT;
        } else if (this.noSpecRadio.getSelection())
        {
            specType = MODEL_BEHAVIOR_TYPE_NO_SPEC;
        } else
        {
            specType = MODEL_BEHAVIOR_TYPE_DEFAULT;
        }

        getConfig().setAttribute(MODEL_BEHAVIOR_SPEC_TYPE, specType);

        // number of workers
        int numberOfWorkers = LAUNCH_NUMBER_OF_WORKERS_DEFAULT;
        try
        {
            numberOfWorkers = Integer.parseInt(workers.getText());
        } catch (NumberFormatException e)
        { /* does not matter */
        }
        getConfig().setAttribute(LAUNCH_NUMBER_OF_WORKERS, numberOfWorkers);

        int maxHeapSizeValue = TLCUIActivator.getDefault().getPreferenceStore().getInt(
                ITLCPreferenceConstants.I_TLC_MAXIMUM_HEAP_SIZE_DEFAULT);
        maxHeapSizeValue = maxHeapSize.getSelection();
        getConfig().setAttribute(LAUNCH_MAX_HEAP_SIZE, maxHeapSizeValue);

        // fpBits
        int fpBitsInt = TLCUIActivator.getDefault().getPreferenceStore().getInt(
                ITLCPreferenceConstants.I_TLC_MAXIMUM_HEAP_SIZE_DEFAULT);
        try
        {
        	fpBitsInt = Integer.parseInt(fpBits.getText());
        } catch (NumberFormatException e)
        { /* does not matter */
        }
        getConfig().setAttribute(LAUNCH_FPBITS, fpBitsInt);
        
        // recover from deadlock
        boolean recover = this.checkpointButton.getSelection();
        getConfig().setAttribute(LAUNCH_RECOVER, recover);

        // check deadlock
        boolean checkDeadlock = this.checkDeadlockButton.getSelection();
        getConfig().setAttribute(MODEL_CORRECTNESS_CHECK_DEADLOCK, checkDeadlock);

        // run in distributed mode
        boolean distributed = this.distributedButton.getSelection();
        getConfig().setAttribute(LAUNCH_DISTRIBUTED, distributed);
        
        final String vmArgs = this.distributedText.getText();
        getConfig().setAttribute(LAUNCH_DISTRIBUTED_ARGS, vmArgs);
        
        final String distributedScript = this.distributedScriptText.getText();
        getConfig().setAttribute(LAUNCH_DISTRIBUTED_SCRIPT, distributedScript);

        // invariants
        List<String> serializedList = FormHelper.getSerializedInput(invariantsTable);
        getConfig().setAttribute(MODEL_CORRECTNESS_INVARIANTS, serializedList);

        // properties
        serializedList = FormHelper.getSerializedInput(propertiesTable);
        getConfig().setAttribute(MODEL_CORRECTNESS_PROPERTIES, serializedList);

        // constants
        List<String> constants = FormHelper.getSerializedInput(constantTable);
        getConfig().setAttribute(MODEL_PARAMETER_CONSTANTS, constants);

        // variables
        String variables = ModelHelper.createVariableList(SemanticHelper.getRootModuleNode());
        getConfig().setAttribute(MODEL_BEHAVIOR_VARS, variables);

        super.commit(onSave);
    }

    /**
     * Checks if checkpoint information changed 
     */
    private void updateCheckpoints()
    {
        IResource[] checkpoints = null;
        try
        {
            // checkpoint id
            checkpoints = ModelHelper.getCheckpoints(getConfig(), false);
        } catch (CoreException e)
        {
            TLCUIActivator.logError("Error checking chekpoint data", e);
        }

        if (checkpoints != null && checkpoints.length > 0)
        {
            this.checkpointIdText.setText(checkpoints[0].getName());
        } else
        {
            this.checkpointIdText.setText(EMPTY_STRING);
        }

        if ((checkpoints == null) || (checkpoints.length == 0))
        {
            checkpointSizeText.setVisible(false);
            chkpointSizeLabel.setVisible(false);
            chkptDeleteButton.setVisible(false);
        } else
        {
            checkpointSizeText.setText(String.valueOf(ResourceHelper.getSizeOfJavaFileResource(checkpoints[0]) / 1000));
            checkpointSizeText.setVisible(true);
            chkpointSizeLabel.setVisible(true);
            chkptDeleteButton.setVisible(true);
        }
    }

    /**
     * Creates the UI
     * This method is called to create the widgets and arrange them on the page
     * 
     * Its helpful to know what the standard SWT widgets look like.
     * Pictures can be found at http://www.eclipse.org/swt/widgets/
     * 
     * Layouts are used throughout this method.
     * A good explanation of layouts is given in the article
     * http://www.eclipse.org/articles/article.php?file=Article-Understanding-Layouts/index.html
     */
    protected void createBodyContent(IManagedForm managedForm)
    {
        DataBindingManager dm = getDataBindingManager();
        int sectionFlags = Section.TITLE_BAR | Section.DESCRIPTION | Section.TREE_NODE;
        FormToolkit toolkit = managedForm.getToolkit();
        Composite body = managedForm.getForm().getBody();

        GridData gd;
        TableWrapData twd;

        /*
         * Because the two Composite objects `left' and `right' are added to the
         * object `body' in this order, `left' is displayed to the left of `right'.
         */
        // left
        Composite left = toolkit.createComposite(body);
        twd = new TableWrapData(TableWrapData.FILL_GRAB);
        twd.grabHorizontal = true;
        left.setLayout(new GridLayout(1, false));
        left.setLayoutData(twd);

        // right
        Composite right = toolkit.createComposite(body);
        twd = new TableWrapData(TableWrapData.FILL_GRAB);
        twd.grabHorizontal = true;
        right.setLayoutData(twd);
        right.setLayout(new GridLayout(1, false));

        Section section;
        GridLayout layout;

        // ------------------------------------------
        // what is the spec
        section = FormHelper.createSectionComposite(left, "What is the behavior spec?", "", toolkit, sectionFlags
                | Section.EXPANDED, getExpansionListener());
        // only grab horizontal space
        gd = new GridData(GridData.FILL_HORIZONTAL);
        section.setLayoutData(gd);

        Composite behaviorArea = (Composite) section.getClient();
        layout = new GridLayout();
        layout.numColumns = 2;
        behaviorArea.setLayout(layout);

        ValidateableSectionPart behaviorPart = new ValidateableSectionPart(section, this, SEC_WHAT_IS_THE_SPEC);
        managedForm.addPart(behaviorPart);
        DirtyMarkingListener whatIsTheSpecListener = new DirtyMarkingListener(behaviorPart, true);
        // split formula option
        initNextFairnessRadio = toolkit.createButton(behaviorArea, "Initial predicate and next-state relation",
                SWT.RADIO);
        initNextFairnessRadio.addFocusListener(focusListener);

        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.horizontalSpan = 2;
        initNextFairnessRadio.setLayoutData(gd);
        initNextFairnessRadio.addSelectionListener(whatIsTheSpecListener);
        initNextFairnessRadio.addFocusListener(focusListener);

        // init
        toolkit.createLabel(behaviorArea, "Init:");
        initFormulaSource = FormHelper.createFormsSourceViewer(toolkit, behaviorArea, SWT.NONE | SWT.SINGLE);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 18;
        initFormulaSource.getTextWidget().setLayoutData(gd);
        initFormulaSource.getTextWidget().addModifyListener(whatIsTheSpecListener);
        initFormulaSource.getTextWidget().addModifyListener(widgetActivatingListener);
        initFormulaSource.getTextWidget().addFocusListener(focusListener);
        dm.bindAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT, initFormulaSource, behaviorPart);

        // next
        toolkit.createLabel(behaviorArea, "Next:");
        nextFormulaSource = FormHelper.createFormsSourceViewer(toolkit, behaviorArea, SWT.NONE | SWT.SINGLE);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 18;
        nextFormulaSource.getTextWidget().setLayoutData(gd);
        nextFormulaSource.getTextWidget().addModifyListener(whatIsTheSpecListener);
        nextFormulaSource.getTextWidget().addModifyListener(widgetActivatingListener);
        nextFormulaSource.getTextWidget().addFocusListener(focusListener);
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
        closedFormulaRadio = toolkit.createButton(behaviorArea, "Temporal formula", SWT.RADIO);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.horizontalSpan = 2;
        closedFormulaRadio.setLayoutData(gd);
        closedFormulaRadio.addSelectionListener(whatIsTheSpecListener);

        // spec
        Label specLabel = toolkit.createLabel(behaviorArea, "");
        // changed from "Spec:" 10 Sep 09
        gd = new GridData();
        gd.verticalAlignment = SWT.TOP;
        specLabel.setLayoutData(gd);
        specSource = FormHelper.createFormsSourceViewer(toolkit, behaviorArea, SWT.V_SCROLL);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 55;
        specSource.getTextWidget().setLayoutData(gd);
        specSource.getTextWidget().addModifyListener(whatIsTheSpecListener);
        specSource.getTextWidget().addModifyListener(widgetActivatingListener);
        dm.bindAttribute(MODEL_BEHAVIOR_CLOSED_SPECIFICATION, specSource, behaviorPart);

        noSpecRadio = toolkit.createButton(behaviorArea, "No Behavior Spec", SWT.RADIO);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.horizontalSpan = 2;
        noSpecRadio.setLayoutData(gd);
        noSpecRadio.addSelectionListener(whatIsTheSpecListener);
        dm.bindAttribute(MODEL_BEHAVIOR_NO_SPEC, noSpecRadio, behaviorPart);

        // ------------------------------------------
        // what to check
        section = FormHelper.createSectionComposite(left, "What to check?", "", toolkit, sectionFlags
                | Section.EXPANDED, getExpansionListener());
        // only grab horizontal space
        gd = new GridData(GridData.FILL_HORIZONTAL);
        section.setLayoutData(gd);

        Composite toBeCheckedArea = (Composite) section.getClient();
        layout = new GridLayout();
        layout.numColumns = 1;
        toBeCheckedArea.setLayout(layout);

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

        // The following code added by LL on 29 May 2010 to expand the Property section
        // and reset the MODEL_PROPERTIES_EXPAND property to "" if that property has 
        // been set to a non-"" value.
        int propFlags = sectionFlags;
        try
        {
            if (!((String) getConfig().getAttribute(MODEL_PROPERTIES_EXPAND, "")).equals("")) {
               propFlags = propFlags | Section.EXPANDED;
               getConfig().setAttribute(MODEL_PROPERTIES_EXPAND, "");
            }
        } catch (CoreException e)
        {
            // I don't know why such an exception might occur, but there's no
            // great harm if it does. LL
        	e.printStackTrace();
        }
        ValidateableTableSectionPart propertiesPart = new ValidateableTableSectionPart(toBeCheckedArea, "Properties",
                "Temporal formulas true for every possible behavior.", toolkit, propFlags, this,
                SEC_WHAT_TO_CHECK_PROPERTIES);
        managedForm.addPart(propertiesPart);
        propertiesTable = propertiesPart.getTableViewer();
        dm.bindAttribute(MODEL_CORRECTNESS_PROPERTIES, propertiesTable, propertiesPart);

        // ------------------------------------------
        // what is the model

        // Constants
        ValidateableConstantSectionPart constantsPart = new ValidateableConstantSectionPart(right,
                "What is the model?", "Specify the values of declared constants.", toolkit, sectionFlags
                        | Section.EXPANDED, this, SEC_WHAT_IS_THE_MODEL);
        managedForm.addPart(constantsPart);
        constantTable = constantsPart.getTableViewer();
        dm.bindAttribute(MODEL_PARAMETER_CONSTANTS, constantTable, constantsPart);
        Composite parametersArea = (Composite) constantsPart.getSection().getClient();
        HyperlinkGroup group = new HyperlinkGroup(parametersArea.getDisplay());

        // TESTING XXXXXX
        // managedForm.removePart(constantsPart);
        // Control saved = right.getChildren()[0] ;
        // constantTable.getTable().setSize(1000, 1000);
        // constantTable.getTable().setVisible(false);
        //        
        // System.out.println("GetSize returns " +
        // constantTable.getTable().getSize().x);
        // right.getChildren()[0].setVisible(false);
        // parametersArea.setVisible(false);

        // create a composite to put the text into
        Composite linksPanelToAdvancedPage = toolkit.createComposite(parametersArea);
        gd = new GridData();
        gd.horizontalSpan = 2;

        linksPanelToAdvancedPage.setLayoutData(gd);
        linksPanelToAdvancedPage.setLayout(new FillLayout(SWT.VERTICAL));

        // first line with hyperlinks
        Composite elementLine = toolkit.createComposite(linksPanelToAdvancedPage);
        elementLine.setLayout(new FillLayout(SWT.HORIZONTAL));

        // the text
        FormText labelText = toolkit.createFormText(elementLine, false);
        labelText.setText("Advanced parts of the model:", false, false);

        // the hyperlinks
        Hyperlink hyper;

        hyper = toolkit.createHyperlink(elementLine, "Additional definitions,", SWT.NONE);
        hyper.setHref(SEC_NEW_DEFINITION);
        hyper.addHyperlinkListener(sectionExpandingAdapter);

        hyper = toolkit.createHyperlink(elementLine, "Definition override,", SWT.NONE);
        hyper.setHref(SEC_DEFINITION_OVERRIDE);
        hyper.addHyperlinkListener(sectionExpandingAdapter);

        // second line with hyperlinks
        Composite elementLine2 = toolkit.createComposite(linksPanelToAdvancedPage);
        elementLine2.setLayout(new FillLayout(SWT.HORIZONTAL));

        hyper = toolkit.createHyperlink(elementLine2, "State constraints,", SWT.NONE);
        hyper.setHref(SEC_STATE_CONSTRAINT);
        hyper.addHyperlinkListener(sectionExpandingAdapter);

        hyper = toolkit.createHyperlink(elementLine2, "Action constraints,", SWT.NONE);
        hyper.setHref(SEC_ACTION_CONSTRAINT);
        hyper.addHyperlinkListener(sectionExpandingAdapter);

        hyper = toolkit.createHyperlink(elementLine2, "Additional model values.", SWT.NONE);
        hyper.setHref(SEC_MODEL_VALUES);
        hyper.addHyperlinkListener(sectionExpandingAdapter);

        // ------------------------------------------
        // run tab
        section = FormHelper.createSectionComposite(right, "How to run?", "TLC Parameters", toolkit, sectionFlags,
                getExpansionListener());
        gd = new GridData(GridData.FILL_HORIZONTAL);
        section.setLayoutData(gd);

        final Composite howToRunArea = (Composite) section.getClient();
        group = new HyperlinkGroup(howToRunArea.getDisplay());
        layout = new GridLayout(2, true);
        howToRunArea.setLayout(layout);

        ValidateableSectionPart howToRunPart = new ValidateableSectionPart(section, this, SEC_HOW_TO_RUN);
        managedForm.addPart(howToRunPart);

        DirtyMarkingListener howToRunListener = new DirtyMarkingListener(howToRunPart, true);

        // max heap size label
        FormText maxHeapLabel = toolkit.createFormText(howToRunArea, true);
        maxHeapLabel.setText("Fraction of physical memory allocated to model checker:", false, false);

		// Create a composite inside the right "cell" of the "how to run"
		// section grid layout to fit the scale and the maxHeapSizeFraction
		// label into a single row.
        final Composite maxHeapScale = new Composite(howToRunArea, SWT.NONE);
        layout = new GridLayout(2, false);
        maxHeapScale.setLayout(layout);

        // field max heap size
        int defaultMaxHeapSize = TLCUIActivator.getDefault().getPreferenceStore().getInt(
                ITLCPreferenceConstants.I_TLC_MAXIMUM_HEAP_SIZE_DEFAULT);
        maxHeapSize = new Scale(maxHeapScale, SWT.NONE);
        maxHeapSize.addSelectionListener(howToRunListener);
        maxHeapSize.addFocusListener(focusListener);
        gd = new GridData();
        gd.horizontalIndent = 10;
        gd.widthHint = 250;
        maxHeapSize.setLayoutData(gd);
        maxHeapSize.setMaximum(99);
        maxHeapSize.setMinimum(1);
        maxHeapSize.setPageIncrement(5);
        maxHeapSize.setSelection(defaultMaxHeapSize);
        maxHeapSize.setToolTipText("This translates to the heap size of the nested TLC Java VM");

        dm.bindAttribute(LAUNCH_MAX_HEAP_SIZE, maxHeapSize, howToRunPart);
        
        // label next to the scale showing the current fraction selected
        final FormText maxHeapSizeFraction = toolkit.createFormText(maxHeapScale, false);
		final TLCRuntime instance = TLCRuntime.getInstance();
		long memory = instance.getAbsolutePhysicalSystemMemory(defaultMaxHeapSize / 100d);
        maxHeapSizeFraction.setText(defaultMaxHeapSize + "%" + " (" + memory + " mb)", false, false);
        maxHeapSize.addPaintListener(new PaintListener() {
			/* (non-Javadoc)
			 * @see org.eclipse.swt.events.PaintListener#paintControl(org.eclipse.swt.events.PaintEvent)
			 */
			public void paintControl(PaintEvent e) {
				// update the label
				int value = ((Scale) e.getSource()).getSelection();
				final TLCRuntime instance = TLCRuntime.getInstance();
				long memory = instance.getAbsolutePhysicalSystemMemory(value / 100d);
				maxHeapSizeFraction.setText(value + "%" + " (" + memory + " mb)" , false, false);
			}
		});

        // fpbits
        FormText fpBitsLabel = toolkit.createFormText(howToRunArea, true);
        fpBitsLabel.setText("2^n amount of disc storage files:", false, false);

        int defaultFPBits = TLCUIActivator.getDefault().getPreferenceStore().getInt(
                ITLCPreferenceConstants.I_TLC_FPBITS_DEFAULT);
        fpBits = toolkit.createText(howToRunArea, "" + defaultFPBits);
        fpBits.addModifyListener(howToRunListener);
        fpBits.addFocusListener(focusListener);
        gd = new GridData();
        gd.horizontalIndent = 10;
        gd.widthHint = 60;
        fpBits.setLayoutData(gd);

        dm.bindAttribute(LAUNCH_FPBITS, fpBits, howToRunPart);
        
        // label workers
        FormText workersLabel = toolkit.createFormText(howToRunArea, true);
        workersLabel.setText("Number of worker threads:", false, false);

        // field workers
        workers = toolkit.createText(howToRunArea, "1");
        workers.addModifyListener(howToRunListener);
        workers.addFocusListener(focusListener);
        gd = new GridData();
        gd.horizontalIndent = 10;
        gd.widthHint = 40;
        workers.setLayoutData(gd);

        dm.bindAttribute(LAUNCH_NUMBER_OF_WORKERS, workers, howToRunPart);
        
        /*
         * run from the checkpoint
         */
        checkpointButton = toolkit.createButton(howToRunArea, "Recover from checkpoint", SWT.CHECK);
        gd = new GridData();
        gd.horizontalSpan = 2;
        gd.verticalIndent = 20;

        checkpointButton.setLayoutData(gd);
        checkpointButton.addSelectionListener(howToRunListener);
        checkpointButton.addFocusListener(focusListener);

        FormText chkpointIdLabel = toolkit.createFormText(howToRunArea, true);
        chkpointIdLabel.setText("Checkpoint ID:", false, false);

        checkpointIdText = toolkit.createText(howToRunArea, "");
        checkpointIdText.setEditable(false);
        gd = new GridData();
        gd.horizontalIndent = 10;
        gd.widthHint = 100;
        checkpointIdText.setLayoutData(gd);
        dm.bindAttribute(LAUNCH_RECOVER, checkpointButton, howToRunPart);

        chkpointSizeLabel = toolkit.createFormText(howToRunArea, true);
        chkpointSizeLabel.setText("Checkpoint size (kbytes):", false, false);
        checkpointSizeText = toolkit.createText(howToRunArea, "");
        gd = new GridData();
        gd.horizontalIndent = 10;
        gd.widthHint = 100;
        checkpointSizeText.setLayoutData(gd);
        chkptDeleteButton = toolkit.createButton(howToRunArea, "Delete Checkpoint", SWT.PUSH);
        chkptDeleteButton.addSelectionListener(new SelectionListener() {

            /* (non-Javadoc)
             * @see org.eclipse.swt.events.SelectionListener#widgetSelected(org.eclipse.swt.events.SelectionEvent)
             */
            public void widgetSelected(SelectionEvent e)
            {
                final IResource[] checkpoints;
                try
                {
                    checkpoints = ModelHelper.getCheckpoints(getConfig(), false);

                    if ((checkpoints != null) && checkpoints.length > 0)
                    {
                        ResourcesPlugin.getWorkspace().run(new IWorkspaceRunnable() {

                            public void run(IProgressMonitor monitor) throws CoreException
                            {
                                checkpoints[0].delete(true, new SubProgressMonitor(monitor, 1));

                            }
                        }, null);
                    }
                } catch (CoreException e1)
                {
                    return;
                }

            }

            /* (non-Javadoc)
             * @see org.eclipse.swt.events.SelectionListener#widgetDefaultSelected(org.eclipse.swt.events.SelectionEvent)
             */
            public void widgetDefaultSelected(SelectionEvent e)
            {
            }
        });
        chkptDeleteButton.addFocusListener(focusListener);
        
        /*
         * Distribution
         */
        //TODO Link help page for distribution mode 
        distributedButton = toolkit.createButton(howToRunArea, "Run in distributed mode", SWT.CHECK);
        gd = new GridData();
        gd.horizontalSpan = 2;

        distributedButton.setLayoutData(gd);
        distributedButton.addSelectionListener(howToRunListener);
		distributedButton.setToolTipText("If checked, state computation will be performed by (remote) workers.");
		distributedButton.addFocusListener(focusListener);
		
		// Additional VM arguments for distributed mode
        FormText distributedLabel = toolkit.createFormText(howToRunArea, true);
        distributedLabel.setText("Additional JVM arguments:", false, false);

        distributedText = toolkit.createText(howToRunArea, "");
        distributedText.setEditable(true);
        distributedText
        .setToolTipText("Optionally pass additional JVM arguments to master TLC process (e.g. -Djava.rmi.server.hostname=ThisHostName)");
        distributedText.addModifyListener(howToRunListener);
        distributedText.addFocusListener(focusListener);
        gd = new GridData();
        gd.horizontalIndent = 10;
        gd.widthHint = 300;
        distributedText.setLayoutData(gd);

        /*
         * pre-fligh script executed prior to distributed TLC (e.g. to start remote workers)
         */
        distributedLabel = toolkit.createFormText(howToRunArea, true);
        distributedLabel.setText("Pre Flight Script:", false, false);

        // non-editable text input
        distributedScriptText = toolkit.createText(howToRunArea, "");
        distributedScriptText.setEditable(true);
        distributedScriptText
        .setToolTipText("Optionally pass a pre-flight script to be run prior to the TLC process (e.g. to start remote workers)");
        distributedScriptText.addModifyListener(howToRunListener);
        gd = new GridData();
        gd.horizontalIndent = 10;
        gd.widthHint = 300;
        distributedScriptText.setLayoutData(gd);
        dm.bindAttribute(LAUNCH_DISTRIBUTED_SCRIPT, distributedScriptText, howToRunPart);

        // skip the left cell in the grid layout
        final Text invisibleText = toolkit.createText(howToRunArea, "");
        invisibleText.setEditable(false);
        invisibleText.setVisible(false);
        invisibleText.setEnabled(false);
        
        // browse button right-aligned
        browseDistributedScriptButton = toolkit.createButton(howToRunArea, "Browse", SWT.PUSH);
        gd = new GridData(GridData.HORIZONTAL_ALIGN_END);
		browseDistributedScriptButton.setLayoutData(gd);
        browseDistributedScriptButton.addSelectionListener(new SelectionListener() {
			/* (non-Javadoc)
			 * @see org.eclipse.swt.events.SelectionListener#widgetSelected(org.eclipse.swt.events.SelectionEvent)
			 */
			public void widgetSelected(SelectionEvent e) {
				// prompt user for a file
				final FileDialog fd = new FileDialog(getSite().getShell(), SWT.OPEN);
				final String oldPath = distributedScriptText.getText();
				fd.setFileName(oldPath);
				
				// use user-provided path as input for script input text box
				final String path = fd.open();
				distributedScriptText.setText((path != null) ? path : oldPath);
			}
			/* (non-Javadoc)
			 * @see org.eclipse.swt.events.SelectionListener#widgetDefaultSelected(org.eclipse.swt.events.SelectionEvent)
			 */
			public void widgetDefaultSelected(SelectionEvent e) {
				//nop
			}
		});

        // deactivate because domain logic is not done yet
        distributedLabel.setVisible(false);
        distributedScriptText.setVisible(false);
        browseDistributedScriptButton.setVisible(false);

        /*
         * run link
         */
        runLink = toolkit.createImageHyperlink(howToRunArea, SWT.NONE);
        runLink.setImage(createRegisteredImage("icons/full/lrun_obj.gif"));
        runLink.addHyperlinkListener(new HyperlinkAdapter() {
            public void linkActivated(HyperlinkEvent e)
            {
                doRun();
            }
        });
        runLink.setText("Run TLC");
        gd = new GridData();
        gd.horizontalSpan = 2;
        gd.widthHint = 200;
        gd.verticalIndent = 20;
        runLink.setLayoutData(gd);
        group.add(runLink);

        generateLink = toolkit.createImageHyperlink(howToRunArea, SWT.NONE);
        generateLink.setImage(createRegisteredImage("icons/full/debugt_obj.gif"));
        generateLink.addHyperlinkListener(new HyperlinkAdapter() {
            public void linkActivated(HyperlinkEvent e)
            {
                doGenerate();
            }
        });
        generateLink.setText("Validate model");
        gd = new GridData();
        gd.horizontalSpan = 2;
        gd.widthHint = 200;
        generateLink.setLayoutData(gd);
        group.add(generateLink);

        // add listeners propagating the changes of the elements to the changes
        // of the
        // parts to the list to be activated after the values has been loaded
        dirtyPartListeners.add(whatIsTheSpecListener);
        dirtyPartListeners.add(whatToCheckListener);
        dirtyPartListeners.add(howToRunListener);
    }

    /**
     * On a refresh, the checkpoint information is re-read 
     */
    public void refresh()
    {
        super.refresh();
        updateCheckpoints();
    }
    
    /**
     * Interpolates based on LinearInterpolation
     */
    private class Interpolator {

    	private final double[] yCoords, xCoords;

    	public Interpolator(double[] x, double[] y) {
    		this.xCoords = x;
    		this.yCoords = y;
    	}

		public double interpolate(double x) {
			for (int i = 1; i < xCoords.length; i++) {
				if (x < xCoords[i]) {
					return yCoords[i] - (yCoords[i] - yCoords[i - 1])
							* (xCoords[i] - x) / (xCoords[i] - xCoords[i - 1]);
				}
			}
			return 0d;
		}
    }
}
