package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import java.util.Arrays;
import java.util.List;
import java.util.Vector;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.PartInitException;
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
import org.lamport.tla.toolbox.tool.tlc.ui.util.DirtyMarkingListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.util.SemanticHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.IHelpConstants;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.ModuleNode;

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

    // Test code
    // remembers if the spec had variables the last time the page was validated.
    // private boolean hasVariables = false;
    // private boolean lastSeenHasVariables = false;

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

    /**
     * constructs the main model page 
     * @param editor
     */
    public MainModelPage(FormEditor editor)
    {
        super(editor, MainModelPage.ID, MainModelPage.TITLE);
        this.helpId = IHelpConstants.MAIN_MODEL_PAGE;
        this.imagePath = "icons/full/choice_sc_obj.gif";
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

        // check deadlock
        boolean checkDeadlock = getConfig().getAttribute(MODEL_CORRECTNESS_CHECK_DEADLOCK,
                MODEL_CORRECTNESS_CHECK_DEADLOCK_DEFAULT);
        this.checkDeadlockButton.setSelection(checkDeadlock);

        // invariants
        List serializedList = getConfig().getAttribute(MODEL_CORRECTNESS_INVARIANTS, new Vector());
        FormHelper.setSerializedInput(invariantsTable, serializedList);

        // properties
        serializedList = getConfig().getAttribute(MODEL_CORRECTNESS_PROPERTIES, new Vector());
        FormHelper.setSerializedInput(propertiesTable, serializedList);

        // constants from the model
        List savedConstants = getConfig().getAttribute(MODEL_PARAMETER_CONSTANTS, new Vector());
        FormHelper.setSerializedInput(constantTable, savedConstants);

        // recover from the checkpoint
        boolean recover = getConfig().getAttribute(LAUNCH_RECOVER, LAUNCH_RECOVER_DEFAULT);
        this.checkpointButton.setSelection(recover);
    }

    // TODO remove
    // The field countXX and the commented-out code in which it appears in the following method
    // were a test that Dan and LL did in September 2009 to try out a method for dynamically
    // modifying the number of pages that are shown in order to provide a more sensible interface
    // when the spec has no variables.
//    private int countXX = 0;

    public void validatePage(boolean switchToErrorPage)
    {
        if (getManagedForm() == null)
        {
            return;
        }
        // TODO remove
        // The following approach has the potential problem that it loses
        // some of the data in the model. If we want to use this approach
        // to control the display of the get-constants area, we have to
        // be careful and check things carefully because weird things
        // seem to happen.
//        countXX++;
//        System.out.println("countXX = " + countXX);
//        if (countXX == 60000)
//        {
//            countXX++;
//            ModelEditor ourFavoriteEditor = (ModelEditor) this.getEditor();
//            ourFavoriteEditor.removePage(0);
//            System.out.println("Page removed");
//            MainModelPage newPage = new MainModelPage(ourFavoriteEditor);
//            try
//            {
//                ourFavoriteEditor.addPage(0, newPage);
//                ourFavoriteEditor.setUpPage(newPage, 0);
//            } catch (PartInitException e)
//            {
//                // TODO Auto-generated catch block
//                TLCUIActivator.logError("Error initializing editor", e);
//                e.printStackTrace();
//            }
//            // newPage.validate(); // Dan: I thought this needed to be added,
//            // but now I think that it's harmful.
//
//            // both the following statements are needed to give make newPage
//            // the one that's shown.
//            ourFavoriteEditor.setActivePage(newPage.getId());
//            newPage.setFocus();
//            System.out.println("Page re-added");
//            // System.out.println("Here goes.  Closing editor.");
//            // ModelEditor ourFavoriteEditor = (ModelEditor) this.getEditor();
//            // IFile launchFile =
//            // ourFavoriteEditor.getResource(IFileProvider.TYPE_MODEL);
//            // ourFavoriteEditor.close(false);
//            // System.out.println("launchFile.getName = " +
//            // launchFile.getName());
//            // // UIHelper.openEditor(OpenModelHandler.EDITOR_ID, launchFile);
//            // try {
//            // UIHelper.getActiveWindow().getActivePage().openEditor(new
//            // FileEditorInput(launchFile),
//            // OpenModelHandler.EDITOR_ID, true);
//            // }
//            // catch (PartInitException e) {
//            // // TODO Auto-generated catch block
//            // e.printStackTrace();
//            // }
//            // System.out.println("Relaunched the editor");
//        }
//        // SOME RANDOM TEST
//        // if (hasVariables !=
//        // (SemanticHelper.getRootModuleNode().getVariableDecls().length != 0))
//        // {
//        // hasVariables = !hasVariables;
//        // createBodyContent(getManagedForm());
//        // System.out.println("We got here in our random test." + count++);
//        // }

        DataBindingManager dm = getDataBindingManager();
        IMessageManager mm = getManagedForm().getMessageManager();

        // delete the messages
        resetAllMessages(false);

        // getting the root module node of the spec
        // this can be null!
        ModuleNode rootModuleNode = SemanticHelper.getRootModuleNode();

        // setup the names from the current page
        getLookupHelper().resetModelNames(this);

        // constants in the table
        List constants = (List) constantTable.getInput();
        // merge constants with currently defined in the specobj, if any
        if (rootModuleNode != null)
        {
            List toDelete = ModelHelper.mergeConstantLists(constants, ModelHelper.createConstantsList(rootModuleNode));
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

        boolean symmetryUsed = false;
        // iterate over the constants
        for (int i = 0; i < constants.size(); i++)
        {
            Assignment constant = (Assignment) constants.get(i);

            List values = Arrays.asList(constant.getParams());
            // check parameters
            validateId(MODEL_PARAMETER_CONSTANTS, values, "param1_", "A parameter name");

            // the constant is still in the list
            if (constant.getRight() == null || EMPTY_STRING.equals(constant.getRight()))
            {
                // right side of assignment undefined
                mm.addMessage(constant.getLabel(), "Provide a value for constant " + constant.getLabel(), constant,
                        IMessageProvider.ERROR, UIHelper.getWidget(dm.getAttributeControl(MODEL_PARAMETER_CONSTANTS)));
                setComplete(false);
                expandSection(dm.getSectionForAttribute(MODEL_PARAMETER_CONSTANTS));

            } else
            {
                if (constant.isSetOfModelValues())
                {
                    if (symmetryUsed && constant.isSymmetricalSet())
                    {
                        // symmetry can be used for only one set of model values
                        mm.addMessage(constant.getLabel(), "Only one symmetrical set of model values is allowed",
                                constant, IMessageProvider.ERROR, UIHelper.getWidget(dm
                                        .getAttributeControl(MODEL_PARAMETER_CONSTANTS)));
                        setComplete(false);
                        expandSection(dm.getSectionForAttribute(MODEL_PARAMETER_CONSTANTS));
                    } else
                    {
                        if (constant.isSymmetricalSet())
                        {
                            symmetryUsed = true;
                        }
                    }
                    TypedSet modelValuesSet = TypedSet.parseSet(constant.getRight());
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

                        List mvList = modelValuesSet.getValuesAsList();
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
                                mm.addMessage(value, "The toolbox cannot handle the model value " + value + ".",
                                        constant, IMessageProvider.ERROR, widget);
                            }
                        }
                    }
                }
            }

            // the constant identifier is a config file keyword
            if (SemanticHelper.isConfigFileKeyword(constant.getLabel()))
            {
                mm.addMessage(constant.getLabel(), "The toolbox cannot handle the constant identifier "
                        + constant.getLabel() + ".", constant, IMessageProvider.ERROR, UIHelper.getWidget(dm
                        .getAttributeControl(MODEL_PARAMETER_CONSTANTS)));
            }
        }

        
        // iterate over the constants again, and check if the parameters are used as Model Values 
        for (int i = 0; i < constants.size(); i++)
        {
            Assignment constant = (Assignment) constants.get(i);
            List values = Arrays.asList(constant.getParams());
            // check list of parameters
            validateUsage(MODEL_PARAMETER_CONSTANTS, values, "param1_", "A parameter name", "Constant Assignment", false);
        }
        
        
        // number of workers
        String numberOfworkers = workers.getText();
        try
        {
            int number = Integer.parseInt(numberOfworkers);
            if (number <= 0)
            {
                mm.addMessage("wrongNumber1", "Number of workers must be a positive integer number", null,
                        IMessageProvider.ERROR, UIHelper.getWidget(dm.getAttributeControl(LAUNCH_NUMBER_OF_WORKERS)));
                setComplete(false);
                expandSection(SEC_HOW_TO_RUN);
            } else
            {
                if (number > Runtime.getRuntime().availableProcessors())
                {
                    mm.addMessage("strangeNumber1", "Specified number of workers is " + number
                            + ". The number of CPU Cores available on the system is "
                            + Runtime.getRuntime().availableProcessors()
                            + ".\n It is not advisable that the number of workers exceeds the number of CPU Cores.",
                            null, IMessageProvider.WARNING, UIHelper.getWidget(dm
                                    .getAttributeControl(LAUNCH_NUMBER_OF_WORKERS)));
                    expandSection(SEC_HOW_TO_RUN);
                }
            }
        } catch (NumberFormatException e)
        {
            mm.addMessage("wrongNumber2", "Number of workers must be a positive integer number", null,
                    IMessageProvider.ERROR, UIHelper.getWidget(dm.getAttributeControl(LAUNCH_NUMBER_OF_WORKERS)));
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
                mm.addMessage("noChckpoint", "No chekpoint data found", null, IMessageProvider.ERROR, UIHelper
                        .getWidget(dm.getAttributeControl(LAUNCH_RECOVER)));
                setComplete(false);
                expandSection(SEC_HOW_TO_RUN);
            }
        }

        // The following code added by LL and DR on 10 Sep 2009.
        // Reset the enabling and selection of spec type depending on the number number
        // of variables in the spec.
        // This code needs to be modified when we modify the model launcher
        // to allow the No Spec option to be selected when there are variables.
        //
        if (rootModuleNode != null)
        {
            if (rootModuleNode.getVariableDecls().length == 0)
            {
                setHasVariables(false);
                // set selection to the NO SPEC field
                setSpecSelection(MODEL_BEHAVIOR_TYPE_NO_SPEC);
            } else
            {
                setHasVariables(true);

                // no spec has been selected, set the selection to the default
                if (noSpecRadio.getSelection()) 
                {
                    // set selection to the default
                    setSpecSelection(MODEL_BEHAVIOR_TYPE_DEFAULT);
                }
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
        if (closedFormulaRadio.getSelection() && specSource.getDocument().get().trim().equals(""))
        {
            mm.addMessage("noSpec", "The formula must be provided", null, IMessageProvider.ERROR, UIHelper.getWidget(dm
                    .getAttributeControl(MODEL_BEHAVIOR_CLOSED_SPECIFICATION)));
            setComplete(false);
            expandSection(dm.getSectionForAttribute(MODEL_BEHAVIOR_CLOSED_SPECIFICATION));
        } else if (initNextFairnessRadio.getSelection())
        {
            String init = initFormulaSource.getDocument().get().trim();
            String next = nextFormulaSource.getDocument().get().trim();

            if (init.equals(""))
            {
                mm.addMessage("noInit", "The Init formula must be provided", null, IMessageProvider.ERROR, UIHelper
                        .getWidget(dm.getAttributeControl(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT)));
                setComplete(false);
                expandSection(dm.getSectionForAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT));
            }
            if (next.equals(""))
            {
                mm.addMessage("noNext", "The Next formula must be provided", null, IMessageProvider.ERROR, UIHelper
                        .getWidget(dm.getAttributeControl(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT)));
                setComplete(false);
                expandSection(dm.getSectionForAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT));
            }
        }

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

        // no variables = no spec
        this.noSpecRadio.setEnabled(!hasVariables);
        // if there are variables, the spec must be provided
        this.closedFormulaRadio.setEnabled(hasVariables);
        this.initNextFairnessRadio.setEnabled(hasVariables);

        // the input fields are eneabled only if there are variables
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

        // recover from deadlock
        boolean recover = this.checkpointButton.getSelection();
        getConfig().setAttribute(LAUNCH_RECOVER, recover);

        // check deadlock
        boolean checkDeadlock = this.checkDeadlockButton.getSelection();
        getConfig().setAttribute(MODEL_CORRECTNESS_CHECK_DEADLOCK, checkDeadlock);

        // invariants
        List serializedList = FormHelper.getSerializedInput(invariantsTable);
        getConfig().setAttribute(MODEL_CORRECTNESS_INVARIANTS, serializedList);

        // properties
        serializedList = FormHelper.getSerializedInput(propertiesTable);
        getConfig().setAttribute(MODEL_CORRECTNESS_PROPERTIES, serializedList);

        // constants
        List constants = FormHelper.getSerializedInput(constantTable);
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
            checkpoints = ModelHelper.getCheckpoints(getConfig());
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
    }

    // TODO remove
    private int ccount = 0;

    /**
     * Creates the UI
     * This method is called to create the widgets and arrange them on the page
     */
    protected void createBodyContent(IManagedForm managedForm)
    {
        DataBindingManager dm = getDataBindingManager();
        int sectionFlags = Section.TITLE_BAR | Section.DESCRIPTION | Section.TREE_NODE;
        // TODO remove
        System.out.println("Call of createBodyContent number " + ccount++ + ", Model editor count = ");
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
        section = FormHelper.createSectionComposite(left, "What is the behavior spec?", "The behavior specification:",
                toolkit, sectionFlags | Section.EXPANDED, getExpansionListener());
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

        // DR & LL changed the order of the two ways of giving the spec and
        // re-added the no-spec option on 10 Sep 2009.

        // split formula option
        initNextFairnessRadio = toolkit.createButton(behaviorArea, "Init and Next", SWT.RADIO);

        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.horizontalSpan = 2;
        initNextFairnessRadio.setLayoutData(gd);
        initNextFairnessRadio.addSelectionListener(whatIsTheSpecListener);

        // init
        toolkit.createLabel(behaviorArea, "Init:");
        initFormulaSource = FormHelper.createFormsSourceViewer(toolkit, behaviorArea, SWT.NONE | SWT.SINGLE);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 18;
        initFormulaSource.getTextWidget().setLayoutData(gd);
        initFormulaSource.getTextWidget().addModifyListener(whatIsTheSpecListener);
        initFormulaSource.getTextWidget().addModifyListener(widgetActivatingListener);
        dm.bindAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT, initFormulaSource, behaviorPart);

        // next
        toolkit.createLabel(behaviorArea, "Next:");
        nextFormulaSource = FormHelper.createFormsSourceViewer(toolkit, behaviorArea, SWT.NONE | SWT.SINGLE);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 18;
        nextFormulaSource.getTextWidget().setLayoutData(gd);
        nextFormulaSource.getTextWidget().addModifyListener(whatIsTheSpecListener);
        nextFormulaSource.getTextWidget().addModifyListener(widgetActivatingListener);
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
        closedFormulaRadio = toolkit.createButton(behaviorArea, "Single formula", SWT.RADIO);
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

        // RANDOM TEST CODE THAT DOESN"T SEEM TO DO ANYTHING
        // left.getChildren()[0].setBounds(0, 0, 0, 0);
        // left.getChildren()[0].setVisible(hasVariables);
        // System.out.println("setVisible(...) " + count++);

        // ------------------------------------------
        // what to check
        section = FormHelper.createSectionComposite(left, "What to check?", "List of invariants and properties:",
                toolkit, sectionFlags | Section.EXPANDED, getExpansionListener());
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

        // invariants
        ValidateableTableSectionPart invariantsPart = new ValidateableTableSectionPart(toBeCheckedArea, "Invariants",
                "Specify invariants to be checked in every state of the specification.", toolkit, sectionFlags, this,
                SEC_WHAT_TO_CHECK_INVARIANTS);
        managedForm.addPart(invariantsPart);
        invariantsTable = invariantsPart.getTableViewer();
        dm.bindAttribute(MODEL_CORRECTNESS_INVARIANTS, invariantsTable, invariantsPart);

        // properties
        ValidateableTableSectionPart propertiesPart = new ValidateableTableSectionPart(toBeCheckedArea, "Properties",
                "Specify properties to be checked.", toolkit, sectionFlags, this, SEC_WHAT_TO_CHECK_PROPERTIES);
        managedForm.addPart(propertiesPart);
        propertiesTable = propertiesPart.getTableViewer();
        dm.bindAttribute(MODEL_CORRECTNESS_PROPERTIES, propertiesTable, propertiesPart);

        // ------------------------------------------
        // what is the model

        // Constants
        ValidateableConstantSectionPart constantsPart = new ValidateableConstantSectionPart(right,
                "What is the model?", "Specify the values of the model constants.", toolkit, sectionFlags
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
        labelText.setText("Some advanced features:", false, false);

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
        section = FormHelper.createSectionComposite(right, "How to run?", "Parameters of the TLC launch.", toolkit,
                sectionFlags, getExpansionListener());
        gd = new GridData(GridData.FILL_HORIZONTAL);
        section.setLayoutData(gd);

        final Composite howToRunArea = (Composite) section.getClient();
        group = new HyperlinkGroup(howToRunArea.getDisplay());
        layout = new GridLayout(2, false);
        howToRunArea.setLayout(layout);

        ValidateableSectionPart howToRunPart = new ValidateableSectionPart(section, this, SEC_HOW_TO_RUN);
        managedForm.addPart(howToRunPart);

        DirtyMarkingListener howToRunListener = new DirtyMarkingListener(howToRunPart, true);

        // label workers
        FormText workersLabel = toolkit.createFormText(howToRunArea, true);
        workersLabel.setText("Number of workers:", false, false);

        // field workers
        workers = toolkit.createText(howToRunArea, "1");
        workers.addModifyListener(howToRunListener);
        gd = new GridData();
        gd.horizontalIndent = 10;
        gd.widthHint = 15;
        workers.setLayoutData(gd);

        dm.bindAttribute(LAUNCH_NUMBER_OF_WORKERS, workers, howToRunPart);

        // run from the checkpoint
        checkpointButton = toolkit.createButton(howToRunArea, "Recover from checkpoint", SWT.CHECK);
        gd = new GridData();
        gd.horizontalSpan = 2;
        gd.verticalIndent = 20;

        checkpointButton.setLayoutData(gd);
        checkpointButton.addSelectionListener(howToRunListener);

        FormText chkpointIdLabel = toolkit.createFormText(howToRunArea, true);
        chkpointIdLabel.setText("Checkpoint ID:", false, false);

        checkpointIdText = toolkit.createText(howToRunArea, "");
        checkpointIdText.setEditable(false);
        gd = new GridData();
        gd.horizontalIndent = 10;
        gd.widthHint = 100;
        checkpointIdText.setLayoutData(gd);
        dm.bindAttribute(LAUNCH_RECOVER, checkpointButton, howToRunPart);

        // run link
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

        // TODO enable on debug support
        // debug link
        /*
         * ImageHyperlink debugLink = toolkit.createImageHyperlink(howToRunArea,
         * SWT.NONE);
         * debugLink.setImage(createRegisteredImage("icons/full/ldebug_obj.gif"
         * )); debugLink.addHyperlinkListener(new HyperlinkAdapter() { public
         * void linkActivated(HyperlinkEvent e) { // doDebug(); } });
         * debugLink.setText("Debug TLC"); debugLink.setEnabled(false); gd = new
         * GridData(); gd.horizontalSpan = 2; gd.widthHint = 200;
         * debugLink.setLayoutData(gd); group.add(debugLink);
         */
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

}
