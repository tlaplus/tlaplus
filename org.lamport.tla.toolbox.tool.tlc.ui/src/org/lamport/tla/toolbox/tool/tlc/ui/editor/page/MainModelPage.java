package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import java.util.Arrays;
import java.util.List;
import java.util.Vector;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.forms.HyperlinkGroup;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.IMessageManager;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.widgets.FormText;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.ImageHyperlink;
import org.eclipse.ui.forms.widgets.Section;
import org.eclipse.ui.forms.widgets.TableWrapData;
import org.lamport.tla.toolbox.tool.tlc.launch.IConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;
import org.lamport.tla.toolbox.tool.tlc.model.TypedSet;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.ConstantSectionPart;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.TableSectionPart;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.VSectionPart;
import org.lamport.tla.toolbox.tool.tlc.ui.util.DirtyMarkingListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.util.SemanticHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.IHelpConstants;

import tla2sany.semantic.ModuleNode;

/**
 * Main model page represents information for most users
 * @author Simon Zambrovski
 * @version $Id$
 */
public class MainModelPage extends BasicFormPage implements IConfigurationConstants, IConfigurationDefaults
{
    public static final String ID = "MainModelPage";
    private Button noSpecRadio;
    private Button closedFormulaRadio;
    private Button initNextFairnessRadio;
    private SourceViewer initFormulaSource;
    private SourceViewer nextFormulaSource;
    private SourceViewer fairnessFormulaSource;
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
                    || e.widget == fairnessFormulaSource.getControl())
            {
                noSpecRadio.setSelection(false);
                closedFormulaRadio.setSelection(false);
                initNextFairnessRadio.setSelection(true);
            }
        }
    };

    /**
     * constructs the main model page 
     * @param editor
     */
    public MainModelPage(FormEditor editor)
    {
        super(editor, MainModelPage.ID, "Model Overview");
        this.helpId = IHelpConstants.MAIN_MODEL_PAGE;
        this.imagePath = "icons/full/choice_sc_obj.gif";
    }

    /**
     * Loads data from the model
     */
    protected void loadData() throws CoreException
    {
        int specType = getConfig().getAttribute(MODEL_BEHAVIOR_SPEC_TYPE, MODEL_BEHAVIOR_TYPE_DEFAULT);

        // set up the radio buttons
        switch (specType) {
        case MODEL_BEHAVIOR_TYPE_NO_SPEC:
            this.closedFormulaRadio.setSelection(true);
            break;
        case MODEL_BEHAVIOR_TYPE_SPEC_CLOSED:
            this.closedFormulaRadio.setSelection(true);
            break;
        case MODEL_BEHAVIOR_TYPE_SPEC_INIT_NEXT:
            this.initNextFairnessRadio.setSelection(true);
            break;
        }

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
        String modelFairness = getConfig().getAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_FAIRNESS, EMPTY_STRING);
        Document fairnessDoc = new Document(modelFairness);
        this.fairnessFormulaSource.setDocument(fairnessDoc);

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

        validate();
    }

    public void validate()
    {
        IMessageManager mm = getManagedForm().getMessageManager();
        // clean old messages
        mm.removeAllMessages();
        // make the run possible
        setComplete(true);

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
            ModelHelper.mergeConstantLists(constants, ModelHelper.createConstantsList(rootModuleNode));
            constantTable.setInput(constants);
        }

        // iterate over the constants
        for (int i = 0; i < constants.size(); i++)
        {
            Assignment constant = (Assignment) constants.get(i);

            List values = Arrays.asList(constant.getParams());
            // check list of parameters
            validateListElements(values, constantTable.getTable(), "param1_", "A parameter name", "Constant Assignment");

            // the constant is still in the list
            if (constant.getRight() == null || EMPTY_STRING.equals(constant.getRight()))
            {
                // right side of assignment undefined
                mm.addMessage(constant.getLabel(), "Provide a value for constant " + constant.getLabel(), constant,
                        IMessageProvider.ERROR, constantTable.getTable());
                setComplete(false);
            } else
            {
                if (constant.isSetOfModelValues())
                {
                    TypedSet modelValuesSet = TypedSet.parseSet(constant.getRight());
                    if (modelValuesSet.getValueCount() > 0)
                    {
                        // there were values defined
                        // check if those are numbers?
                        if (modelValuesSet.hasANumberOnlyValue())
                        {
                            mm.addMessage("modelValues1", "A model value can not be an number", modelValuesSet,
                                    IMessageProvider.ERROR, constantTable.getTable());
                            setComplete(false);
                        }
                        // check list of model values
                        validateListElements(modelValuesSet.getValuesAsList(), constantTable.getTable(),
                                "modelValues2_", "A model value", "Constant Assignment");
                    }
                }
            }
        }

        // number of workers
        String numberOfworkers = workers.getText();
        try
        {
            int number = Integer.parseInt(numberOfworkers);
            if (number <= 0)
            {
                mm.addMessage("wrongNumber1", "Number of workers must be a positive integer number", null,
                        IMessageProvider.ERROR, workers);
                setComplete(false);
            } else
            {
                if (number > Runtime.getRuntime().availableProcessors())
                {
                    mm.addMessage("strangeNumber1", "Specified number of workers is " + number
                            + ". The number of CPU Cores available on the system is "
                            + Runtime.getRuntime().availableProcessors()
                            + ".\n It is not advisable that the number of workers exceeds the number of CPU Cores.", null,
                            IMessageProvider.WARNING, workers);
                }
            }
        } catch (NumberFormatException e)
        {
            mm.addMessage("wrongNumber2", "Number of workers must be a positive integer number", null,
                    IMessageProvider.ERROR, workers);
            setComplete(false);
        }

        // spec or no spec
        Control selectedOption = closedFormulaRadio.getSelection() ? closedFormulaRadio : (initNextFairnessRadio
                .getSelection() ? initNextFairnessRadio : null);
        if (selectedOption != null)
        {
            // the user selected to use a spec
            // check if there are variables declared
            if (rootModuleNode != null && rootModuleNode.getVariableDecls().length == 0)
            {
                // no variables => install an error
                mm.addMessage("noVariables", "There were no variables declared in the root module", null,
                        IMessageProvider.ERROR, selectedOption);
                setComplete(false);
            }
        }

        // check if the selected fields are filled
        if (closedFormulaRadio.getSelection() && specSource.getDocument().get().trim().equals(""))
        {
            mm.addMessage("noSpec", "The formula must be provided", null, IMessageProvider.ERROR, specSource
                    .getTextWidget());
            setComplete(false);
        } else if (initNextFairnessRadio.getSelection())
        {
            String init = initFormulaSource.getDocument().get().trim();
            String next = nextFormulaSource.getDocument().get().trim();

            if (init.equals(""))
            {
                mm.addMessage("noInit", "The init formula must be provided", null, IMessageProvider.ERROR,
                        initFormulaSource.getTextWidget());
                setComplete(false);
            }
            if (next.equals(""))
            {
                mm.addMessage("noNext", "The spec formula must be provided", null, IMessageProvider.ERROR,
                        nextFormulaSource.getTextWidget());
                setComplete(false);
            }
        }

        super.validate();
    }

    /**
     * Save data back to config
     */
    public void commit(boolean onSave)
    {
        // closed formula
        String closedFormula = this.specSource.getDocument().get();
        getConfig().setAttribute(MODEL_BEHAVIOR_CLOSED_SPECIFICATION, closedFormula);

        // init formula
        String initFormula = this.initFormulaSource.getDocument().get();
        getConfig().setAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT, initFormula);

        // next formula
        String nextFormula = this.nextFormulaSource.getDocument().get();
        getConfig().setAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT, nextFormula);

        // fairness formula
        String fairnessFormula = this.fairnessFormulaSource.getDocument().get();
        getConfig().setAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_FAIRNESS, fairnessFormula);

        // mode
        int specType = (this.noSpecRadio.getSelection()) ? MODEL_BEHAVIOR_TYPE_NO_SPEC : (this.closedFormulaRadio
                .getSelection() ? MODEL_BEHAVIOR_TYPE_SPEC_CLOSED : MODEL_BEHAVIOR_TYPE_SPEC_INIT_NEXT);

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
     * Creates the UI
     */
    protected void createBodyContent(IManagedForm managedForm)
    {
        int sectionFlags = Section.TITLE_BAR | Section.DESCRIPTION | Section.TREE_NODE;

        FormToolkit toolkit = managedForm.getToolkit();
        Composite body = managedForm.getForm().getBody();

        GridData gd;
        TableWrapData twd;

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
        section = FormHelper.createSectionComposite(left, "What is the spec?", "The behavior specification:", toolkit,
                sectionFlags | Section.EXPANDED, getExpansionListener());
        // only grab horizontal space
        gd = new GridData(GridData.FILL_HORIZONTAL);
        // gd.horizontalSpan = 2;
        section.setLayoutData(gd);

        Composite behaviorArea = (Composite) section.getClient();
        layout = new GridLayout();
        layout.numColumns = 2;
        behaviorArea.setLayout(layout);

        VSectionPart behaviorPart = new VSectionPart(section, this);
        managedForm.addPart(behaviorPart);
        DirtyMarkingListener whatIsTheSpecListener = new DirtyMarkingListener(behaviorPart, true);

        noSpecRadio = toolkit.createButton(behaviorArea, "No Spec (Calculator mode)", SWT.RADIO);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.horizontalSpan = 2;
        noSpecRadio.setLayoutData(gd);
        noSpecRadio.addSelectionListener(whatIsTheSpecListener);

        // closed formula option
        closedFormulaRadio = toolkit.createButton(behaviorArea, "Single formula", SWT.RADIO);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.horizontalSpan = 2;
        closedFormulaRadio.setLayoutData(gd);
        closedFormulaRadio.addSelectionListener(whatIsTheSpecListener);

        // spec
        toolkit.createLabel(behaviorArea, "Spec:");
        specSource = FormHelper.createSourceViewer(toolkit, behaviorArea, SWT.NONE);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 20;
        specSource.getTextWidget().setLayoutData(gd);
        specSource.getTextWidget().addModifyListener(whatIsTheSpecListener);
        specSource.getTextWidget().addModifyListener(widgetActivatingListener);

        // split formula option
        initNextFairnessRadio = toolkit.createButton(behaviorArea, "Init and Next", SWT.RADIO);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.horizontalSpan = 2;
        initNextFairnessRadio.setLayoutData(gd);
        initNextFairnessRadio.addSelectionListener(whatIsTheSpecListener);

        // init
        toolkit.createLabel(behaviorArea, "Init:");
        initFormulaSource = FormHelper.createSourceViewer(toolkit, behaviorArea, SWT.NONE);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 20;
        initFormulaSource.getTextWidget().setLayoutData(gd);
        initFormulaSource.getTextWidget().addModifyListener(whatIsTheSpecListener);
        initFormulaSource.getTextWidget().addModifyListener(widgetActivatingListener);

        // next
        toolkit.createLabel(behaviorArea, "Next:");
        nextFormulaSource = FormHelper.createSourceViewer(toolkit, behaviorArea, SWT.NONE);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 20;
        nextFormulaSource.getTextWidget().setLayoutData(gd);
        nextFormulaSource.getTextWidget().addModifyListener(whatIsTheSpecListener);
        nextFormulaSource.getTextWidget().addModifyListener(widgetActivatingListener);

        // fairness
        toolkit.createLabel(behaviorArea, "Fairness:");
        fairnessFormulaSource = FormHelper.createSourceViewer(toolkit, behaviorArea, SWT.NONE);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 20;
        fairnessFormulaSource.getTextWidget().setLayoutData(gd);
        fairnessFormulaSource.getTextWidget().addModifyListener(whatIsTheSpecListener);
        fairnessFormulaSource.getTextWidget().addModifyListener(widgetActivatingListener);

        // ------------------------------------------
        // what to check
        section = FormHelper.createSectionComposite(left, "What to check?", "List of invariants and properties:",
                toolkit, Section.TITLE_BAR | Section.TREE_NODE | Section.EXPANDED, getExpansionListener());
        // only grab horizontal space
        gd = new GridData(GridData.FILL_HORIZONTAL);
        // gd.horizontalSpan = 2;
        section.setLayoutData(gd);

        Composite toBeCheckedArea = (Composite) section.getClient();
        layout = new GridLayout();
        layout.numColumns = 1;
        toBeCheckedArea.setLayout(layout);

        checkDeadlockButton = toolkit.createButton(toBeCheckedArea, "Deadlock", SWT.CHECK);

        VSectionPart toBeCheckedPart = new VSectionPart(section, this);
        managedForm.addPart(toBeCheckedPart);
        DirtyMarkingListener whatToCheckListener = new DirtyMarkingListener(toBeCheckedPart, true);
        checkDeadlockButton.addSelectionListener(whatToCheckListener);

        // invariants
        TableSectionPart invariantsPart = new TableSectionPart(toBeCheckedArea, "Invariants",
                "Specify invariants to be checked in every state of the specification.", toolkit, sectionFlags, this);
        managedForm.addPart(invariantsPart);
        invariantsTable = invariantsPart.getTableViewer();

        // properties
        TableSectionPart propertiesPart = new TableSectionPart(toBeCheckedArea, "Properties",
                "Specify properties to be checked.", toolkit, sectionFlags, this);
        managedForm.addPart(propertiesPart);
        propertiesTable = propertiesPart.getTableViewer();

        // ------------------------------------------
        // what is the model

        // Constants
        ConstantSectionPart constantsPart = new ConstantSectionPart(right, "What is the model?",
                "Specify the values of the model constants.", toolkit, sectionFlags | Section.EXPANDED, this);
        managedForm.addPart(constantsPart);

        Composite parametersArea = (Composite) constantsPart.getSection().getClient();
        FormText createFormText = toolkit.createFormText(parametersArea, true);
        createFormText.setText("Some advanced features http://www.google.de/", false, true);

        constantTable = constantsPart.getTableViewer();

        gd = new GridData();
        gd.horizontalSpan = 2;
        createFormText.setLayoutData(gd);

        // ------------------------------------------
        // run tab
        section = FormHelper.createSectionComposite(right, "How to run?", "Parameters of the TLC launch.", toolkit,
                sectionFlags | Section.EXPANDED, getExpansionListener());
        gd = new GridData(GridData.FILL_HORIZONTAL);
        section.setLayoutData(gd);

        final Composite howToRunArea = (Composite) section.getClient();
        layout = new GridLayout();
        layout.numColumns = 2;
        howToRunArea.setLayout(layout);

        VSectionPart howToRunPart = new VSectionPart(section, this);
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
        gd.widthHint = 100;
        workers.setLayoutData(gd);

        HyperlinkGroup group = new HyperlinkGroup(howToRunArea.getDisplay());

        // run link
        ImageHyperlink runLink = toolkit.createImageHyperlink(howToRunArea, SWT.NONE);
        runLink.setImage(createRegisteredImage("icons/full/lrun_obj.gif"));
        runLink.addHyperlinkListener(runDebugAdapter);
        runLink.setText("Run TLC");
        runLink.setHref(MODE_RUN);
        gd = new GridData();
        gd.horizontalSpan = 2;
        gd.widthHint = 200;
        runLink.setLayoutData(gd);

        // debug link
        ImageHyperlink debugLink = toolkit.createImageHyperlink(howToRunArea, SWT.NONE);
        debugLink.setImage(createRegisteredImage("icons/full/ldebug_obj.gif"));
        debugLink.addHyperlinkListener(runDebugAdapter);
        debugLink.setText("Debug TLC");
        debugLink.setHref(MODE_DEBUG);
        // TODO enable on debug support
        debugLink.setEnabled(false);
        gd = new GridData();
        gd.horizontalSpan = 2;
        gd.widthHint = 200;
        debugLink.setLayoutData(gd);

        group.add(runLink);
        group.add(debugLink);

        // add listeners propagating the changes of the elements to the changes of the
        // parts to the list to be activated after the values has been loaded
        dirtyPartListeners.add(whatIsTheSpecListener);
        dirtyPartListeners.add(whatToCheckListener);
        dirtyPartListeners.add(howToRunListener);
    }
}
