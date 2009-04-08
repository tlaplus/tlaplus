package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import java.util.List;
import java.util.Vector;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.forms.HyperlinkGroup;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.SectionPart;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.widgets.FormText;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.ImageHyperlink;
import org.eclipse.ui.forms.widgets.Section;
import org.eclipse.ui.forms.widgets.TableWrapData;
import org.lamport.tla.toolbox.tool.tlc.launch.IConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.ui.util.DirtyMarkingListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.util.IHelpConstants;

/**
 * Main model page represents informnation for most users
 * @author Simon Zambrovski
 * @version $Id$
 */
public class MainModelPage extends BasicFormPage implements IConfigurationConstants, IConfigurationDefaults
{
    public static final String ID = "MainModelPage";
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
        boolean isClosedFormula = getConfig().getAttribute(MODEL_BEHAVIOR_IS_CLOSED_SPEC_USED, MODEL_BEHAVIOR_IS_CLOSED_SPEC_USED_DEFAULT);
        
        // set up the radio buttons
        this.closedFormulaRadio.setSelection(isClosedFormula);
        this.initNextFairnessRadio.setSelection(!isClosedFormula);
        
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
        boolean checkDeadlock = getConfig().getAttribute(MODEL_CORRECTNESS_CHECK_DEADLOCK, MODEL_CORRECTNESS_CHECK_DEADLOCK_DEFAULT);
        this.checkDeadlockButton.setSelection(checkDeadlock);
        
        // invariants
        List serializedList= getConfig().getAttribute(MODEL_CORRECTNESS_INVARIANTS, new Vector());
        FormHelper.setSerializedInput(invariantsTable, serializedList);

        // properties
        serializedList = getConfig().getAttribute(MODEL_CORRECTNESS_PROPERTIES, new Vector());
        FormHelper.setSerializedInput(propertiesTable, serializedList);

        
        // constants from the model
        List savedConstants = getConfig().getAttribute(MODEL_PARAMETER_CONSTANTS, new Vector());
        // get the root module
        /*
        ModuleNode moduleNode = ToolboxHandle.getSpecObj().getExternalModuleTable().getRootModule();
        // get the list of constants
        List constants = ModelHelper.createConstantsList(moduleNode);
        */
        // TODO check if new constants exist...
        FormHelper.setSerializedInput(constantTable, savedConstants);

        
    }

    /**
     * Save data back to config
     */
    protected void commit(boolean onSave)
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
        boolean isClosedSpecification = this.closedFormulaRadio.getSelection();
        getConfig().setAttribute(MODEL_BEHAVIOR_IS_CLOSED_SPEC_USED, isClosedSpecification);

        // number of workers
        int numberOfWorkers = LAUNCH_NUMBER_OF_WORKERS_DEFAULT;
        try
        {
            numberOfWorkers = Integer.parseInt(workers.getText());
        } catch (NumberFormatException e) { /* does not matter */ }
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

        SectionPart behaviorPart = new SectionPart(section);
        managedForm.addPart(behaviorPart);
        DirtyMarkingListener whatIsTheSpecListener = new DirtyMarkingListener(behaviorPart, true);

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

        // next
        toolkit.createLabel(behaviorArea, "Next:");
        nextFormulaSource = FormHelper.createSourceViewer(toolkit, behaviorArea, SWT.NONE);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 20;
        nextFormulaSource.getTextWidget().setLayoutData(gd);
        nextFormulaSource.getTextWidget().addModifyListener(whatIsTheSpecListener);

        // fairness
        toolkit.createLabel(behaviorArea, "Fairness:");
        fairnessFormulaSource = FormHelper.createSourceViewer(toolkit, behaviorArea, SWT.NONE);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 20;
        fairnessFormulaSource.getTextWidget().setLayoutData(gd);
        fairnessFormulaSource.getTextWidget().addModifyListener(whatIsTheSpecListener);

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

        SectionPart toBeCheckedPart = new SectionPart(section);
        managedForm.addPart(toBeCheckedPart);
        DirtyMarkingListener whatToCheckListener = new DirtyMarkingListener(toBeCheckedPart, true);
        checkDeadlockButton.addSelectionListener(whatToCheckListener);

        // invariants
        TableSectionPart invariantsPart = new TableSectionPart(toBeCheckedArea, "Invariants",
                "Specify invariants to be checked in every state of the specification.", toolkit, sectionFlags);
        managedForm.addPart(invariantsPart);
        invariantsTable = invariantsPart.getTableViewer();

        // properties
        TableSectionPart propertiesPart = new TableSectionPart(toBeCheckedArea, "Properties",
                "Specify properties to be checked.", toolkit, sectionFlags);
        managedForm.addPart(propertiesPart);
        propertiesTable = propertiesPart.getTableViewer();

        
        // ------------------------------------------
        // what is the model

        // Constants
        ConstantSectionPart constantsPart = new ConstantSectionPart(right, "What is the model?",
                "Specify the values of the model constants.", toolkit, sectionFlags | Section.EXPANDED);
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

        SectionPart howToRunPart = new SectionPart(section);
        managedForm.addPart(howToRunPart);

        DirtyMarkingListener howToRunListener = new DirtyMarkingListener(howToRunPart, true);

        // label workers
        FormText workersLabel = toolkit.createFormText(howToRunArea, true);
        workersLabel.setText("Number of workers:", false, false);

        // field workers
        workers = toolkit.createText(howToRunArea, "1");
        workers.addModifyListener(howToRunListener);
        gd = new GridData();
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
        ignoringListeners.add(whatIsTheSpecListener);
        ignoringListeners.add(whatToCheckListener);
        ignoringListeners.add(howToRunListener);
    }
}
