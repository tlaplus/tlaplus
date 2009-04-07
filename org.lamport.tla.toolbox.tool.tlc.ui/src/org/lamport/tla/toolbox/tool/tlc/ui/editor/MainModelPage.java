package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.SectionPart;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.widgets.FormText;
import org.eclipse.ui.forms.widgets.FormToolkit;
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
    }

    /**
     * Save data back to config
     */
    protected void commit(boolean onSave)
    {

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

        Composite left = toolkit.createComposite(body);
        twd = new TableWrapData(TableWrapData.FILL_GRAB);
        twd.grabHorizontal = true;
        left.setLayout(new GridLayout(1, false));
        left.setLayoutData(twd);

        Composite right = toolkit.createComposite(body);
        twd = new TableWrapData(TableWrapData.FILL_GRAB);
        twd.grabHorizontal = true;
        right.setLayoutData(twd);
        right.setLayout(new GridLayout(1, false));

        
        // ------------------------------------------
        // run tab
        Section section = FormHelper.createSectionComposite(left, "How to run?", "The behavior specification:",
                toolkit, sectionFlags | Section.EXPANDED,
                getExpansionListener());
        // only grab horizontal space
        gd = new GridData(GridData.FILL_HORIZONTAL);
        section.setLayoutData(gd);

        Composite howToRunArea = (Composite) section.getClient();
        GridLayout layout = new GridLayout();
        layout.numColumns = 2;
        howToRunArea.setLayout(layout);

        
        
        // ------------------------------------------
        // behavior tab
        section = FormHelper.createSectionComposite(left, "What is the spec?", "The behavior specification:",
                toolkit, sectionFlags | Section.EXPANDED,
                getExpansionListener());
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
        DirtyMarkingListener behaviorListener = new DirtyMarkingListener(behaviorPart, true);

        // closed formula option
        closedFormulaRadio = toolkit.createButton(behaviorArea, "Single formula", SWT.RADIO);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.horizontalSpan = 2;
        closedFormulaRadio.setLayoutData(gd);

        // spec
        toolkit.createLabel(behaviorArea, "Spec:");
        specSource = FormHelper.createSourceViewer(toolkit, behaviorArea, SWT.NONE);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 20;
        specSource.getTextWidget().setLayoutData(gd);

        // split formula option
        initNextFairnessRadio = toolkit.createButton(behaviorArea, "Init and Next", SWT.RADIO);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.horizontalSpan = 2;
        initNextFairnessRadio.setLayoutData(gd);

        // init
        toolkit.createLabel(behaviorArea, "Init:");
        initFormulaSource = FormHelper.createSourceViewer(toolkit, behaviorArea, SWT.NONE);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 20;
        initFormulaSource.getTextWidget().setLayoutData(gd);

        // next
        toolkit.createLabel(behaviorArea, "Next:");
        nextFormulaSource = FormHelper.createSourceViewer(toolkit, behaviorArea, SWT.NONE);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 20;
        nextFormulaSource.getTextWidget().setLayoutData(gd);

        // fairness
        toolkit.createLabel(behaviorArea, "Fairness:");
        fairnessFormulaSource = FormHelper.createSourceViewer(toolkit, behaviorArea, SWT.NONE);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 20;
        fairnessFormulaSource.getTextWidget().setLayoutData(gd);

        // ------------------------------------------
        // what to check
        section = FormHelper.createSectionComposite(left, "What to check?", "List of invariants and properties:",
                toolkit, Section.TITLE_BAR | Section.TREE_NODE | Section.EXPANDED,
                getExpansionListener());
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
        DirtyMarkingListener toBeCheckedListener = new DirtyMarkingListener(toBeCheckedPart, true);

        // invariants
        TableSectionPart invariantsPart = new TableSectionPart(toBeCheckedArea, "Invariants",
                "Specify invariants to be checked in every state of the specification.", toolkit, sectionFlags );
        managedForm.addPart(invariantsPart);

        // properties
        TableSectionPart propertiesPart = new TableSectionPart(toBeCheckedArea, "Properties",
                "Specify properties to be checked.", toolkit, sectionFlags );
        managedForm.addPart(propertiesPart);

        // ------------------------------------------
        // model parameters

        // Constants
        ConstantSectionPart constantsPart = new ConstantSectionPart(right, "Constants instantiation",
                "Specify the values of the model constants.", toolkit, sectionFlags);
        managedForm.addPart(constantsPart);

        Composite parametersArea = (Composite) constantsPart.getSection().getClient();
        // layout = new GridLayout();
        // parametersArea.setLayout(layout);
        FormText createFormText = toolkit.createFormText(parametersArea, true);
        createFormText.setText("Some advanced features http://www.google.de/", false, true);
        
        gd = new GridData();
        gd.horizontalSpan = 2;
        createFormText.setLayoutData(gd);
        

        /*
        SectionPart parametersPart = new SectionPart(section);
        managedForm.addPart(parametersPart);
        DirtyMarkingListener parametersListener = new DirtyMarkingListener(parametersPart, true);
        */

        // add listeners propagating the changes of the elements to the changes of the
        // parts to the list to be activated after the values has been loaded
        ignoringListeners.add(behaviorListener);
        ignoringListeners.add(toBeCheckedListener);
    }
}
