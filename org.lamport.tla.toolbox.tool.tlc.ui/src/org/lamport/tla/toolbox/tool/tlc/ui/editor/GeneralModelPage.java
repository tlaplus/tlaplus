package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.jface.dialogs.MessageDialog;
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
import org.eclipse.ui.forms.events.HyperlinkAdapter;
import org.eclipse.ui.forms.events.HyperlinkEvent;
import org.eclipse.ui.forms.widgets.FormText;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.ImageHyperlink;
import org.eclipse.ui.forms.widgets.Section;
import org.eclipse.ui.forms.widgets.TableWrapData;
import org.eclipse.ui.forms.widgets.TableWrapLayout;
import org.lamport.tla.toolbox.tool.tlc.launch.IConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.ui.util.DirtyMarkingListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.IHelpConstants;

/**
 * First page of the model editor, representing the summary
 * @author Simon Zambrovski
 * @version $Id$
 */
public class GeneralModelPage extends BasicFormPage implements IConfigurationConstants, IConfigurationDefaults
{

    public static final String ID = "GeneralModelPage";
    private Text specName;
    private Text modelName;
    private Text workers;
    private Text coverage;
    private Text depth;
    private Text seed;
    private Text aril;
    private Button simulationOption;
    private Button mcDFIDOption;
    private Button mcOption;
    private Text dfiddepth;

    public GeneralModelPage(FormEditor editor)
    {
        super(editor, GeneralModelPage.ID, "Model Overview");
        this.helpId = IHelpConstants.GENERAL_MODEL_PAGE;
        this.imagePath = "icons/full/choice_sc_obj.gif";
    }

    /**
     * Load data from the config
     */
    protected void loadData() throws CoreException
    {
        mcOption.setSelection(true);

        specName.setText(getConfig().getAttribute(SPEC_NAME, EMPTY_STRING));
        modelName.setText(getConfig().getAttribute(MODEL_NAME, EMPTY_STRING));

        workers.setText("" + getConfig().getAttribute(LAUNCH_NUMBER_OF_WORKERS, LAUNCH_NUMBER_OF_WORKERS_DEFAULT));
    }

    /**
     * Save data back to config
     */
    protected void commit(boolean onSave)
    {
        int numberOfWorkers = LAUNCH_NUMBER_OF_WORKERS_DEFAULT;
        try
        {
            numberOfWorkers = Integer.parseInt(workers.getText());
        } catch (NumberFormatException e)
        {
            // does not matter
        }
        // save the number of workers
        getConfig().setAttribute(LAUNCH_NUMBER_OF_WORKERS, numberOfWorkers);
        
        super.commit(onSave);
    }

    /**
     * Creates the UI
     */
    protected void createBodyContent(IManagedForm managedForm)
    {
        FormToolkit toolkit = managedForm.getToolkit();
        Composite body = managedForm.getForm().getBody();

        Composite left = toolkit.createComposite(body);
        left.setLayout(new TableWrapLayout());

        createSummarySection(toolkit, left);
        createLaunchSection(toolkit, left);

        Composite right = toolkit.createComposite(body);
        TableWrapData twd = new TableWrapData(TableWrapData.FILL_GRAB);
        twd.grabHorizontal = true;
        right.setLayoutData(twd);
        right.setLayout(new TableWrapLayout());
        createAdvancedSection(toolkit, right, managedForm);
    }

    /**
     * @param toolkit
     * @param body
     */
    private void createSummarySection(FormToolkit toolkit, Composite body)
    {
        TableWrapData twd;
        GridData gd;
        // summary section
        Section section = FormHelper.createSectionComposite(body, "Model definition",
                "This section provides summary about the model definition", toolkit);
        Composite area = (Composite) section.getClient();
        area.setLayout(new GridLayout(2, false));
        // layout
        twd = new TableWrapData();
        twd.grabHorizontal = true;
        twd.grabVertical = false;
        section.setLayoutData(twd);

        // label spec name
        FormText specNameLabel = toolkit.createFormText(area, true);
        specNameLabel.setText("Specification name:", false, false);

        // field spec name
        specName = toolkit.createText(area, "");
        gd = new GridData();
        gd.widthHint = 200;
        specName.setLayoutData(gd);
        specName.setEditable(false);

        // label model name
        FormText modelNameLabel = toolkit.createFormText(area, true);
        modelNameLabel.setText("Configuration name:", false, false);

        // field model name
        modelName = toolkit.createText(area, "");
        gd = new GridData();
        gd.widthHint = 200;
        modelName.setLayoutData(gd);
        modelName.setEditable(false);
    }

    /**
     * @param toolkit
     * @param body
     */
    private void createAdvancedSection(FormToolkit toolkit, Composite body, IManagedForm managedForm)
    {
        TableWrapData twd;
        GridData gd;
        // advanced section
        Section section = FormHelper.createSectionComposite(body, "Advanced configuration",
                "This section provides advanced options for the model checker run.", toolkit);
        Composite area = (Composite) section.getClient();
        area.setLayout(new GridLayout(2, false));
        // layout
        twd = new TableWrapData();
        twd.grabHorizontal = true;
        twd.grabVertical = false;
        section.setLayoutData(twd);

        SectionPart advancedPart = new SectionPart(section);
        managedForm.addPart(advancedPart);

        DirtyMarkingListener advancedListener = new DirtyMarkingListener(advancedPart, true);
        
        // label modelname
        FormText workersLabel = toolkit.createFormText(area, true);
        workersLabel.setText("Number of workers:", false, false);

        // field workers
        workers = toolkit.createText(area, "1");
        workers.addModifyListener(advancedListener);
        gd = new GridData();
        gd.widthHint = 100;
        workers.setLayoutData(gd);

        // label coverage
        FormText coverageLabel = toolkit.createFormText(area, true);
        coverageLabel.setText("Report coverage each (sec.):", false, false);

        // field coverage
        coverage = toolkit.createText(area, "0");
        coverage.addModifyListener(advancedListener);
        gd = new GridData();
        gd.widthHint = 100;
        coverage.setLayoutData(gd);

        // add the ignoring listeners
        ignoringListeners.add(advancedListener);
    }

    /**
     * @param toolkit
     * @param body
     */
    private void createLaunchSection(FormToolkit toolkit, final Composite body)
    {
        TableWrapData twd;
        GridData gd;

        // launch section
        Section section = FormHelper.createSectionComposite(body, "Launching", "Launch the model checker:", toolkit);
        Composite area = (Composite) section.getClient();
        area.setLayout(new GridLayout(2, false));
        // layout
        twd = new TableWrapData();
        twd.grabHorizontal = false;
        twd.grabVertical = false;
        section.setLayoutData(twd);

        HyperlinkGroup group = new HyperlinkGroup(body.getDisplay());
        // run link
        ImageHyperlink runLink = toolkit.createImageHyperlink(area, SWT.NONE);
        runLink.setImage(createRegisteredImage("icons/full/lrun_obj.gif"));
        runLink.addHyperlinkListener(new HyperlinkAdapter() {

            public void linkActivated(HyperlinkEvent e)
            {
                ILaunchConfigurationWorkingCopy config = getConfig();
                if (config.isDirty())
                {
                    boolean confirmDirty = MessageDialog.openConfirm(body.getShell(), "Dirty editors",
                            "Press ok to save and proceed or press cancel to abort the launch");
                    if (confirmDirty)
                    {
                        ModelHelper.doSaveConfigurationCopy(config);
                    } else
                    {
                        return;
                    }
                }

                try
                {
                    System.out.println("Run clicked");
                    config.launch(TLCModelLaunchDelegate.MODE_MODELCHECK, null, false);
                    System.out.println("Finished");
                } catch (CoreException e1)
                {
                    // TODO Auto-generated catch block
                    e1.printStackTrace();
                }

            }
        });
        runLink.setText("Run TLC");
        gd = new GridData();
        gd.horizontalSpan = 2;
        gd.widthHint = 200;
        runLink.setLayoutData(gd);

        // debug link
        ImageHyperlink debugLink = toolkit.createImageHyperlink(area, SWT.NONE);
        debugLink.setImage(createRegisteredImage("icons/full/ldebug_obj.gif"));
        debugLink.addHyperlinkListener(new HyperlinkAdapter() {
            public void linkActivated(HyperlinkEvent e)
            {
                System.out.println("Debug clicked");
            }
        });
        debugLink.setText("Debug TLC");
        gd = new GridData();
        gd.horizontalSpan = 2;
        gd.widthHint = 200;
        runLink.setLayoutData(gd);

        group.add(runLink);
        group.add(debugLink);

        createAdvancedLaunchSection(toolkit, area);
    }

    /**
     * @param toolkit
     * @param area
     */
    private Section createAdvancedLaunchSection(FormToolkit toolkit, Composite parent)
    {
        GridData gd;

        // advanced section
        Section advancedSection = FormHelper.createSectionComposite(parent, "Launching details", "", toolkit,
                Section.CLIENT_INDENT | Section.TREE_NODE | Section.COMPACT, getExpansionListener());
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.horizontalSpan = 2;
        gd.grabExcessHorizontalSpace = true;
        advancedSection.setLayoutData(gd);

        Composite area = (Composite) advancedSection.getClient();
        area.setLayout(new GridLayout(2, false));

        mcOption = toolkit.createButton(area, "Breadth-first mode", SWT.RADIO);
        gd = new GridData();
        gd.horizontalSpan = 2;
        mcOption.setLayoutData(gd);

        mcDFIDOption = toolkit.createButton(area, "Depth-first mode", SWT.RADIO);
        gd = new GridData();
        gd.horizontalSpan = 2;
        mcDFIDOption.setLayoutData(gd);
        // label depth
        FormText dfidDepthLabel = toolkit.createFormText(area, true);
        dfidDepthLabel.setText("Depth:", false, false);
        gd = new GridData();
        gd.horizontalIndent = 10;
        dfidDepthLabel.setLayoutData(gd);
        // field depth
        dfiddepth = toolkit.createText(area, "100");
        gd = new GridData();
        gd.widthHint = 100;
        dfiddepth.setLayoutData(gd);

        simulationOption = toolkit.createButton(area, "Simulation mode", SWT.RADIO);
        gd = new GridData();
        gd.horizontalSpan = 2;
        simulationOption.setLayoutData(gd);

        // label depth
        FormText depthLabel = toolkit.createFormText(area, true);
        depthLabel.setText("Depth:", false, false);
        gd = new GridData();
        gd.horizontalIndent = 10;
        depthLabel.setLayoutData(gd);
        // field depth
        depth = toolkit.createText(area, "100");
        gd = new GridData();
        gd.widthHint = 100;
        depth.setLayoutData(gd);

        // label seed
        FormText seedLabel = toolkit.createFormText(area, true);
        seedLabel.setText("Seed:", false, false);
        gd = new GridData();
        gd.horizontalIndent = 10;
        seedLabel.setLayoutData(gd);

        // field seed
        seed = toolkit.createText(area, "");
        gd = new GridData();
        gd.widthHint = 200;
        seed.setLayoutData(gd);

        // label seed
        FormText arilLabel = toolkit.createFormText(area, true);
        arilLabel.setText("Aril:", false, false);
        gd = new GridData();
        gd.horizontalIndent = 10;
        arilLabel.setLayoutData(gd);

        // field seed
        aril = toolkit.createText(area, "");
        gd = new GridData();
        gd.widthHint = 200;
        aril.setLayoutData(gd);

        return advancedSection;
    }

}
