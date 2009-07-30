package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.eclipse.ui.forms.widgets.TableWrapData;
import org.lamport.tla.toolbox.tool.tlc.launch.IConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.output.ITLCOutputListener;
import org.lamport.tla.toolbox.tool.tlc.output.PartitionToolkit;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.util.IHelpConstants;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * A page to display results of model checking
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ResultPage extends BasicFormPage implements ITLCOutputListener
{
    public static final String ID = "resultPage";
    private static final String NO_OUTPUT_AVAILABLE = "No execution data is available";
    // private Text startTimeText;
    // private Text elapsedTimeText;
    // private Text currentTask;
    // private Text statesGenerated;
    // private Text statesFound;
    // private Text statesLeft;

    private Text output;
    private Text progress;
    private Text coverage;    
    private Text errors;
    // flag indicating that the job / file output is finished
    private boolean isDone = false;

    /**
     * @param editor
     */
    public ResultPage(FormEditor editor)
    {
        super(editor, ID, "Model Checking Results");
        this.helpId = IHelpConstants.RESULT_MODEL_PAGE;
        this.imagePath = "icons/full/choice_sc_obj.gif";
    }


    protected void loadData() throws CoreException
    {
        TLCOutputSourceRegistry.getStatusRegistry().disconnect(this);
        boolean connected = TLCOutputSourceRegistry.getStatusRegistry().connect(this);
        if (!connected)
        {
            setText(this.output, NO_OUTPUT_AVAILABLE, false);
            setText(this.progress, NO_OUTPUT_AVAILABLE, false);
        }
    }

    // /**
    // * Updates the state fields
    // * @param generated
    // * @param distinct
    // * @param left
    // */
    // private void setStates(int generated, int distinct, int left)
    // {
    // statesFound.setText(String.valueOf(distinct));
    // statesGenerated.setText(String.valueOf(generated));
    // statesLeft.setText(String.valueOf(left));
    // }

    /**
     * reload the data on activation
     */
    public void setActive(boolean active)
    {
        super.setActive(active);
        if (active)
        {
            // refresh
            try
            {
                loadData();
            } catch (CoreException e)
            {
                TLCUIActivator.logError("Error refreshing the page", e);
            }
        }
    }


    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.ITLCOutputListener#getProcessName()
     */
    public String getProcessName()
    {
        String modelName = null;
        try
        {
            modelName = getConfig().getAttribute(IConfigurationConstants.MODEL_NAME, "");
        } catch (CoreException e)
        {
            TLCUIActivator.logError("Error retrieveing the model name", e);
        }
        Assert.isTrue(modelName != null && !modelName.equals(""), "Bug, model name is not set properly");
        return modelName;
    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.ITLCOutputListener#onDone()
     */
    public synchronized void onDone()
    {
        this.isDone = true;
        System.out.println("Done");
    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.ITLCOutputListener#newSourceOccured(int)
     */
    public synchronized void onNewSource()
    {
        // System.out.println("Live stream for current model.");
        setText(this.output, NO_OUTPUT_AVAILABLE, false);
        setText(this.progress, NO_OUTPUT_AVAILABLE, false);
    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.ITLCOutputListener#onOutput(org.eclipse.jface.text.ITypedRegion, org.eclipse.jface.text.IDocument)
     */
    public synchronized void onOutput(ITypedRegion region, IDocument document)
    {

        if (isDone) 
        {
            // the only reason for this is the restart of the MC, after the previous run completed.
            // clean up the output
            setText(this.output, "", false);
            setText(this.progress, "", false);
            isDone = false;
        }
        try
        {
            final String outputMessage = document.get(region.getOffset(), region.getLength()) + "\n";

            switch (PartitionToolkit.getRegionTypeAsInt(region)) {
            case PartitionToolkit.TYPE_USER_OUTPUT:
                setText(this.output, outputMessage, true);
                break;
            case PartitionToolkit.TYPE_COVERAGE:
            case PartitionToolkit.TYPE_INIT_END:
            case PartitionToolkit.TYPE_INIT_START:
            case PartitionToolkit.TYPE_PROGRESS:
            case PartitionToolkit.TYPE_TAG:
                setText(this.progress, outputMessage, true);
                break;
            case PartitionToolkit.TYPE_UNKNOWN:
            default:
                System.err.println("Unknown type detected: " + region.getType());
                break;
            }

        } catch (BadLocationException e)
        {
            TLCUIActivator.logError("Error retrieving a message for the process", e);
        }
    }

    /**
     * Replaces or appends the text to the text control
     * @param control
     * @param message
     * @param append
     */
    public synchronized void setText(final Text control, final String message, final boolean append)
    {
        UIHelper.runUIAsync(new Runnable() {

            public void run()
            {
                if (append)
                {
                    if (NO_OUTPUT_AVAILABLE.equals(control.getText()))
                    {
                        control.setText("");
                    }
                    control.append(message);
                } else
                {
                    control.setText(message);
                }
                control.update();
            }
        });
    }

    
    /**
     * Draw the fields
     */
    protected void createBodyContent(IManagedForm managedForm)
    {
        int sectionFlags = Section.TITLE_BAR | Section.DESCRIPTION | Section.TREE_NODE | Section.EXPANDED;
        int textFieldFlags = SWT.MULTI | SWT.V_SCROLL | SWT.WRAP | SWT.READ_ONLY | SWT.FULL_SELECTION;

        FormToolkit toolkit = managedForm.getToolkit();
        Composite body = managedForm.getForm().getBody();

        GridData gd;
        TableWrapData twd;

        // left
        Composite left = toolkit.createComposite(body);
        twd = new TableWrapData(TableWrapData.FILL_GRAB);
        twd.grabHorizontal = true;
        left.setLayout(new GridLayout(1, true));
        left.setLayoutData(twd);

        // right
        Composite right = toolkit.createComposite(body);
        twd = new TableWrapData(TableWrapData.FILL_GRAB);
        twd.grabHorizontal = true;
        right.setLayoutData(twd);
        right.setLayout(new GridLayout(1, true));

        Section section;
        GridLayout layout;

        // -------------------------------------------------------------------
        // progress
        section = FormHelper.createSectionComposite(left, "Progress", "The current progress of model-checking",
                toolkit, sectionFlags, getExpansionListener());
        // only grab horizontal space
        gd = new GridData(GridData.FILL_HORIZONTAL);
        section.setLayoutData(gd);
        addSection(SEC_PROGRESS, section);

        Composite progressArea = (Composite) section.getClient();
        layout = new GridLayout(4, false);
        progressArea.setLayout(layout);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.grabExcessHorizontalSpace = true;
        progressArea.setLayoutData(gd);

        /*
        startTimeText = createTextLeft("Start time:", progressArea, toolkit);
        statesGenerated = createTextRight("States generated:", progressArea, toolkit);
        elapsedTimeText = createTextLeft("Elapsed time:", progressArea, toolkit);
        statesFound = createTextRight("Distinct states found:", progressArea, toolkit);
        currentTask = createTextLeft("Current task:", progressArea, toolkit);
        statesLeft = createTextRight("States left on queue:", progressArea, toolkit);
         */
        progress = toolkit.createText(progressArea, "", textFieldFlags);
        gd = new GridData(SWT.FILL, SWT.LEFT, true, true);
        gd.minimumHeight = 300;
        gd.heightHint = 300;
        gd.minimumWidth = 300;
        progress.setLayoutData(gd);

        // -------------------------------------------------------------------
        // errors
        section = FormHelper.createSectionComposite(left, "Errors", "Detected errors",
                toolkit, sectionFlags, getExpansionListener());
        // only grab horizontal space
        gd = new GridData(GridData.FILL_HORIZONTAL);
        section.setLayoutData(gd);
        addSection(SEC_ERRORS, section);

        Composite errorsArea = (Composite) section.getClient();
        layout = new GridLayout(4, false);
        errorsArea.setLayout(layout);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.grabExcessHorizontalSpace = true;
        errorsArea.setLayoutData(gd);

        errors = toolkit.createText(errorsArea, "", textFieldFlags);
        gd = new GridData(SWT.FILL, SWT.LEFT, true, true);
        gd.minimumHeight = 150;
        gd.heightHint = 300;
        gd.minimumWidth = 150;
        errors.setLayoutData(gd);

        
        // -------------------------------------------------------------------
        // output
        section = FormHelper.createSectionComposite(right, "User Output", "Output created by TLC during the execution",
                toolkit, sectionFlags, getExpansionListener());
        // only grab horizontal space
        gd = new GridData(SWT.FILL, SWT.LEFT, true, false);
        section.setLayoutData(gd);
        addSection(SEC_OUTPUT, section);

        Composite outputArea = (Composite) section.getClient();
        layout = new GridLayout();
        layout.numColumns = 1;
        outputArea.setLayout(layout);
        gd = new GridData(SWT.FILL, SWT.LEFT, true, true);
        outputArea.setLayoutData(gd);

        output = toolkit.createText(outputArea, "", textFieldFlags);
        gd = new GridData(SWT.FILL, SWT.LEFT, true, true);
        gd.minimumHeight = 300;
        gd.heightHint = 300;
        gd.minimumWidth = 300;
        output.setLayoutData(gd);
        
        // -------------------------------------------------------------------
        // coverage
        section = FormHelper.createSectionComposite(right, "Coverage", "The coverage information",
                toolkit, sectionFlags | Section.COMPACT, getExpansionListener());
        // only grab horizontal space
        gd = new GridData(GridData.FILL_HORIZONTAL);
        section.setLayoutData(gd);
        addSection(SEC_COVERAGE, section);

        Composite coverageArea = (Composite) section.getClient();
        layout = new GridLayout(4, false);
        coverageArea.setLayout(layout);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.grabExcessHorizontalSpace = true;
        coverageArea.setLayoutData(gd);

        coverage = toolkit.createText(coverageArea, "", textFieldFlags);
        gd = new GridData(SWT.FILL, SWT.LEFT, true, true);
        gd.minimumHeight = 150;
        gd.heightHint = 300;
        gd.minimumWidth = 150;
        coverage.setLayoutData(gd);

    }
    
    /**
     * Dispose the page
     */
    public void dispose()
    {
        TLCOutputSourceRegistry.getStatusRegistry().disconnect(this);
        super.dispose();
    }
    
    public void setEnabled(boolean enabled)
    {
        // do nothing here, since the result page is read-only per definition
    }

    
    
    /**
     * Creates a text component with left-aligned text
     * @param title
     * @param parent
     * @param toolkit
     * @return
     */
    public static Text createTextLeft(String title, Composite parent, FormToolkit toolkit)
    {
        toolkit.createLabel(parent, title);
        Text text = toolkit.createText(parent, "");

        GridData gd = new GridData(SWT.FILL, SWT.LEFT, true, false);
        gd.horizontalIndent = 30;
        gd.horizontalAlignment = SWT.RIGHT;
        text.setLayoutData(gd);

        return text;

    }

    /**
     * Creates a text component with right-aligned text
     * @param title
     * @param parent
     * @param toolkit
     * @return
     */
    public static Text createTextRight(String title, Composite parent, FormToolkit toolkit)
    {
        Label label = toolkit.createLabel(parent, title);
        GridData gd = new GridData();
        gd.horizontalIndent = 30;
        label.setLayoutData(gd);

        Text text = toolkit.createText(parent, "");

        gd = new GridData(SWT.FILL, SWT.LEFT, true, false);
        gd.horizontalIndent = 30;
        gd.minimumWidth = 30;
        gd.horizontalAlignment = SWT.RIGHT;
        text.setLayoutData(gd);

        return text;
    }

}
