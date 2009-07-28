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
import org.lamport.tla.toolbox.tool.tlc.output.TLCOutputSourceRegistry;
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
    // private Text startTimeText;
    // private Text elapsedTimeText;
    // private Text currentTask;
    // private Text statesGenerated;
    // private Text statesFound;
    // private Text statesLeft;

    private Text output;
    private Text progress;

    /**
     * @param editor
     */
    public ResultPage(FormEditor editor)
    {
        super(editor, ID, "Model Checking Results");
        this.helpId = IHelpConstants.RESULT_MODEL_PAGE;
        this.imagePath = "icons/full/choice_sc_obj.gif";
    }

    protected void createBodyContent(IManagedForm managedForm)
    {
        int sectionFlags = Section.TITLE_BAR | Section.DESCRIPTION | Section.TREE_NODE | Section.EXPANDED;

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
        progress = toolkit.createText(progressArea, "", SWT.MULTI | SWT.V_SCROLL);
        gd = new GridData(SWT.FILL, SWT.LEFT, true, true);
        gd.minimumHeight = 300;
        gd.minimumWidth = 300;
        progress.setLayoutData(gd);

        // output
        section = FormHelper.createSectionComposite(right, "Output", "Output created by TLC during the execution",
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

        output = toolkit.createText(outputArea, "", SWT.MULTI | SWT.V_SCROLL);
        gd = new GridData(SWT.FILL, SWT.LEFT, true, true);
        gd.minimumHeight = 300;
        gd.minimumWidth = 300;
        output.setLayoutData(gd);
    }

    protected void loadData() throws CoreException
    {
        TLCOutputSourceRegistry.getStatusRegistry().connect(this);
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

    private static Text createTextLeft(String title, Composite parent, FormToolkit toolkit)
    {
        toolkit.createLabel(parent, title);
        Text text = toolkit.createText(parent, "");

        GridData gd = new GridData(SWT.FILL, SWT.LEFT, true, false);
        gd.horizontalIndent = 30;
        gd.horizontalAlignment = SWT.RIGHT;
        text.setLayoutData(gd);

        return text;

    }

    private static Text createTextRight(String title, Composite parent, FormToolkit toolkit)
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

 
    public void dispose()
    {
        TLCOutputSourceRegistry.getStatusRegistry().disconnect(this);
        super.dispose();
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
    public void onDone()
    {
        System.out.println("Done");
    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.ITLCOutputListener#onOutput(org.eclipse.jface.text.ITypedRegion, org.eclipse.jface.text.IDocument)
     */
    public void onOutput(ITypedRegion region, IDocument document)
    {
        try
        {
            final String outputMessage = document.get(region.getOffset(), region.getLength()) + "\n";

            
            switch (PartitionToolkit.getRegionTypeAsInt(region))
            {
            case PartitionToolkit.TYPE_USER_OUTPUT:
                appendText(this.output, outputMessage);
                break;
            case PartitionToolkit.TYPE_COVERAGE:
            case PartitionToolkit.TYPE_INIT_END:
            case PartitionToolkit.TYPE_INIT_START:
            case PartitionToolkit.TYPE_PROGRESS:            
                appendText(this.progress, outputMessage);
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
    
    public void appendText(final Text control, final String message) 
    {
        UIHelper.runUIAsync(new Runnable() {
            
            public void run()
            {
                control.append(message);
                refresh();
            }
        });
    }

}
