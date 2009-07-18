package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.eclipse.ui.forms.widgets.TableWrapData;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.util.ReadOnlyFileEditorInput;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper.IFileProvider;
import org.lamport.tla.toolbox.util.IHelpConstants;

/**
 * A page to display results of model checking
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ResultPage extends BasicFormPage implements IResourceChangeListener
{
    public static final String ID = "resultPage";
//    private Text startTimeText;
//    private Text elapsedTimeText;
//    private Text currentTask;
//    private Text statesGenerated;
//    private Text statesFound;
//    private Text statesLeft;
    
    private Text output;
    private Text progress;
    
    private IDocument document = null;
    
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
        section = FormHelper.createSectionComposite(left, "Progress", "The current progress of model-checking", toolkit,
                sectionFlags, getExpansionListener());
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
        progress = toolkit.createText(progressArea, "");
        gd = new GridData(SWT.FILL, SWT.LEFT, true, true);
        gd.minimumHeight = 300;
        gd.minimumWidth = 300;
        progress.setLayoutData(gd);

        
        // output
        section = FormHelper.createSectionComposite(right, "Output", "Output created by TLC during the execution", toolkit,
                sectionFlags, getExpansionListener());
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
        
        output = toolkit.createText(outputArea, "");
        gd = new GridData(SWT.FILL, SWT.LEFT, true, true);
        gd.minimumHeight = 300;
        gd.minimumWidth = 300;
        output.setLayoutData(gd);
    }


    protected void loadData() throws CoreException
    {
//        if (getEditor() instanceof ModelEditor) 
//        {
//            editor = (ModelEditor) getEditor();
//            IResource resource = editor.getResource(IFileProvider.TYPE_RESULT);
//            if (resource.exists()) 
//            {
//                super.setInput(new ReadOnlyFileEditorInput((IFile) resource));
//            }
//        }
//
//        
//        IEditorInput editorInput = getEditorInput();
//        if (editorInput != null) 
//        {
//            // there is something to display
//            enableSection(SEC_PROGRESS, true);
//            enableSection(SEC_OUTPUT, true);
//            
//            output.setText("Text!");
//            
//        } else 
//        {
//            // disable the fields
//            enableSection(SEC_PROGRESS, false);
//            enableSection(SEC_OUTPUT, false);
//        }
        
        
//        startTimeText.setText(f.format(new Date()));
//        elapsedTimeText.setText(f.format(new Date())); 
//        currentTask.setText("idle");
        
//        setStates(100, 100, 23);
    }


//    /**
//     * Updates the state fields
//     * @param generated
//     * @param distinct
//     * @param left
//     */
//    private void setStates(int generated, int distinct, int left)
//    {
//        statesFound.setText(String.valueOf(distinct));
//        statesGenerated.setText(String.valueOf(generated));
//        statesLeft.setText(String.valueOf(left));
//    }
    
    private static Text createTextLeft(String title, Composite parent, FormToolkit toolkit) 
    {
        toolkit.createLabel(parent, title);
        Text text  = toolkit.createText(parent, "");
        
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
        
        Text text  = toolkit.createText(parent, "");
        
        gd = new GridData(SWT.FILL, SWT.LEFT, true, false);
        gd.horizontalIndent = 30;
        gd.minimumWidth = 30;
        gd.horizontalAlignment = SWT.RIGHT;
        text.setLayoutData(gd);
        
        return text;
    }

    /* (non-Javadoc)
     * @see org.eclipse.core.resources.IResourceChangeListener#resourceChanged(org.eclipse.core.resources.IResourceChangeEvent)
     */
    public void resourceChanged(IResourceChangeEvent event)
    {
        IFile logFile = ((IFileProvider)getEditor()).getResource(IFileProvider.TYPE_RESULT);
        IResourceDelta logDelta = event.getDelta().findMember(logFile.getFullPath());
        if (logDelta != null) 
        {
            switch(logDelta.getKind()) 
            {
            case IResourceDelta.ADDED:
                initDocument();
                break;
            case IResourceDelta.REMOVED:
                document = null;
                break;
            case IResourceDelta.CHANGED:
                // System.out.println(">> change");
                break;
            }
        } 
    }

    
    private void initDocument()
    {
        IFile logFile = ((IFileProvider)getEditor()).getResource(IFileProvider.TYPE_RESULT);
        ReadOnlyFileEditorInput fInput = new ReadOnlyFileEditorInput(logFile);
        FileDocumentProvider fileDocumentProvider = new FileDocumentProvider();
        try
        {
            fileDocumentProvider.connect(fInput);
            document = fileDocumentProvider.getDocument(fInput);
            document.setDocumentPartitioner(new FastPartitioner(new LogPartitionTokenScanner(), LogPartitionTokenScanner.CONTENT_TYPES));
        } catch (CoreException e)
        {
            e.printStackTrace();
        }
        
    }
    
    public void dispose()
    {
        document = null;
        super.dispose();
    }

    
}
