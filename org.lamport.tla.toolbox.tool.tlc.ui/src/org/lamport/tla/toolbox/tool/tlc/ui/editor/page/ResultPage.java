package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import java.text.SimpleDateFormat;
import java.util.List;
import java.util.Vector;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.IContentProvider;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.eclipse.ui.forms.widgets.TableWrapData;
import org.lamport.tla.toolbox.tool.tlc.launch.IConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.output.ITLCOutputListener;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCRegion;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.CoverageInformationItem;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.StateSpaceInformationItem;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.util.IHelpConstants;
import org.lamport.tla.toolbox.util.UIHelper;

import tlc2.output.EC;
import tlc2.output.MP;

/**
 * A page to display results of model checking
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ResultPage extends BasicFormPage implements ITLCOutputListener
{
    public static final String ID = "resultPage";
    private static final String NO_OUTPUT_AVAILABLE = "No execution data is available";

    private SourceViewer output;
    private SourceViewer progress;
    private Text startTimeText;
    private Text elapsedTimeText;
    private TableViewer coverage;
    private TableViewer stateSpace;

    // flag indicating that the job / file output is finished
    private boolean isDone = false;
    /**
     * Content provider delivering list content
     */
    private IContentProvider listContentProvider = new IStructuredContentProvider() {
        public void inputChanged(Viewer viewer, Object oldInput, Object newInput)
        {
        }

        public void dispose()
        {
        }

        public Object[] getElements(Object inputElement)
        {
            if (inputElement != null && inputElement instanceof List)
            {
                return ((List) inputElement).toArray(new Object[((List) inputElement).size()]);
            }
            return null;
        }
    };
    private Text coverageTimestampText;

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

        this.coverage.setInput(new Vector());
        this.stateSpace.setInput(new Vector());

        this.progress.setDocument(new Document(NO_OUTPUT_AVAILABLE));
        this.output.setDocument(new Document(NO_OUTPUT_AVAILABLE));

        TLCOutputSourceRegistry.getStatusRegistry().connect(this);
    }

    /**
     * reload the data on activation
     */
    public void setActive(boolean active)
    {
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
        super.setActive(active);
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
    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.ITLCOutputListener#newSourceOccured(int)
     */
    public synchronized void onNewSource()
    {
        UIHelper.runUIAsync(new Runnable() {

            public void run()
            {
                ResultPage.this.coverage.setInput(new Vector());
                ResultPage.this.stateSpace.setInput(new Vector());
            }
        });

        setText(this.output.getDocument(), NO_OUTPUT_AVAILABLE, false);
        setText(this.progress.getDocument(), NO_OUTPUT_AVAILABLE, false);
    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.ITLCOutputListener#onOutput(org.eclipse.jface.text.ITypedRegion, org.eclipse.jface.text.IDocument)
     */
    public synchronized void onOutput(ITypedRegion region, IDocument document)
    {
        // restarting
        if (isDone)
        {
            // the only reason for this is the restart of the MC, after the previous run completed.
            // clean up the output
            setText(this.output.getDocument(), "", false);
            setText(this.progress.getDocument(), "", false);
            isDone = false;
        }

        String outputMessage;
        try
        {
            outputMessage = document.get(region.getOffset(), region.getLength());

        } catch (BadLocationException e)
        {
            TLCUIActivator.logError("Error retrieving a message for the process", e);
            TLCUIActivator.logDebug("R " + region);
            return;
        }

        if (region instanceof TLCRegion)
        {
            TLCRegion tlcRegion = (TLCRegion) region;
            int severity = tlcRegion.getSeverity();
            int messageCode = tlcRegion.getMessageCode();

            switch (severity) {
            case MP.ERROR:
            case MP.TLCBUG:
            case MP.WARNING:

                // setText(this.errors, outputMessage, true);
                break;
            case MP.NONE:
                switch (messageCode) {
                // Progress information
                case EC.TLC_SANY_START:
                case EC.TLC_MODE_MC:
                case EC.TLC_MODE_SIMU:
                case EC.TLC_SANY_END:
                case EC.TLC_COMPUTING_INIT:
                case EC.TLC_CHECKING_TEMPORAL_PROPS:
                case EC.TLC_SUCCESS:
                case EC.TLC_PROGRESS_SIMU:
                case EC.TLC_PROGRESS_START_STATS_DFID:
                case EC.TLC_PROGRESS_STATS_DFID:
                case EC.TLC_INITIAL_STATE:
                case EC.TLC_INIT_GENERATED1:
                case EC.TLC_INIT_GENERATED2:
                case EC.TLC_INIT_GENERATED3:
                case EC.TLC_INIT_GENERATED4:
                case EC.TLC_STATS:
                case EC.TLC_STATS_DFID:
                case EC.TLC_STATS_SIMU:
                case EC.TLC_SEARCH_DEPTH:
                case EC.TLC_CHECKPOINT_START:
                case EC.TLC_CHECKPOINT_END:
                case EC.TLC_CHECKPOINT_RECOVER_START:
                case EC.TLC_CHECKPOINT_RECOVER_END:
                case EC.TLC_CHECKPOINT_RECOVER_END_DFID:                    
                    setText(this.progress.getDocument(), outputMessage, true);
                    break;
                case EC.TLC_FINISHED:
                    final String finishedTimestamp = outputMessage.substring(outputMessage.indexOf("(") + 1,
                            outputMessage.indexOf(")"));
                    UIHelper.runUIAsync(new Runnable() {

                        public void run()
                        {
                            ResultPage.this.elapsedTimeText.setText(finishedTimestamp);
                        }
                    });
                    break;

                case EC.TLC_STARTING:
                    final String startingTimestamp = outputMessage.substring(outputMessage.indexOf("(") + 1,
                            outputMessage.indexOf(")"));
                    UIHelper.runUIAsync(new Runnable() {

                        public void run()
                        {
                            ResultPage.this.startTimeText.setText(startingTimestamp);
                        }
                    });
                    break;
                case EC.TLC_PROGRESS_STATS:
                    final StateSpaceInformationItem stateSpaceInformationItem = StateSpaceInformationItem
                            .parse(outputMessage);
                    UIHelper.runUIAsync(new Runnable() {
                        public void run()
                        {
                            // TODO add to the model
                            ResultPage.this.stateSpace.add(stateSpaceInformationItem);
                            ResultPage.this.stateSpace.refresh(stateSpaceInformationItem);
                        }
                    });
                    break;
                // Coverage information
                case EC.TLC_COVERAGE_START:
                    final String coverageTimestamp = CoverageInformationItem.parseCoverageTimestamp(outputMessage);
                    UIHelper.runUIAsync(new Runnable() {

                        public void run()
                        {
                            ResultPage.this.coverage.setInput(new Vector());
                            ResultPage.this.coverageTimestampText.setText(coverageTimestamp);
                        }
                    });
                    break;
                case EC.TLC_COVERAGE_VALUE:
                    final CoverageInformationItem coverageInformationItem = CoverageInformationItem
                            .parse(outputMessage);
                    UIHelper.runUIAsync(new Runnable() {
                        public void run()
                        {
                            // TODO add to the model
                            ResultPage.this.coverage.add(coverageInformationItem);
                            ResultPage.this.coverage.refresh(coverageInformationItem);
                        }
                    });
                    break;
                case EC.TLC_COVERAGE_END:
                    break;
                default:
                    setText(this.output.getDocument(), outputMessage, true);
                    break;
                }
                break;
            default:
                setText(this.output.getDocument(), outputMessage, true);
            }

        } else
        {
            setText(this.output.getDocument(), outputMessage, true);
            // TLCUIActivator.logDebug("Unknown type detected: " + region.getType() + " message " + outputMessage);
        }

    }

    /**
     * Sets text
     * @param document
     * @param message
     * @param append
     * @throws BadLocationException
     */
    public synchronized void setText(final IDocument document, final String message, final boolean append)
    {
        final String CR = "\n";
        final String EMPTY = "";

        UIHelper.runUIAsync(new Runnable() {

            public void run()
            {
                try
                {
                    if (append)
                    {
                        if (document.getLength() == NO_OUTPUT_AVAILABLE.length())
                        {
                            String content = document.get(0, NO_OUTPUT_AVAILABLE.length());
                            if (content != null && NO_OUTPUT_AVAILABLE.equals(content))
                            {
                                document.replace(0, document.getLength(), message
                                        + ((message.endsWith(CR)) ? EMPTY : CR));
                            }
                        } else
                        {
                            document.replace(document.getLength(), 0, message + ((message.endsWith(CR)) ? EMPTY : CR));
                        }
                    } else
                    {
                        document.replace(0, document.getLength(), message + ((message.endsWith(CR)) ? EMPTY : CR));
                    }
                } catch (BadLocationException e)
                {

                }
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

        // join
        Composite join = toolkit.createComposite(body);
        twd = new TableWrapData(TableWrapData.FILL_GRAB);
        twd.grabHorizontal = true;
        twd.colspan = 2;
        join.setLayout(new GridLayout(1, true));
        join.setLayoutData(twd);

        Section section;
        GridLayout layout;

        // -------------------------------------------------------------------
        // progress
        section = FormHelper.createSectionComposite(join, "Progress", "The current progress of model-checking",
                toolkit, sectionFlags, getExpansionListener());
        // only grab horizontal space
        gd = new GridData(GridData.FILL_HORIZONTAL);
        section.setLayoutData(gd);

        Composite progressArea = (Composite) section.getClient();
        layout = new GridLayout(3, false);
        progressArea.setLayout(layout);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.grabExcessHorizontalSpace = true;
        progressArea.setLayoutData(gd);

        // ------------ first row ------------

        Composite timesComposite = toolkit.createComposite(progressArea);
        gd = new GridData();
        gd.verticalAlignment = SWT.TOP;
        timesComposite.setLayoutData(gd);
        timesComposite.setLayout(new GridLayout(2, false));

        // start
        startTimeText = createTextLeft("Start time:", timesComposite, toolkit);
        // elapsed time
        elapsedTimeText = createTextLeft("Elapsed time:", timesComposite, toolkit);

        // coverage
        Composite coverageStats = createAndSetupCoverage("Coverage:", progressArea, toolkit);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 200;
        gd.minimumHeight = 200;
        coverageStats.setData(gd);

        // progress stats
        Composite stateStats = createAndSetupStateSpace("Statespace Statistics:", progressArea, toolkit);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 200;
        gd.minimumHeight = 200;
        stateStats.setData(gd);

        // ------------ second row ------------

        progress = FormHelper.createFormsOutputViewer(toolkit, progressArea, textFieldFlags);
        gd = new GridData(SWT.FILL, SWT.LEFT, true, true);
        gd.horizontalSpan = 3;
        gd.minimumHeight = 300;
        gd.heightHint = 250;
        gd.minimumWidth = 300;
        progress.getControl().setLayoutData(gd);

        // -------------------------------------------------------------------
        // output
        section = FormHelper.createSectionComposite(join, "User Output", "Output created by TLC during the execution",
                toolkit, sectionFlags, getExpansionListener());
        // only grab horizontal space
        gd = new GridData(SWT.FILL, SWT.LEFT, true, false);
        section.setLayoutData(gd);

        Composite outputArea = (Composite) section.getClient();
        layout = new GridLayout();
        layout.numColumns = 1;
        outputArea.setLayout(layout);
        gd = new GridData(SWT.FILL, SWT.LEFT, true, true);
        outputArea.setLayoutData(gd);

        output = FormHelper.createFormsOutputViewer(toolkit, outputArea, textFieldFlags);
        gd = new GridData(SWT.FILL, SWT.LEFT, true, true);
        gd.minimumHeight = 280;
        gd.heightHint = 280;
        gd.minimumWidth = 300;
        output.getControl().setLayoutData(gd);
    }

    /**
     * Creates the state space table 
     * @param label
     * @param parent
     * @param toolkit
     * @return
     */
    private Composite createAndSetupStateSpace(String label, Composite parent, FormToolkit toolkit)
    {
        Composite statespaceComposite = toolkit.createComposite(parent);
        statespaceComposite.setLayout(new GridLayout(1, false));

        toolkit.createLabel(statespaceComposite, label);

        Table stateTable = toolkit.createTable(statespaceComposite, SWT.MULTI | SWT.FULL_SELECTION | SWT.V_SCROLL
                | SWT.BORDER);
        GridData gd = new GridData(StateSpaceLabelProvider.MIN_WIDTH, 100);
        stateTable.setLayoutData(gd);

        stateTable.setHeaderVisible(true);
        stateTable.setLinesVisible(true);

        StateSpaceLabelProvider.createTableColumns(stateTable);

        // create the viewer
        this.stateSpace = new TableViewer(stateTable);

        // create list-based content provider
        this.stateSpace.setContentProvider(new IStructuredContentProvider() {
            public void inputChanged(Viewer viewer, Object oldInput, Object newInput)
            {
            }

            public void dispose()
            {
            }

            public Object[] getElements(Object inputElement)
            {
                if (inputElement != null && inputElement instanceof List)
                {
                    return ((List) inputElement).toArray(new Object[((List) inputElement).size()]);
                }
                return null;
            }
        });

        this.stateSpace.setLabelProvider(new StateSpaceLabelProvider());
        return statespaceComposite;
    }

    /**
     * Creates the state space table 
     * @param label
     * @param parent
     * @param toolkit
     * @return
     */
    private Composite createAndSetupCoverage(String label, Composite parent, FormToolkit toolkit)
    {
        Composite coverageComposite = toolkit.createComposite(parent);
        coverageComposite.setLayout(new GridLayout(2, false));
        GridData gd = new GridData();
        coverageComposite.setLayoutData(gd);
        toolkit.createLabel(coverageComposite, label);

        this.coverageTimestampText = toolkit.createText(coverageComposite, "", SWT.FLAT);
        this.coverageTimestampText.setEditable(false);
        gd = new GridData();
        gd.minimumWidth = 200;
        gd.grabExcessHorizontalSpace = true;
        this.coverageTimestampText.setLayoutData(gd);

        Table stateTable = toolkit.createTable(coverageComposite, SWT.MULTI | SWT.FULL_SELECTION | SWT.V_SCROLL
                | SWT.BORDER);
        gd = new GridData(CoverageLabelProvider.MIN_WIDTH, 100);
        gd.horizontalSpan = 2;
        stateTable.setLayoutData(gd);

        stateTable.setHeaderVisible(true);
        stateTable.setLinesVisible(true);

        CoverageLabelProvider.createTableColumns(stateTable);

        // create the viewer
        this.coverage = new TableViewer(stateTable);

        // create list-based content provider
        this.coverage.setContentProvider(listContentProvider);

        this.coverage.setLabelProvider(new CoverageLabelProvider());
        return coverageComposite;
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
        Label createLabel = toolkit.createLabel(parent, title);
        GridData gd = new GridData();
        createLabel.setLayoutData(gd);
        gd.verticalAlignment = SWT.TOP;
        Text text = toolkit.createText(parent, "");

        gd = new GridData(SWT.FILL, SWT.LEFT, true, false);
        gd.horizontalIndent = 30;
        gd.verticalAlignment = SWT.TOP;
        gd.horizontalAlignment = SWT.RIGHT;
        gd.minimumWidth = 150;
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

    /**
     * Provides labels for the statespace table 
     */
    static class StateSpaceLabelProvider extends LabelProvider implements ITableLabelProvider
    {
        public final static String[] columnTitles = new String[] { "Time", "Diameter", "States Found",
                "States Distinct", "States Left" };
        public final static int[] columnWidths = { 150, 80, 80, 80, 80 };
        public static final int MIN_WIDTH = columnWidths[0] + columnWidths[1] + columnWidths[2] + columnWidths[3]
                + columnWidths[4];
        public final static int COL_TIME = 0;
        public final static int COL_DIAMETER = 1;
        public final static int COL_FOUND = 2;
        public final static int COL_DISTINCT = 3;
        public final static int COL_LEFT = 4;

        private static final SimpleDateFormat sdf = new SimpleDateFormat("yyyy-MM-dd hh:mm:ss");

        /* (non-Javadoc)
         * @see org.eclipse.jface.viewers.ITableLabelProvider#getColumnImage(java.lang.Object, int)
         */
        public Image getColumnImage(Object element, int columnIndex)
        {
            return null;
        }

        /**
         * @param stateTable
         */
        public static void createTableColumns(Table stateTable)
        {
            // create table headers
            for (int i = 0; i < columnTitles.length; i++)
            {
                TableColumn column = new TableColumn(stateTable, SWT.NULL);
                column.setWidth(columnWidths[i]);
                column.setText(columnTitles[i]);
            }
        }

        /* (non-Javadoc)
         * @see org.eclipse.jface.viewers.ITableLabelProvider#getColumnText(java.lang.Object, int)
         */
        public String getColumnText(Object element, int columnIndex)
        {
            if (element instanceof StateSpaceInformationItem)
            {
                StateSpaceInformationItem item = (StateSpaceInformationItem) element;
                switch (columnIndex) {
                case COL_TIME:
                    return sdf.format(item.getTime());
                case COL_DIAMETER:
                    return String.valueOf(item.getDiameter());
                case COL_FOUND:
                    return String.valueOf(item.getFoundStates());
                case COL_DISTINCT:
                    return String.valueOf(item.getDistinctStates());
                case COL_LEFT:
                    return String.valueOf(item.getLeftStates());
                }
            }
            return null;
        }

    }

    /**
     * Provides labels for the coverage table 
     */
    static class CoverageLabelProvider extends LabelProvider implements ITableLabelProvider
    {
        public final static String[] columnTitles = new String[] { "Module", "Location", "Count" };
        public final static int[] columnWidths = { 80, 200, 80 };
        public static final int MIN_WIDTH = columnWidths[0] + columnWidths[1] + columnWidths[2];
        public final static int COL_MODULE = 0;
        public final static int COL_LOCATION = 1;
        public final static int COL_COUNT = 2;

        /* (non-Javadoc)
         * @see org.eclipse.jface.viewers.ITableLabelProvider#getColumnImage(java.lang.Object, int)
         */
        public Image getColumnImage(Object element, int columnIndex)
        {
            return null;
        }

        /**
         * @param stateTable
         */
        public static void createTableColumns(Table stateTable)
        {
            // create table headers
            for (int i = 0; i < columnTitles.length; i++)
            {
                TableColumn column = new TableColumn(stateTable, SWT.NULL);
                column.setWidth(columnWidths[i]);
                column.setText(columnTitles[i]);
            }
        }

        /* (non-Javadoc)
         * @see org.eclipse.jface.viewers.ITableLabelProvider#getColumnText(java.lang.Object, int)
         */
        public String getColumnText(Object element, int columnIndex)
        {
            if (element instanceof CoverageInformationItem)
            {
                CoverageInformationItem item = (CoverageInformationItem) element;
                switch (columnIndex) {
                case COL_MODULE:
                    return item.getModule();
                case COL_LOCATION:
                    return item.getLocation();
                case COL_COUNT:
                    return String.valueOf(item.getCount());
                }
            }
            return null;
        }

    }

}
