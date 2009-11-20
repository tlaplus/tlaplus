package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import java.text.SimpleDateFormat;
import java.util.List;
import java.util.Vector;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.events.HyperlinkAdapter;
import org.eclipse.ui.forms.events.HyperlinkEvent;
import org.eclipse.ui.forms.events.IHyperlinkListener;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Hyperlink;
import org.eclipse.ui.forms.widgets.Section;
import org.eclipse.ui.forms.widgets.TableWrapData;
import org.eclipse.ui.forms.widgets.TableWrapLayout;
import org.lamport.tla.toolbox.tool.tlc.output.data.CoverageInformationItem;
import org.lamport.tla.toolbox.tool.tlc.output.data.ITLCModelLaunchDataPresenter;
import org.lamport.tla.toolbox.tool.tlc.output.data.StateSpaceInformationItem;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.util.ActionClickListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.view.TLCErrorView;
import org.lamport.tla.toolbox.util.IHelpConstants;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * A page to display results of model checking (the "third tab"
 * of the model editor).
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ResultPage extends BasicFormPage implements ITLCModelLaunchDataPresenter
{
    public static final String ID = "resultPage";

    private static final String TOOLTIP = "Click on a row to go to action.";

    private Hyperlink errorStatusHyperLink;
    /**
     * UI elements
     */
    private SourceViewer userOutput;
    private SourceViewer progressOutput;
    private Text startTimestampText;
    private Text finishTimestampText;
    private Text lastCheckpointTimeText;
    private Text coverageTimestampText;
    private Text currentStatusText;
    private TableViewer coverage;
    private TableViewer stateSpace;

    // hyper link listener activated in case of errors
    protected IHyperlinkListener errorHyperLinkListener = new HyperlinkAdapter() {

        public void linkActivated(HyperlinkEvent e)
        {
            TLCModelLaunchDataProvider dataProvider = TLCOutputSourceRegistry.getSourceRegistry().getProvider(
                    getConfig());
            if (dataProvider != null)
            {
                TLCErrorView.updateErrorView(dataProvider);
            }
        }
    };

    /**
     * Constructor for the page
     * @param editor
     */
    public ResultPage(FormEditor editor)
    {
        super(editor, ID, "Model Checking Results");
        this.helpId = IHelpConstants.RESULT_MODEL_PAGE;
        this.imagePath = "icons/full/choice_sc_obj.gif";
    }

    /**
     * Will be called by the provider on data changes
     */
    public void modelChanged(final TLCModelLaunchDataProvider dataProvider, final int fieldId)
    {
        UIHelper.runUIAsync(new Runnable() {
            public void run()
            {
                switch (fieldId) {
                case USER_OUTPUT:
                    ResultPage.this.userOutput.setDocument(dataProvider.getUserOutput());
                    break;
                case PROGRESS_OUTPUT:
                    ResultPage.this.progressOutput.setDocument(dataProvider.getProgressOutput());
                    break;
                case START_TIME:
                    ResultPage.this.startTimestampText.setText(dataProvider.getStartTimestamp());
                    break;
                case END_TIME:
                    ResultPage.this.finishTimestampText.setText(dataProvider.getFinishTimestamp());
                    break;
                case LAST_CHECKPOINT_TIME:
                    ResultPage.this.lastCheckpointTimeText.setText(dataProvider.getLastCheckpointTimeStamp());
                    break;
                case CURRENT_STATUS:
                    ResultPage.this.currentStatusText.setText(dataProvider.getCurrentStatus());
                    break;
                case COVERAGE_TIME:
                    ResultPage.this.coverageTimestampText.setText(dataProvider.getCoverageTimestamp());
                    break;
                case COVERAGE:
                    ResultPage.this.coverage.setInput(dataProvider.getCoverageInfo());
                    break;
                case PROGRESS:
                    ResultPage.this.stateSpace.setInput(dataProvider.getProgressInformation());
                    break;
                case ERRORS:
                    String text;
                    Color color;
                    int errorCount = dataProvider.getErrors().size();
                    switch (errorCount) {
                    case 0:
                        text = TLCModelLaunchDataProvider.NO_ERRORS;
                        color = TLCUIActivator.getColor(SWT.COLOR_BLACK);
                        ResultPage.this.errorStatusHyperLink
                                .removeHyperlinkListener(ResultPage.this.errorHyperLinkListener);
                        break;
                    case 1:
                        text = "1 Error";
                        ResultPage.this.errorStatusHyperLink
                                .addHyperlinkListener(ResultPage.this.errorHyperLinkListener);
                        color = TLCUIActivator.getColor(SWT.COLOR_RED);
                        break;
                    default:
                        text = String.valueOf(errorCount) + " Errors";
                        ResultPage.this.errorStatusHyperLink
                                .addHyperlinkListener(ResultPage.this.errorHyperLinkListener);
                        color = TLCUIActivator.getColor(SWT.COLOR_RED);
                        break;
                    }

                    ResultPage.this.errorStatusHyperLink.setText(text);
                    ResultPage.this.errorStatusHyperLink.setForeground(color);

                    // update the error view
                    TLCErrorView.updateErrorView(dataProvider);
                    break;
                default:
                    break;
                }

                // ResultPage.this.refresh();
            }
        });

    }

    /**
     * Gets the data provider for the current page
     */
    public void loadData() throws CoreException
    {

        TLCModelLaunchDataProvider provider = TLCOutputSourceRegistry.getSourceRegistry().getProvider(getConfig());
        if (provider != null)
        {
            provider.setPresenter(this);
        } else
        {
            // no data provider
            reinit();
        }
    }

    /**
     * Reinitialize the fields
     * has to be run in the UI thread
     */
    private synchronized void reinit()
    {
        // TLCUIActivator.logDebug("Entering reinit()");
        this.startTimestampText.setText("");
        this.finishTimestampText.setText("");
        this.lastCheckpointTimeText.setText("");
        this.currentStatusText.setText(TLCModelLaunchDataProvider.NOT_RUNNING);
        this.errorStatusHyperLink.setText(TLCModelLaunchDataProvider.NO_ERRORS);
        this.coverage.setInput(new Vector());
        this.stateSpace.setInput(new Vector());
        this.progressOutput.setDocument(new Document(TLCModelLaunchDataProvider.NO_OUTPUT_AVAILABLE));
        this.userOutput.setDocument(new Document(TLCModelLaunchDataProvider.NO_OUTPUT_AVAILABLE));
        // TLCUIActivator.logDebug("Exiting reinit()");
    }

    /**
     * Dispose the page
     */
    public void dispose()
    {
        TLCModelLaunchDataProvider provider = TLCOutputSourceRegistry.getSourceRegistry().getProvider(getConfig());
        if (provider != null)
        {
            provider.setPresenter(null);
        }
        super.dispose();
    }

    public void setEnabled(boolean enabled)
    {
        // do nothing here, since the result page is read-only per definition
    }

    /**
     * Draw the fields
     */
    protected void createBodyContent(IManagedForm managedForm)
    {
        int sectionFlags = Section.TITLE_BAR | Section.DESCRIPTION | Section.TREE_NODE | Section.EXPANDED | SWT.WRAP;
        int textFieldFlags = SWT.MULTI | SWT.V_SCROLL | SWT.READ_ONLY | SWT.FULL_SELECTION | SWT.WRAP;

        FormToolkit toolkit = managedForm.getToolkit();
        Composite body = managedForm.getForm().getBody();
        TableWrapLayout layout = new TableWrapLayout();
        layout.numColumns = 1;
        body.setLayout(layout);

        TableWrapData twd;
        Section section;
        GridData gd;

        // -------------------------------------------------------------------
        // general section
        section = FormHelper.createSectionComposite(body, "General", ""
        /* "The current progress of model-checking"*/, toolkit, sectionFlags & ~Section.DESCRIPTION,
                getExpansionListener());
        twd = new TableWrapData(TableWrapData.FILL);
        twd.colspan = 1;

        section.setLayoutData(twd);

        Composite generalArea = (Composite) section.getClient();
        generalArea.setLayout(new GridLayout());

        // ------------ status composite ------------
        Composite statusComposite = toolkit.createComposite(generalArea);
        statusComposite.setLayout(new GridLayout(2, false));

        // start
        this.startTimestampText = FormHelper.createTextLeft("Start time:", statusComposite, toolkit);
        this.startTimestampText.setEditable(false);
        // elapsed time
        this.finishTimestampText = FormHelper.createTextLeft("End time:", statusComposite, toolkit);
        this.finishTimestampText.setEditable(false);
        // last checkpoint time
        this.lastCheckpointTimeText = FormHelper.createTextLeft("Last checkpoint time:", statusComposite, toolkit);
        this.lastCheckpointTimeText.setEditable(false);
        // current status
        this.currentStatusText = FormHelper.createTextLeft("Current status:", statusComposite, toolkit);
        this.currentStatusText.setEditable(false);
        this.currentStatusText.setText(TLCModelLaunchDataProvider.NOT_RUNNING);
        // errors
        // Label createLabel =
        // toolkit.createLabel(statusComposite, "Errors detected:");
        // this.errorStatusHyperLink = toolkit.createHyperlink(statusComposite, "", SWT.RIGHT);
        this.errorStatusHyperLink = FormHelper.createHyperlinkLeft("Errors detected:", statusComposite, toolkit);

        // -------------------------------------------------------------------
        // statistics section
        section = FormHelper.createSectionComposite(body, "Statistics", "",
        /*"The current progress of model-checking",*/
        toolkit, (sectionFlags | Section.COMPACT) & ~Section.DESCRIPTION, getExpansionListener());
        twd = new TableWrapData(TableWrapData.FILL);
        twd.colspan = 1;
        section.setLayoutData(twd);
        Composite statArea = (Composite) section.getClient();
        RowLayout rowLayout = new RowLayout(SWT.HORIZONTAL);
        // rowLayout.numColumns = 2;
        statArea.setLayout(rowLayout);

        // progress stats
        createAndSetupStateSpace("State space progress:", statArea, toolkit);
        // coverage stats
        createAndSetupCoverage("Coverage at", statArea, toolkit);

        // -------------------------------------------------------------------
        // output section
        section = FormHelper.createSectionComposite(body, "User Output",
                "TLC output generated by evaluating Print and PrintT expressions.", toolkit, sectionFlags,
                getExpansionListener());
        Composite outputArea = (Composite) section.getClient();
        outputArea.setLayout(new GridLayout());
        // output viewer
        userOutput = FormHelper.createFormsOutputViewer(toolkit, outputArea, textFieldFlags);

        gd = new GridData(SWT.FILL, SWT.LEFT, true, true);
        gd.minimumHeight = 300;
        gd.minimumWidth = 300;
        userOutput.getControl().setLayoutData(gd);

        // -------------------------------------------------------------------
        // progress section
        section = FormHelper.createSectionComposite(body, "Progress Output", "",
        /* "The current progress of model-checking",*/
        toolkit, sectionFlags, getExpansionListener());
        section.setExpanded(false);
        Composite progressArea = (Composite) section.getClient();
        progressArea = (Composite) section.getClient();
        progressArea.setLayout(new GridLayout());

        progressOutput = FormHelper.createFormsOutputViewer(toolkit, progressArea, textFieldFlags);
        gd = new GridData(SWT.FILL, SWT.LEFT, true, true);
        gd.minimumHeight = 300;
        gd.minimumWidth = 300;
        progressOutput.getControl().setLayoutData(gd);

    }

    /**
     * Creates the state space table (initializes the {@link stateSpace} variable)
     * @param label
     * @param parent
     * @param toolkit
     * @return the constructed composite
     */
    private Composite createAndSetupStateSpace(String label, Composite parent, FormToolkit toolkit)
    {
        Composite statespaceComposite = toolkit.createComposite(parent, SWT.WRAP);
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
     * Creates the coverage table (initializes the {@link coverageTimestamp} and {@link coverage} variables)  
     * @param label
     * @param parent
     * @param toolkit
     * @return returns the containing composite
     */
    private Composite createAndSetupCoverage(String label, Composite parent, FormToolkit toolkit)
    {
        Composite coverageComposite = toolkit.createComposite(parent, SWT.WRAP);
        coverageComposite.setLayout(new GridLayout(2, false));
        GridData gd = new GridData();
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
        stateTable.setToolTipText(TOOLTIP);

        CoverageLabelProvider.createTableColumns(stateTable);

        // create the viewer
        this.coverage = new TableViewer(stateTable);

        coverage.addSelectionChangedListener(new ActionClickListener());

        // create list-based content provider
        this.coverage.setContentProvider(new IStructuredContentProvider() {
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

        this.coverage.setLabelProvider(new CoverageLabelProvider());
        return coverageComposite;
    }

    /**
     * Provides labels for the state space table 
     */
    static class StateSpaceLabelProvider extends LabelProvider implements ITableLabelProvider
    {
        public final static String[] columnTitles = new String[] { "Time", "Diameter", "States Found",
                "Distinct States", "Queue Size" };
        public final static int[] columnWidths = { 120, 60, 80, 100, 80 };
        public static final int MIN_WIDTH = columnWidths[0] + columnWidths[1] + columnWidths[2] + columnWidths[3]
                + columnWidths[4];
        public final static int COL_TIME = 0;
        public final static int COL_DIAMETER = 1;
        public final static int COL_FOUND = 2;
        public final static int COL_DISTINCT = 3;
        public final static int COL_LEFT = 4;

        private static final SimpleDateFormat sdf = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss"); // $NON-NLS-1$

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
                // the "N/A" values are used for simulation mode
                StateSpaceInformationItem item = (StateSpaceInformationItem) element;
                switch (columnIndex) {
                case COL_TIME:
                    return sdf.format(item.getTime());
                case COL_DIAMETER:
                    if (item.getDiameter() >= 0)
                    {
                        return String.valueOf(item.getDiameter());
                    } else
                    {
                        return "--";
                    }
                case COL_FOUND:
                    return String.valueOf(item.getFoundStates());
                case COL_DISTINCT:
                    if (item.getDistinctStates() >= 0)
                    {
                        return String.valueOf(item.getDistinctStates());
                    } else
                    {
                        return "--";
                    }

                case COL_LEFT:
                    if (item.getLeftStates() >= 0)
                    {
                        return String.valueOf(item.getLeftStates());
                    } else
                    {
                        return "--";
                    }
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
                column.setToolTipText(TOOLTIP);
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
