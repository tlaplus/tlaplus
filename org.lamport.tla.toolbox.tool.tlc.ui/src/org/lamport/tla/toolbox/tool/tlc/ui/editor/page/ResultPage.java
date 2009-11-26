package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import java.text.SimpleDateFormat;
import java.util.List;
import java.util.Vector;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.resource.JFaceResources;
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
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.ValidateableSectionPart;
import org.lamport.tla.toolbox.tool.tlc.ui.util.ActionClickListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.DirtyMarkingListener;
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
    private SourceViewer expressionEvalResult;
    private SourceViewer expressionEvalInput;
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
                case CONST_EXPR_EVAL_OUTPUT:
                    ResultPage.this.expressionEvalResult.getTextWidget().setText(dataProvider.getCalcOutput());
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

        // constant expression
        String expression = getConfig().getAttribute(MODEL_EXPRESSION_EVAL, EMPTY_STRING);
        expressionEvalInput.setDocument(new Document(expression));
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
     * 
     * Its helpful to know what the standard SWT widgets look like.
     * Pictures can be found at http://www.eclipse.org/swt/widgets/
     * 
     * Layouts are used throughout this method.
     * A good explanation of layouts is given in the article
     * http://www.eclipse.org/articles/article.php?file=Article-Understanding-Layouts/index.html
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
        // There is no description line for this section, so it is
        // necessary to eliminate that bit in the style flags that
        // are passed in. If the bit were not changed to 0, an
        // extra empty line would appear below the title.
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
        // There is no description line for this section, so it is
        // necessary to eliminate that bit in the style flags that
        // are passed in. If the bit were not changed to 0, an
        // extra empty line would appear below the title.
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
        // Calculator section
        // There is no description line for this section, so it is
        // necessary to eliminate that bit in the style flags that
        // are passed in. If the bit were not changed to 0, an
        // extra empty line would appear below the title.
        section = FormHelper.createSectionComposite(body, "Evaluate Constant Expression", "", toolkit, sectionFlags
                & ~Section.DESCRIPTION, getExpansionListener());

        Composite resultArea = (Composite) section.getClient();
        GridLayout gLayout = new GridLayout(2, false);
        gLayout.marginHeight = 0;
        resultArea.setLayout(gLayout);

        Composite expressionComposite = toolkit.createComposite(resultArea);
        expressionComposite.setLayoutData(new GridData(SWT.FILL, SWT.FILL, false, false));
        gLayout = new GridLayout(1, false);
        gLayout.marginHeight = 0;
        gLayout.marginBottom = 5;
        expressionComposite.setLayout(gLayout);

        toolkit.createLabel(expressionComposite, "Expression: ");
        expressionEvalInput = FormHelper.createFormsSourceViewer(toolkit, expressionComposite, textFieldFlags);

        // We want the value section to get larger as the window
        // gets larger but not the expression section.
        Composite valueComposite = toolkit.createComposite(resultArea);
        valueComposite.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
        valueComposite.setLayout(gLayout);
        toolkit.createLabel(valueComposite, "Value: ");
        expressionEvalResult = FormHelper.createFormsOutputViewer(toolkit, valueComposite, textFieldFlags);

        // We dont want these items to fill excess
        // vertical space because then in some cases
        // this causes the text box to be extremely
        // tall instead of having a scroll bar.
        gd = new GridData(SWT.FILL, SWT.FILL, true, false);
        gd.minimumWidth = 500;
        gd.heightHint = 80;
        expressionEvalResult.getTextWidget().setLayoutData(gd);
        // The expression section should not grab excess horizontal
        // space because if this flag is set to true and the length
        // of the expression causes a vertical scroll bar to appear,
        // then when the model is run, the expression text box
        // will get wide enough to fit the entire expression on
        // one line instead of wrapping the text.
        gd = new GridData(SWT.FILL, SWT.FILL, false, false);
        gd.widthHint = 500;
        gd.heightHint = 80;
        expressionEvalInput.getTextWidget().setLayoutData(gd);
        // We want this font to be the same as the input.
        // If it was not set it would be the same as the font
        // in the module editor.
        expressionEvalResult.getTextWidget().setFont(JFaceResources.getTextFont());
        expressionEvalInput.getTextWidget().setFont(JFaceResources.getTextFont());
        // This is required to paint the borders of the text boxes
        // it must be called on the direct parent of the widget
        // with a border. There is a call of this methon in
        // FormHelper.createSectionComposite, but that is called
        // on the section which is not a direct parent of the
        // text box widget.
        toolkit.paintBordersFor(expressionComposite);
        toolkit.paintBordersFor(valueComposite);

        ValidateableSectionPart calculatorSectionPart = new ValidateableSectionPart(section, this, SEC_EXPRESSION);
        // This ensures that when the part is made dirty, the model
        // appears unsaved.
        managedForm.addPart(calculatorSectionPart);

        // This makes the widget unsaved when text is entered.
        expressionEvalInput.getTextWidget().addModifyListener(new DirtyMarkingListener(calculatorSectionPart, false));

        getDataBindingManager().bindAttribute(MODEL_EXPRESSION_EVAL, expressionEvalInput, calculatorSectionPart);

        // -------------------------------------------------------------------
        // output section
        section = FormHelper.createSectionComposite(body, "User Output",
                "TLC output generated by evaluating Print and PrintT expressions.", toolkit, sectionFlags,
                getExpansionListener());
        Composite outputArea = (Composite) section.getClient();
        outputArea.setLayout(new GridLayout());
        // output viewer
        userOutput = FormHelper.createFormsOutputViewer(toolkit, outputArea, textFieldFlags);

        // We dont want this item to fill excess
        // vertical space because then in some cases
        // this causes the text box to be extremely
        // tall instead of having a scroll bar.
        gd = new GridData(SWT.FILL, SWT.LEFT, true, false);
        gd.heightHint = 300;
        gd.minimumWidth = 300;
        userOutput.getControl().setLayoutData(gd);

        // -------------------------------------------------------------------
        // progress section
        // There is no description line for this section, so it is
        // necessary to eliminate that bit in the style flags that
        // are passed in. If the bit were not changed to 0, an
        // extra empty line would appear below the title.
        section = FormHelper.createSectionComposite(body, "Progress Output", "",
        /* "The current progress of model-checking",*/
        toolkit, sectionFlags & ~Section.DESCRIPTION, getExpansionListener());
        section.setExpanded(false);
        Composite progressArea = (Composite) section.getClient();
        progressArea = (Composite) section.getClient();
        progressArea.setLayout(new GridLayout());

        progressOutput = FormHelper.createFormsOutputViewer(toolkit, progressArea, textFieldFlags);
        // We dont want this item to fill excess
        // vertical space because then in some cases
        // this causes the text box to be extremely
        // tall instead of having a scroll bar.
        gd = new GridData(SWT.FILL, SWT.LEFT, true, false);
        gd.heightHint = 300;
        gd.minimumWidth = 300;
        progressOutput.getControl().setLayoutData(gd);

    }

    /**
     * Save data back to model
     */
    public void commit(boolean onSave)
    {
        String expression = this.expressionEvalInput.getDocument().get();
        getConfig().setAttribute(MODEL_EXPRESSION_EVAL, expression);

        super.commit(onSave);
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
