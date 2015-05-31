package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.List;
import java.util.TimeZone;
import java.util.Vector;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.resources.WorkspaceJob;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.PaintEvent;
import org.eclipse.swt.events.PaintListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;
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
import org.eclipse.ui.progress.UIJob;
import org.lamport.tla.toolbox.tool.tlc.output.data.CoverageInformationItem;
import org.lamport.tla.toolbox.tool.tlc.output.data.ITLCModelLaunchDataPresenter;
import org.lamport.tla.toolbox.tool.tlc.output.data.StateSpaceInformationItem;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.contribution.DynamicContributionItem;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.ValidateableSectionPart;
import org.lamport.tla.toolbox.tool.tlc.ui.preference.ITLCPreferenceConstants;
import org.lamport.tla.toolbox.tool.tlc.ui.util.ActionClickListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.DirtyMarkingListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.view.TLCErrorView;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.FontPreferenceChangeListener;
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
    // startTime is provided by the TLCModelLaunchDataProvider's getStartTime()
    // method.
    private long startTime = 0;
    private Text finishTimestampText;
    private Text lastCheckpointTimeText;
    private Text coverageTimestampText;
    private Text currentStatusText;
    private Text fingerprintCollisionProbabilityText;
    private TableViewer coverage;
    private TableViewer stateSpace;

    private final Lock disposeLock = new ReentrantLock(true);

    // listener on changes to the tlc output font preference
    private FontPreferenceChangeListener fontChangeListener;

    // hyper link listener activated in case of errors
    protected IHyperlinkListener errorHyperLinkListener = new HyperlinkAdapter() {

        public void linkActivated(HyperlinkEvent e)
        {
            if (getConfig() != null)
            {
                try
                {
                    ModelHelper.setOriginalTraceShown(getConfig(), true);
                } catch (CoreException e1)
                {
                    TLCUIActivator.getDefault().logError("Error setting the original trace to be shown.", e1);
                }
                TLCErrorView.updateErrorView(getConfig());
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
			public void run() {
				// Acquire dispose lock prior to widget access. Using a single
				// lock just to serialize dispose and modelChange seems
				// overkill, but the wait-for graph becomes tricky with all the
				// background jobs going on (at least too tricky to get it
				// solved within an hour).
            	disposeLock.lock();
            	try {
                	if (getPartControl().isDisposed()) {
            			// Don't update the widgets if the underlying SWT control has
            			// already been disposed. Otherwise it results in an
            			// "SWTException: Widget is disposed".
                		return;
                	}
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
	                    ResultPage.this.startTimestampText.setText(new Date(dataProvider.getStartTimestamp()).toString());
	                    ResultPage.this.startTime = dataProvider.getStartTime();
	                    break;
	                case END_TIME:
	                    long finishTimestamp = dataProvider.getFinishTimestamp();
	                    if(finishTimestamp < 0) {
	                    	ResultPage.this.finishTimestampText.setText("");
	                    	break;
	                    }
	                    ResultPage.this.finishTimestampText.setText(new Date(finishTimestamp).toString());
	                    
	                    // calc elapsed time and set as Tooltip
	                    final SimpleDateFormat sdf = new SimpleDateFormat("HH:mm:ss");
	                    sdf.setTimeZone(TimeZone.getTimeZone("GMT")); // explicitly set TZ to handle local offset
	                    long elapsedTime = finishTimestamp - dataProvider.getStartTimestamp();
	                    ResultPage.this.finishTimestampText.setToolTipText(sdf.format(new Date(elapsedTime)));
	                    ResultPage.this.startTimestampText.setToolTipText(sdf.format(new Date(elapsedTime)));
	                    break;
	                case LAST_CHECKPOINT_TIME:
	                    long lastCheckpointTimeStamp = dataProvider.getLastCheckpointTimeStamp();
	                    if(lastCheckpointTimeStamp > 0) {
	                    	ResultPage.this.lastCheckpointTimeText.setText(new Date(lastCheckpointTimeStamp).toString());
	                    	break;
	                    }
	                   	ResultPage.this.lastCheckpointTimeText.setText("");
	                   	break;
	                case CURRENT_STATUS:
	                    ResultPage.this.currentStatusText.setText(dataProvider.getCurrentStatus());
	                    break;
	                case FINGERPRINT_COLLISION_PROBABILITY:
	                    ResultPage.this.fingerprintCollisionProbabilityText.setText(dataProvider.getFingerprintCollisionProbability());
	                    break;
	                case COVERAGE_TIME:
	                    ResultPage.this.coverageTimestampText.setText(dataProvider.getCoverageTimestamp());
	                    break;
	                case COVERAGE:
	                    ResultPage.this.coverage.setInput(dataProvider.getCoverageInfo());
	                    break;
	                case PROGRESS:
	                    ResultPage.this.stateSpace.setInput(dataProvider.getProgressInformation());
	
	                    // The following code finds all the graph windows (shells) for this
	                    // model and calls redraw() and update() on them, which apparently is the
	                    // magic incantation to cause its listener to be called to issue the
	                    // necessary commands to redraw the data and then displays the result.
	                    String suffix = getGraphTitleSuffix(ResultPage.this);
	                    Shell[] shells = UIHelper.getCurrentDisplay().getShells();
	                    for (int i = 0; i < shells.length; i++)
	                    {
	                        if (shells[i].getText().endsWith(suffix))
	                        {
	                            shells[i].redraw();
	                            shells[i].update();
	                            // The following was commented out by LL on 6 Jul 2012 because it was filling
	                            // up the Console log with useless stuff.
	                            // TLCUIActivator.getDefault().logDebug("Called redraw/update on shell number" + i);
	                        }
	                    }
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
	                    TLCErrorView.updateErrorView(dataProvider.getConfig());
	                    break;
	                default:
	                    break;
	                }
            	} finally {
            		disposeLock.unlock();
            	}
            }
        });

    }

    /**
     * Gets the data provider for the current page
     */
    public void loadData() throws CoreException
    {

        TLCOutputSourceRegistry modelCheckSourceRegistry = TLCOutputSourceRegistry.getModelCheckSourceRegistry();
		TLCModelLaunchDataProvider provider = modelCheckSourceRegistry.getProvider(getConfig());
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
        // TLCUIActivator.getDefault().logDebug("Entering reinit()");
    	disposeLock.lock();
    	try {
    		if (getPartControl().isDisposed()) {
    			// Cannot access widgets past their disposal
    			return;
    		}
    		this.startTimestampText.setText("");
    		this.startTime = 0;
    		this.finishTimestampText.setText("");
    		this.lastCheckpointTimeText.setText("");
    		this.currentStatusText.setText(TLCModelLaunchDataProvider.NOT_RUNNING);
    		this.errorStatusHyperLink.setText(TLCModelLaunchDataProvider.NO_ERRORS);
    		this.coverage.setInput(new Vector<CoverageInformationItem>());
    		this.stateSpace.setInput(new Vector<StateSpaceInformationItem>());
    		this.progressOutput.setDocument(new Document(TLCModelLaunchDataProvider.NO_OUTPUT_AVAILABLE));
    		this.userOutput.setDocument(new Document(TLCModelLaunchDataProvider.NO_OUTPUT_AVAILABLE));
    	} finally {
    		disposeLock.unlock();
    	}
        // TLCUIActivator.getDefault().logDebug("Exiting reinit()");
    }

    /**
     * Dispose the page
     */
    public void dispose()
    {
    	disposeLock.lock();
    	try {
        /*
         * Remove graph windows raised for the page.
         */
        String suffix = getGraphTitleSuffix(this);
        Shell[] shells = UIHelper.getCurrentDisplay().getShells();
        for (int i = 0; i < shells.length; i++)
        {
            if (shells[i].getText().endsWith(suffix))
            {
                shells[i].dispose();
            }
        }

        JFaceResources.getFontRegistry().removeListener(fontChangeListener);

        TLCModelLaunchDataProvider provider = TLCOutputSourceRegistry.getModelCheckSourceRegistry().getProvider(
                getConfig());
        if (provider != null)
        {
            provider.setPresenter(null);
        }
        super.dispose();
    	} finally {
    		disposeLock.unlock();
    	}
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
        // fingerprint collision probability
        this.fingerprintCollisionProbabilityText = FormHelper.createTextLeft("Fingerprint collision probability:", statusComposite, toolkit);
        this.fingerprintCollisionProbabilityText.setEditable(false);
        this.fingerprintCollisionProbabilityText.setText("");

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
        createAndSetupStateSpace("State space progress (click column header for graph)", statArea, toolkit);
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
        getDataBindingManager().bindSection(calculatorSectionPart, SEC_EXPRESSION, getId());

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
        userOutput.getControl().setFont(JFaceResources.getFont(ITLCPreferenceConstants.I_TLC_OUTPUT_FONT));

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
        progressOutput.getControl().setFont(JFaceResources.getFont(ITLCPreferenceConstants.I_TLC_OUTPUT_FONT));

        Vector<Control> controls = new Vector<Control>();
        controls.add(userOutput.getControl());
        controls.add(progressOutput.getControl());
        fontChangeListener = new FontPreferenceChangeListener(controls, ITLCPreferenceConstants.I_TLC_OUTPUT_FONT);

        JFaceResources.getFontRegistry().addListener(fontChangeListener);
        
        headClientTBM.add(new DynamicContributionItem(new LoadOutputAction()));
    }

	class LoadOutputAction extends Action {
		public LoadOutputAction() {
			super("Load output", TLCUIActivator.imageDescriptorFromPlugin(
					TLCUIActivator.PLUGIN_ID,
					"icons/full/copy_edit.gif"));
			setDescription("Loads the output from an external model run (requires \"-tool\" parameter) corresponding to this model.");
			setToolTipText(
					"Loads an existing output (e.g. from a standlone TLC run that corresponds to this model). Output has to contain tool markers. Run TLC with \"-tool\" command line parameter.	");
		}

		public void run() {
			// Get the user input (the path to the TLC output file).
			final FileDialog fileDialog = new FileDialog(new Shell());
			final String path = fileDialog.open();
			
			// I/O operations should never run inside the UI thread.
			final Job j = new WorkspaceJob("Loading output file...") {
				public IStatus runInWorkspace(final IProgressMonitor monitor) throws CoreException {
					try {
						// Import the file into the Toolbox on the file/resource layer.
						final TLCOutputSourceRegistry modelCheckSourceRegistry = TLCOutputSourceRegistry
								.getModelCheckSourceRegistry();
						modelCheckSourceRegistry
								.removeTLCStatusSource(new ILaunchConfiguration[] { getConfig() });
						ModelHelper.createModelOutputLogFile(getConfig(),
								new FileInputStream(new File(path)), monitor);
						
						// Once the output has been imported on the
						// file/resource layer, update the UI.
						final Job job = new UIJob("Updating results page with loaded output...") {
							public IStatus runInUIThread(IProgressMonitor monitor) {
								try {
									ResultPage.this.loadData();
								} catch (CoreException e) {
									return new Status(IStatus.ERROR, TLCUIActivator.PLUGIN_ID, e.getMessage(), e);
								}
								return Status.OK_STATUS;
							}
						};
						job.schedule();
						
					} catch (FileNotFoundException e) {
						return new Status(IStatus.ERROR, TLCUIActivator.PLUGIN_ID, e.getMessage(), e);
					}
	                return Status.OK_STATUS;
				}
			};
		   	final IWorkspace workspace = ResourcesPlugin.getWorkspace();
			j.setRule(workspace.getRuleFactory().buildRule());
			j.schedule();
		}
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

        StateSpaceLabelProvider.createTableColumns(stateTable, this);

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
        getSite().setSelectionProvider(this.stateSpace);
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

        final Table stateTable = toolkit.createTable(coverageComposite, SWT.MULTI | SWT.FULL_SELECTION | SWT.V_SCROLL
                | SWT.BORDER | SWT.VIRTUAL);
        gd = new GridData(CoverageLabelProvider.MIN_WIDTH, 100);
        gd.horizontalSpan = 2;
        stateTable.setLayoutData(gd);

        stateTable.setHeaderVisible(true);
        stateTable.setLinesVisible(true);
        stateTable.setToolTipText(TOOLTIP);

        CoverageLabelProvider.createTableColumns(stateTable);

        // create the viewer
        this.coverage = new TableViewer(stateTable);

        coverage.getTable().addMouseListener(new ActionClickListener(this.coverage));

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
        
        getSite().setSelectionProvider(this.coverage);
        
        return coverageComposite;
    }

    /**
     * Returns the StateSpaceInformationItem objects currently being displayed in 
     * the "State space progress" area, except in temporal order--that is, in the
     * opposite order from which they are displayed.
     * 
     * @return
     */
    public StateSpaceInformationItem[] getStateSpaceInformation()
    {
		List<StateSpaceInformationItem> infoList = (List<StateSpaceInformationItem>) stateSpace.getInput();
        StateSpaceInformationItem[] result = new StateSpaceInformationItem[infoList.size()];
        for (int i = 0; i < result.length; i++)
        {
            result[i] = infoList.get(result.length - i - 1);
        }
        return result;

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
        public static void createTableColumns(Table stateTable, ResultPage page)
        {
            // create table headers
            for (int i = 0; i < columnTitles.length; i++)
            {
                TableColumn column = new TableColumn(stateTable, SWT.NULL);
                column.setWidth(columnWidths[i]);
                column.setText(columnTitles[i]);

                // The following statement attaches a listener to the column
                // header. See the ResultPageColumnListener comments.

                column.addSelectionListener(new ResultPageColumnListener(i, page));
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

    /**
     * A ResultPageColumnListener is a listener that handles clicks on
     * the column headers of the "State space progress" region of the
     * Result Page.  The same class is used for all the column
     * headers, with the column number indicating which column header
     * was clicked on.
     * 
     * @author lamport
     *
     */
    static class ResultPageColumnListener implements SelectionListener
    {

        private int columnNumber;
        private ResultPage resultPage;

        public ResultPageColumnListener(int columnNumber, ResultPage resultPage)
        {
            super();
            this.columnNumber = columnNumber;
            this.resultPage = resultPage;
        }

        /* (non-Javadoc)
         * @see org.eclipse.swt.events.SelectionListener#widgetDefaultSelected(org.eclipse.swt.events.SelectionEvent)
         */
        public void widgetDefaultSelected(SelectionEvent e)
        {
        	// nop
        }

        /**
         * This is called when the user clicks on the header of a column
         * of the "State space progress" region of the ResultsPage.  It 
         * raises a window with a graph of the specified column.
         */
        public void widgetSelected(SelectionEvent e)
        {
            UIHelper.runUIAsync(new DataDisplay(resultPage, columnNumber));

        }

    }

    /**
     * The run method of this class creates a shell (a window) to display
     * a graph of the appropriate State Space Progress information when the user clicks on
     * a column heading.  It then adds a PaintListener to that shell, and that 
     * listener draws the graph initially and whenever the window is resized or
     * some other event requires it to be redrawn.
     * 
     * The constructor is used to pass the arguments needed by the run method to
     * display the data.
     * 
     * Note: The location at which the shells are displayed is fixed in code
     * buried deeply.  There should probably be some thought given to where to
     * pop up the window, and perhaps a window should be popped up in the same
     * place as the last such window was popped--perhaps with a bit of random
     * variation to prevent them all from piling up.
     *  
     * @author lamport
     *
     */
    static class DataDisplay implements Runnable
    {
        int columnNumber;
        ResultPage resultPage;

        /**
         *  The constructor returns an object with null data and times arrays
         *  if there are not at least two data points.  
         *  
         * @param ssInfo
         * @param columnNumber
         */
        public DataDisplay(ResultPage resultPage, int columnNumber)
        {

            this.resultPage = resultPage;
            this.columnNumber = columnNumber;
        }

        /**
         * Much of the stuff in this run() method was copied, without much
         * understanding from Snippet245.java in the Eclipse examples.
         */
        public void run()
        {

            /*
             * The data and times arrays are set to contain the data items to be displayed
             * and the elapsed time (in milliseconds) at which each item was posted.
             * The data is obtained from the appropriate column of the ssInfo items.
             * For the Time column, the number of reports is graphed.
             */

            // The following method for getting the current display was
            // copied without understanding from someplace or other.

            String title = getGraphTitle(columnNumber, resultPage);

            // We check if a shell exists with this title, and use it if
            // it does. Otherwise, we get a new shell.
            Display display = UIHelper.getCurrentDisplay();
            boolean shellExists = false;
            Shell theShell = null;
            Shell[] shells = display.getShells();
            for (int i = 0; i < shells.length; i++)
            {
                if (shells[i].getText().equals(title))
                {
                    theShell = shells[i];
                    shellExists = true;
                    break;
                }
            }
            if (!shellExists)
            {
                theShell = new Shell(display, SWT.SHELL_TRIM);
            }
            final Shell shell = theShell;
            shell.setText(title);
            shell.setActive(); // should cause it to pop up to the top.
            if (shellExists)
            {
                shell.redraw();
                shell.update();
            } else
            {
                shell.addPaintListener(new PaintListener() {
                    public void paintControl(PaintEvent event)
                    {
                        StateSpaceInformationItem[] ssInfo = resultPage.getStateSpaceInformation();
                        if (ssInfo.length < 2)
                        {
                            return;
                        }

                        final long[] data = new long[ssInfo.length + 1];
                        long[] times = new long[ssInfo.length + 1];
                        data[0] = 0;
                        times[0] = 0;

                        long startTime = resultPage.startTime;
                        TLCUIActivator.getDefault().logDebug("first reported time - starttime = "
                                + (ssInfo[0].getTime().getTime() - startTime));
                        if (startTime > ssInfo[0].getTime().getTime() - 1000)
                        {
                            startTime = ssInfo[0].getTime().getTime() - 1000;
                        }
                        for (int i = 1; i < data.length; i++)
                        {
                            switch (columnNumber) {
                            case StateSpaceLabelProvider.COL_TIME:
                                data[i] = i - 1;
                                break;
                            case StateSpaceLabelProvider.COL_DIAMETER:
                                data[i] = ssInfo[i - 1].getDiameter();
                                break;
                            case StateSpaceLabelProvider.COL_FOUND:
                                data[i] = ssInfo[i - 1].getFoundStates();
                                break;
                            case StateSpaceLabelProvider.COL_DISTINCT:
                                data[i] = ssInfo[i - 1].getDistinctStates();
                                break;
                            case StateSpaceLabelProvider.COL_LEFT:
                                data[i] = ssInfo[i - 1].getLeftStates();
                                break;
                            default:
                                return;
                            }
                            times[i] = ssInfo[i - 1].getTime().getTime() - startTime;
                        }

                        Rectangle rect = shell.getClientArea();
                        // Set maxData to the largest data value;
                        long maxData = 0;
                        for (int i = 0; i < data.length; i++)
                        {
                            if (data[i] > maxData)
                            {
                                maxData = data[i];
                            }
                        }
                        long maxTime = times[times.length - 1];

                        // event.gc.drawOval(0, 0, rect.width - 1, rect.height - 1);
                        if (maxTime > 0)
                        {
                        	// In case maxData equals 0, we use 1 instead for computing
                        	// the coordinates of the points.
                        	// (Added by LL on 6 July 2011 to fix division by zero bug.)
                        	long maxDataVal = maxData ;
                        	if (maxDataVal == 0) {
                        		maxDataVal = 1;
                        	}
                            int[] pointArray = new int[2 * data.length];
                            for (int i = 0; i < data.length; i++)
                            {
                                pointArray[2 * i] = (int) ((times[i] * rect.width) / maxTime);
                                pointArray[(2 * i) + 1] = (int) (rect.height - ((data[i] * rect.height) / maxDataVal));
                            }
                            event.gc.drawPolyline(pointArray);
                        }
                        String stringTime = "Time: ";
                        long unreportedTime = maxTime;
                        long days = maxTime / (1000 * 60 * 60 * 24);
                        if (days > 0)
                        {
                            unreportedTime = unreportedTime - days * (1000 * 60 * 60 * 24);
                            stringTime = stringTime + days + ((days == 1) ? (" day ") : (" days  "));

                        }
                        long hours = unreportedTime / (1000 * 60 * 60);
                        if (hours > 0)
                        {
                            unreportedTime = unreportedTime - hours * (1000 * 60 * 60);
                            stringTime = stringTime + hours + ((hours == 1) ? (" hour ") : (" hours  "));
                        }
                        unreportedTime = (unreportedTime + (1000 * 26)) / (1000 * 60);
                        stringTime = stringTime + unreportedTime
                                + ((unreportedTime == 1) ? (" minute ") : (" minutes  "));
                        event.gc.drawString(stringTime, 0, 0);
                        event.gc.drawString("Current: " + data[data.length - 1], 0, 15);
                        if (maxData != data[data.length - 1])
                        {
                            event.gc.drawString("Maximum: " + maxData, 0, 30);
                        }
                    }
                });
            }
            ;
            if (!shellExists)
            {
                shell.setBounds(100 + 30 * columnNumber, 100 + 30 * columnNumber, 400, 300);
            }
            shell.open();
            // The following code from the Eclipse example was eliminated.
            // It seems to cause the shell to survive after the Toolbox is
            // killed.
            //
            // while (!shell.isDisposed()) {
            // if (!display.readAndDispatch()) display.sleep();
            // }

        }

    }

    /**
     * The title of a graph consists of two parts:  the prefix, which
     * identifies the column, and the suffix, which identifies the model.
     * When we dispose of the ResultPage, we must dispose of all graph
     * window (shells) for that model.
     * 
     * @param resultPage
     * @return
     */
    private static String getGraphTitleSuffix(ResultPage resultPage)
    {
        return "(" + ModelHelper.getModelName(resultPage.getConfig().getFile()) + ")";
    }

    private static String getGraphTitle(int columnNumber, ResultPage resultPage)
    {
        String title = StateSpaceLabelProvider.columnTitles[columnNumber];
        if (columnNumber == StateSpaceLabelProvider.COL_TIME)
        {
            title = "Number of Progress Reports";
        }
        return title + " " + getGraphTitleSuffix(resultPage);
    }

}
