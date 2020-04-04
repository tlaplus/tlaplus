package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.results;

import java.io.Closeable;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.Vector;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import org.apache.commons.lang3.time.DurationFormatUtils;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.resources.WorkspaceJob;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.layout.TableColumnLayout;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.mylyn.commons.notifications.core.INotificationService;
import org.eclipse.mylyn.commons.notifications.ui.NotificationsUi;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Item;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Layout;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.editor.IFormPage;
import org.eclipse.ui.forms.events.ExpansionAdapter;
import org.eclipse.ui.forms.events.ExpansionEvent;
import org.eclipse.ui.forms.events.HyperlinkAdapter;
import org.eclipse.ui.forms.events.HyperlinkEvent;
import org.eclipse.ui.forms.events.IHyperlinkListener;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Hyperlink;
import org.eclipse.ui.forms.widgets.Section;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.progress.UIJob;
import org.lamport.tla.toolbox.editor.basic.TLAEditorActivator;
import org.lamport.tla.toolbox.editor.basic.TLAFastPartitioner;
import org.lamport.tla.toolbox.editor.basic.TLAPartitionScanner;
import org.lamport.tla.toolbox.spec.Module;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.model.ModelCoverage;
import org.lamport.tla.toolbox.tool.tlc.output.data.ActionInformationItem;
import org.lamport.tla.toolbox.tool.tlc.output.data.CoverageInformation;
import org.lamport.tla.toolbox.tool.tlc.output.data.CoverageInformationItem;
import org.lamport.tla.toolbox.tool.tlc.output.data.CoverageUINotification;
import org.lamport.tla.toolbox.tool.tlc.output.data.ITLCModelLaunchDataPresenter;
import org.lamport.tla.toolbox.tool.tlc.output.data.StateSpaceInformationItem;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCError;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.contribution.DynamicContributionItem;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.DataBindingManager;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ISectionConstants;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.TLACoverageEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.BasicFormPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.ErrorMessage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.MainModelPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.advanced.AdvancedModelPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.advanced.AdvancedTLCOptionsPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.ValidateableSectionPart;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.preference.IModelEditorPreferenceConstants;
import org.lamport.tla.toolbox.tool.tlc.ui.preference.ITLCPreferenceConstants;
import org.lamport.tla.toolbox.tool.tlc.ui.util.DirtyMarkingListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.util.RecordToSourceCoupler;
import org.lamport.tla.toolbox.tool.tlc.ui.view.TLCErrorView;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.FontPreferenceChangeListener;
import org.lamport.tla.toolbox.util.IHelpConstants;
import org.lamport.tla.toolbox.util.UIHelper;

import tlc2.model.Assignment;

/**
 * A page to display results of model checking.
 * @author Simon Zambrovski
 */
@SuppressWarnings("restriction")
public class ResultPage extends BasicFormPage implements Closeable, ITLCModelLaunchDataPresenter {
	public static final String RESULT_PAGE_PROBLEM = "ResultPageProblem";

    public static final String ID = "resultPage";

    /**
     * The title of a graph consists of two parts:  the prefix, which
     * identifies the column, and the suffix, which identifies the model.
     * When we dispose of the ResultPage, we must dispose of all graph
     * window (shells) for that model.
     * 
     * @param resultPage
     * @return the graph title suffix
     */
	static String getGraphTitleSuffix(ResultPage resultPage) {
		return "(" + resultPage.getModel().getName() + ")";
	}

	private static final Color ERROR_PANE_BACKGROUND = new Color(PlatformUI.getWorkbench().getDisplay(), 255, 241, 237);
	private static final SimpleDateFormat DATE_FORMATTER = new SimpleDateFormat("HH:mm:ss '('MMM d')'");
	
	
    /**
     * UI elements
     */
    private SourceViewer userOutput;
    private SourceViewer progressOutput;
    
    private Composite calculatorSection;
    private SourceViewer expressionEvalResult;
    private SourceViewer expressionEvalInput;
	private ValidateableSectionPart validateableCalculatorSection;
	private Button noBehaviorModeToggleButton;

	private Section generalSection;
	private int collapsedSectionHeight = 20;		// We should be able to calculate this before we need; this is the 'just in case' value
	private long startTimestamp;
    private Composite generalTopPane;
    private Label startLabel;
    private Label lastCheckpointLabel;
    private Label finishLabel;
    private Label tlcSimulationLabel;    
    private Label tlcSearchModeLabel;
    private Label tlcStatusLabel;

    private Composite generalErrorPane;
    private Hyperlink errorStatusHyperLink;
    private Label fingerprintCollisionLabel;

    private Text coverageTimestampText;
    private TableViewer coverage;
    private TableViewer stateSpace;
	private final Map<String, Section> sections = new HashMap<String, Section>();
    private final Lock disposeLock = new ReentrantLock(true);

    // listener on changes to the tlc output font preference
    private FontPreferenceChangeListener fontChangeListener;

    // hyper link listener activated in case of errors
    private final IHyperlinkListener m_errorHyperLinkListener = new HyperlinkAdapter() {
		public void linkActivated(final HyperlinkEvent e) {
			if (getModel() != null) {
				getModel().setOriginalTraceShown(true);
				TLCErrorView.updateErrorView(getModelEditor());
			}
		}
    };

	private IMarker incompleteStateExploration;
	
	private final INotificationService notificationService;
	
	private final ErrorPaneViewState errorPaneViewState;
	
	private final ArrayList<String> markedErrorMessages;

    /**
     * Constructor for the page
     * @param editor
     */
	public ResultPage(final FormEditor editor) {
        super(editor, ID, "Model Checking Results", "icons/full/results_page_" + IMAGE_TEMPLATE_TOKEN + ".png");
        helpId = IHelpConstants.RESULT_MODEL_PAGE;
        
        notificationService = NotificationsUi.getService();
        
        errorPaneViewState = new ErrorPaneViewState();
        markedErrorMessages = new ArrayList<>();
    }

	@Override
    public void modelCheckingWillBegin() {
		errorPaneViewState.clearState();
		markedErrorMessages.clear();
		getManagedForm().getMessageManager().removeAllMessages();
		PlatformUI.getWorkbench().getDisplay().syncExec(() -> {
			if (!tlcStatusLabel.isDisposed()) {
	    		tlcStatusLabel.setText("Starting...");
				errorStatusHyperLink.setVisible(errorPaneViewState.errorLinkIsDisplayed());
				fingerprintCollisionLabel.setVisible(errorPaneViewState.fingerprintIsDisplayed());
				setErrorPaneVisible(errorPaneViewState.shouldDisplay());
			}
		});
	}

    /**
     * Will be called by the provider on data changes
     */
	@Override
	public void modelChanged(final TLCModelLaunchDataProvider dataProvider, final int fieldId) {
		UIHelper.runUIAsync(() -> {
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
						userOutput.setDocument(dataProvider.getUserOutput());
						break;
					case PROGRESS_OUTPUT:
						progressOutput.setDocument(dataProvider.getProgressOutput());
						break;
					case CONST_EXPR_EVAL_OUTPUT:
						if (expressionEvalResult != null) {
							expressionEvalResult.getTextWidget().setText(dataProvider.getCalcOutput());
						}
						break;
					case START_TIME:
						setStartTime(dataProvider.getStartTimestamp());
						break;
					case END_TIME:
						setEndTime(dataProvider.getFinishTimestamp());

						final long delta = dataProvider.getFinishTimestamp() - dataProvider.getStartTimestamp();
						final String duration = DurationFormatUtils.formatDuration(delta, "HH'hrs' mm'mins' ss'sec'");
						startLabel.setToolTipText(duration);
						finishLabel.setToolTipText(duration);
						break;
					case TLC_MODE:
						setSearchMode(dataProvider.getTLCMode());

						final IFormPage iep = getEditor().findPage(AdvancedTLCOptionsPage.ID);
						if (iep != null) {
							((AdvancedTLCOptionsPage) iep).setFpIndex(dataProvider.getFPIndex());
						} else {
							// The tab isn't open so set the value into the model and the tab, should it
							// open, will
							// load it out of the model.
							getModel().setAttribute(LAUNCH_FP_INDEX, dataProvider.getFPIndex());
							getModelEditor().saveModel();
						}
					case LAST_CHECKPOINT_TIME:
						setCheckpoint(dataProvider.getLastCheckpointTimeStamp());
						break;
					case CURRENT_STATUS:
						tlcStatusLabel.setText(dataProvider.getCurrentStatus());
						generalTopPane.layout(true, true);
						break;
					case FINGERPRINT_COLLISION_PROBABILITY:
						final String collisionText = dataProvider.getFingerprintCollisionProbability().trim();

						if (collisionText.length() == 0) {
							fingerprintCollisionLabel.setVisible(false);
							errorPaneViewState.setFingerprintDisplay(false);
							setErrorPaneVisible(errorPaneViewState.shouldDisplay());
						} else {
							fingerprintCollisionLabel.setText("Fingerprint collision probability: " + collisionText);
							fingerprintCollisionLabel.setVisible(true);
							errorPaneViewState.setFingerprintDisplay(true);
							setErrorPaneVisible(true);
						}
						break;
					case COVERAGE_TIME:
						final String coverageTimestamp = dataProvider.getCoverageTimestamp();
						if ("".equals(coverageTimestamp)) {
							// Reset
							coverageTimestampText.setText("");
						} else {
							// Print statistics timestamp relative to TLC startup.
							final Date date = TLCModelLaunchDataProvider.parseDate(coverageTimestamp);
							final String interval = TLCModelLaunchDataProvider.formatInterval(getStartTimestamp(),
									date.getTime());
							coverageTimestampText.setText(String.format("(at %s)", interval));
							coverageTimestampText.setToolTipText(
									"Time indicates the execution time at which the numbers were recorded");
						}
						break;
					case COVERAGE:
						final CoverageInformation coverageInfo = dataProvider.getCoverageInfo();
						coverage.setInput(coverageInfo);
						break;
					case COVERAGE_END_OVERHEAD:
						notificationService.notify(Collections.singletonList(new CoverageUINotification(getModelEditor())));
						// Continue with COVERAGE_END...
					case COVERAGE_END:
						final CoverageInformation ci = dataProvider.getCoverageInfo();
						if (ci.isEmpty() || ci.isLegacy()) {
							// Cannot show coverage information without (non-legacy) coverage data.
							break;
						}
						
						// Delete all zero coverage markers because they might have become obsolete
						// since the last reporting..
						// Consider this spec:
						// ----
						// Init == x = 1
						// A == x' = x + 1
						// B == TLCGet("duration") > 90 /\ x' = x
						// Spec == Init /\ [][A \/ B]_x
						// ----
						// With -coverage set to 1 (every  60 secs), the first coverage reporting
						// marks action B as disabled. However, in subsequent reportings, B is enabled.
						try {
							List<Module> modules = getModel().getSpec().getModules();
							for (Module module : modules) {
								module.getResource().deleteMarkers(ModelEditor.ZERO_COVERAGE_ACTION_MARKER, false,
										IResource.DEPTH_ZERO);
							}
						} catch (CoreException e) {
							TLCUIActivator.getDefault().logError(e.getMessage(), e);
						}

						final List<ActionInformationItem> zeroCoverageInformation = ci.getDisabledSpecActions();
						for (ActionInformationItem item : zeroCoverageInformation) {
							final Module m = getModel().getSpec().getModule(item.getModule());
							if (m == null) {
								// With the Toolbox better be safe than sorry.
								continue;
							}
							try {
								final IMarker createMarker = m.getResource()
										.createMarker(ModelEditor.ZERO_COVERAGE_ACTION_MARKER);

								createMarker.setAttribute(IMarker.MESSAGE,
										String.format("%s is never enabled.", item.getName()));
								createMarker.setAttribute(IMarker.LINE_NUMBER, item.getModuleLocation().beginLine());

								// In order to color/highlight the token itself, set char_start and char_end
								// too. At this point we decided it is too intrusive though.
//							final org.eclipse.jface.text.IRegion region = org.lamport.tla.toolbox.util.AdapterFactory
//									.locationToRegion(item.getModuleLocation());
//							createMarker.setAttribute(IMarker.CHAR_START, region.getOffset());
//							createMarker.setAttribute(IMarker.CHAR_END, region.getOffset() + region.getLength());
							} catch (CoreException e) {
								TLCUIActivator.getDefault().logError(e.getMessage(), e);
							}
						}

						// Do not open the dedicated coverage editor below if the user only requested
						// action-only coverage.
						if (ModelCoverage.ACTION.equals(getModel().getCoverage())) {
							break;
						}

						final ModelEditor modelEditor = (ModelEditor) getEditor();

						final List<IFile> savedTLAFiles = modelEditor.getModel().getSavedTLAFiles();
						for (IFile iFile : savedTLAFiles) {
							if (!ci.has(iFile)) {
								continue;
							}
							// Open the files as pages of the current model editor.
							final FileEditorInput input = new FileEditorInput(iFile);
							final IEditorPart[] findEditors = modelEditor.findEditors(input);
							try {
								if (findEditors.length == 0) {
									modelEditor.addPage(new TLACoverageEditor(ci.projectionFor(iFile)), input);
								} else {
									if (findEditors[0] instanceof TLACoverageEditor) {
										final TLACoverageEditor coverageEditor = (TLACoverageEditor) findEditors[0];
										coverageEditor.resetInput(ci.projectionFor(iFile));
									}
								}
							} catch (PartInitException e) {
								TLCUIActivator.getDefault().logError(e.getMessage(), e);
							}
						}
						break;
					case PROGRESS:
						stateSpace.setInput(dataProvider.getProgressInformation());

						// The following code finds all the graph windows (shells) for this
						// model and calls redraw() and update() on them, which apparently is the
						// magic incantation to cause its listener to be called to issue the
						// necessary commands to redraw the data and then displays the result.
						String suffix = getGraphTitleSuffix(ResultPage.this);
						Shell[] shells = UIHelper.getCurrentDisplay().getShells();
						for (int i = 0; i < shells.length; i++) {
							if (shells[i].getText().endsWith(suffix)) {
								shells[i].redraw();
								shells[i].update();
								// The following was commented out by LL on 6 Jul 2012 because it was filling
								// up the Console log with useless stuff.
								// TLCUIActivator.getDefault().logDebug("Called redraw/update on shell number" +
								// i);
							}
						}
						break;
					case WARNINGS:
						if (dataProvider.isSymmetryWithLiveness()) {
							final MainModelPage mmp = (MainModelPage) getModelEditor().getFormPage(MainModelPage.ID);
							final Optional<Assignment> possibleSymmetrySet = mmp.getConstants().stream()
									.filter(c -> c.isSymmetricalSet()).findFirst();
							if (possibleSymmetrySet.isPresent()) {
								final Assignment symmetrySet = possibleSymmetrySet.get();
								final String errorMessage = String.format("%s %s", symmetrySet.getLabel(),
										"declared to be symmetric. Liveness checking under symmetry might fail to find a violation.");
								getModelEditor().addErrorMessage(
										new ErrorMessage(errorMessage, symmetrySet.getLabel(), MainModelPage.ID,
												Arrays.asList(ISectionConstants.SEC_WHAT_IS_THE_MODEL,
														ISectionConstants.SEC_WHAT_TO_CHECK_PROPERTIES),
												IModelConfigurationConstants.MODEL_PARAMETER_CONSTANTS));
								final Hashtable<String, Object> marker = ModelHelper
										.createMarkerDescription(errorMessage, IMarker.SEVERITY_WARNING);
								getModel().setMarker(marker, ModelHelper.TLC_MODEL_ERROR_MARKER_TLC);
							}
						}
						if (dataProvider.isConstraintsWithLiveness()) {
							final String errorMessage = "Liveness checking with state or action constraints might fail to find a violation. "
									+ "Please read section 14.3.5 on page 247 of Specifying Systems "
									+ "(https://lamport.azurewebsites.net/tla/book.html) for more details.";
							getModelEditor().addErrorMessage(new ErrorMessage(errorMessage, "StateConstraintWarning",
									AdvancedModelPage.ID, Arrays.asList(ISectionConstants.SEC_STATE_CONSTRAINT),
									IModelConfigurationConstants.MODEL_PARAMETER_CONSTRAINT));
							final Hashtable<String, Object> marker = ModelHelper
									.createMarkerDescription(errorMessage, IMarker.SEVERITY_WARNING);
							getModel().setMarker(marker, ModelHelper.TLC_MODEL_ERROR_MARKER_TLC);
						}
						break;
					case ERRORS:
						final String text;
						final Color color;
						final boolean visible;
						final int errorCount = dataProvider.getErrors().size();
						switch (errorCount) {
							case 0:
								text = TLCModelLaunchDataProvider.NO_ERRORS;
								color = TLCUIActivator.getColor(SWT.COLOR_BLACK);
								errorStatusHyperLink.removeHyperlinkListener(m_errorHyperLinkListener);
								visible = false;
								break;
							case 1:
								text = "1 Error";
								errorStatusHyperLink.addHyperlinkListener(m_errorHyperLinkListener);
								color = TLCUIActivator.getColor(SWT.COLOR_RED);
								visible = true;
								break;
							default:
								text = String.valueOf(errorCount) + " Errors";
								errorStatusHyperLink.addHyperlinkListener(m_errorHyperLinkListener);
								color = TLCUIActivator.getColor(SWT.COLOR_RED);
								visible = true;
								break;
						}

						if (visible) {
							final ModelEditor editor = (ModelEditor)getEditor();
							final MainModelPage mmp = (MainModelPage)editor.findPage(MainModelPage.ID);
							
							mmp.addGlobalTLCErrorMessage(ResultPage.ID + "_err_" + errorCount);
						}
						
						synchronized (markedErrorMessages) {
							for (final TLCError error : dataProvider.getErrors()) {
								final String message = error.getMessage();
								if (!markedErrorMessages.contains(message)) {
									final Hashtable<String, Object> marker = ModelHelper
											.createMarkerDescription(message, IMarker.SEVERITY_ERROR);
									getModel().setMarker(marker, ModelHelper.TLC_MODEL_ERROR_MARKER_TLC);
									markedErrorMessages.add(message);
								}
							}
						}
						
						errorStatusHyperLink.setText(text);
						errorStatusHyperLink.setForeground(color);
						errorStatusHyperLink.setVisible(visible);
						errorPaneViewState.setErrorLinkDisplay(visible);
						setErrorPaneVisible(errorPaneViewState.shouldDisplay());

						// update the error view - previously (pre-201909) we used the Model instance
						// contained
						// in the data provider.
						TLCErrorView.updateErrorView(getModelEditor());
						break;
					default:
						break;
				}

				// Set label provider to highlight unexplored states if
				// TLC is done but not all states are explored.
				if (stateSpace.getLabelProvider() instanceof StateSpaceLabelProvider) {
					final StateSpaceLabelProvider sslp = (StateSpaceLabelProvider) stateSpace.getLabelProvider();
					if (dataProvider.isDone() && dataProvider.getProgressInformation().size() > 0) {
						final long statesLeft = dataProvider.getProgressInformation().get(0).getLeftStates();
						if (statesLeft > 0) {
							sslp.setHighlightUnexplored();
							// Create a problem marker which gets displayed by
							// BasicFormPage/ModelEditor as a warning on the
							// result page.
							if (incompleteStateExploration == null) {
								final Hashtable<String, Object> marker = ModelHelper.createMarkerDescription(
										"State space exploration incomplete", IMarker.SEVERITY_WARNING);
								marker.put(ModelHelper.TLC_MODEL_ERROR_MARKER_ATTRIBUTE_PAGE, ResultPage.ID);
								incompleteStateExploration = getModel().setMarker(marker,
										ModelHelper.TLC_MODEL_ERROR_MARKER_TLC);
							}
						} else {
							if (incompleteStateExploration != null) {
								try {
									incompleteStateExploration.delete();
									resetMessage(RESULT_PAGE_PROBLEM);
									incompleteStateExploration = null;
								} catch (CoreException e) {
									TLCUIActivator.getDefault().logError(e.getMessage(), e);
								}
							}
							sslp.unsetHighlightUnexplored();
						}
					}
					stateSpace.refresh();
				}
			} finally {
				disposeLock.unlock();
			}
		});
	}

    /**
     * {@inheritDoc}
     */
	@Override
	public void setFocus() {
		if ((expressionEvalInput != null) && !expressionEvalInput.getTextWidget().isDisposed()
										  && !expressionEvalInput.getTextWidget().isFocusControl()) {
			final StyledText st = expressionEvalInput.getTextWidget();
			final int caretOffset = st.getText().length();
			
			st.setFocus();
			
			/*
			 * We get a focus notification at least 3 times after TLC execution finishes, in which none of those times
			 * 	does the text widget believe itself focused. Further, the text widget gaining focus resets its caret
			 * 	offset to 0; so, nearly ubiquitously we end up with the caret offset position set invocation never
			 * 	sticking. We resort to this waiting-out-the-notification-storm ugly hack to get the caret set
			 *  to stick; were we getting more than 3 notifications, i would use a thread pool to gate proliferation
			 *  here.
			 */
			final Runnable ohSWT = () -> {
				try {
					Thread.sleep(75);
				} catch (Exception e) { }
				
				if (!st.isDisposed()) {
					st.getDisplay().asyncExec(() -> {
						if (!st.isDisposed()) {
							st.setCaretOffset(caretOffset);
						}
					});
				}
			};
			(new Thread(ohSWT)).start();
		}
	}
    
    /**
     * Gets the data provider for the current page
     */
    @Override
	public void loadData() throws CoreException {
    	final TLCOutputSourceRegistry modelCheckSourceRegistry = TLCOutputSourceRegistry.getModelCheckSourceRegistry();
    	final TLCModelLaunchDataProvider provider = modelCheckSourceRegistry.getProvider(getModel());
		if (provider != null) {
			provider.addDataPresenter(this);
		} else {
			// no data provider
			reinit();
		}

		// constant expression
		final Document document = new Document(getModel().getEvalExpression());
		final IDocumentPartitioner partitioner = new TLAFastPartitioner(
				TLAEditorActivator.getDefault().getTLAPartitionScanner(), TLAPartitionScanner.TLA_PARTITION_TYPES);
		document.setDocumentPartitioner(TLAPartitionScanner.TLA_PARTITIONING, partitioner);
		partitioner.connect(document);
		if (expressionEvalInput != null) {
			expressionEvalInput.setDocument(document);
		}
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
    			return;
    		}
    		
    		startTimestamp = 0;
    		startLabel.setText("");
    		lastCheckpointLabel.setText("");
    		finishLabel.setText("");
    		tlcSimulationLabel.setVisible(false);
    		tlcSearchModeLabel.setText("");
    		tlcStatusLabel.setText(TLCModelLaunchDataProvider.NOT_RUNNING);
    		errorStatusHyperLink.setText(TLCModelLaunchDataProvider.NO_ERRORS);
            errorStatusHyperLink.setVisible(false);
            fingerprintCollisionLabel.setText("");
            fingerprintCollisionLabel.setVisible(false);
    		coverage.setInput(new Vector<CoverageInformationItem>());
    		stateSpace.setInput(new Vector<StateSpaceInformationItem>());
    		progressOutput.setDocument(new Document(TLCModelLaunchDataProvider.NO_OUTPUT_AVAILABLE));
    		userOutput.setDocument(new Document(TLCModelLaunchDataProvider.NO_OUTPUT_AVAILABLE));

    		setErrorPaneVisible(false);
        	
        	generalTopPane.layout(true, true);
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
			for (int i = 0; i < shells.length; i++) {
				if (shells[i].getText().endsWith(suffix)) {
					shells[i].dispose();
				}
			}

			if (incompleteStateExploration != null) {
				incompleteStateExploration.delete();
				incompleteStateExploration = null;
			}

			JFaceResources.getFontRegistry().removeListener(fontChangeListener);

			final Model model = getModel();
			final TLCOutputSourceRegistry modelCheckSourceRegistry = TLCOutputSourceRegistry.getModelCheckSourceRegistry();
			// Do not initialize provider in dispose if it hasn't been initialized yet.
			if (modelCheckSourceRegistry.hasProvider(model)) {
				final TLCModelLaunchDataProvider provider = modelCheckSourceRegistry.getProvider(model);
				if (provider != null) {
					provider.removeDataPresenter(this);
				}
			}
			super.dispose();
		} catch (CoreException e) {
			e.printStackTrace();
		} finally {
			disposeLock.unlock();
		}
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
	protected Layout getBodyLayout() {
		return FormHelper.createFormTableWrapLayout(true, 1);
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
	protected void createBodyContent(IManagedForm managedForm) {
        final int sectionFlags = Section.TITLE_BAR | Section.DESCRIPTION | Section.TREE_NODE | Section.EXPANDED | SWT.WRAP;
        final int textFieldFlags = SWT.MULTI | SWT.V_SCROLL | SWT.H_SCROLL | SWT.READ_ONLY | SWT.WRAP | SWT.FULL_SELECTION;

        final FormToolkit toolkit = managedForm.getToolkit();
        final Composite body = managedForm.getForm().getBody();

        Section section;
        GridLayout gl;
        GridData gd;

        gl = new GridLayout();
        gl.marginHeight = 0;
        gl.marginWidth = 0;
        body.setLayout(gl);

        // -------------------------------------------------------------------
        // general section
        // There is no description line for this section, so it is
        // necessary to eliminate that bit in the style flags that
        // are passed in. If the bit were not changed to 0, an
        // extra empty line would appear below the title.
        generalSection = FormHelper.createSectionComposite(body, "General", "", toolkit, sectionFlags & ~Section.DESCRIPTION,
                null); //getExpansionListener());
        sections.put(SEC_GENERAL, generalSection);
        gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        gd.verticalAlignment = SWT.TOP;
        generalSection.setLayoutData(gd);
        final GeneralSectionExpansionHoopJumper absurdListener = new GeneralSectionExpansionHoopJumper();
        generalSection.addExpansionListener(absurdListener);
        generalSection.setData(SECTION_EXPANSION_LISTENER, absurdListener);
        
        final Composite generalArea = (Composite) generalSection.getClient();
        gl = new GridLayout(1, false);
        gl.marginHeight = 0;
        gl.marginWidth = 0;
        gl.marginBottom = 6;
        generalArea.setLayout(gl);
        
        generalTopPane = new Composite(generalArea, SWT.NONE);
        gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        gd.verticalAlignment = SWT.TOP;
        generalTopPane.setLayoutData(gd);
        gl = new GridLayout(6, false);
        gl.marginHeight = 0;
        gl.marginWidth = 0;
        gl.horizontalSpacing = 12;
        generalTopPane.setLayout(gl);
        
        startLabel = new Label(generalTopPane, SWT.NONE);
        startLabel.setLayoutData(new GridData());
        startLabel.setFont(JFaceResources.getFontRegistry().getBold(JFaceResources.DIALOG_FONT));
        lastCheckpointLabel = new Label(generalTopPane, SWT.NONE);
        lastCheckpointLabel.setLayoutData(new GridData());
        finishLabel = new Label(generalTopPane, SWT.NONE);
        finishLabel.setLayoutData(new GridData());
        finishLabel.setFont(JFaceResources.getFontRegistry().getBold(JFaceResources.DIALOG_FONT));
        tlcSimulationLabel = new Label(generalTopPane, SWT.NONE);
        gd = new GridData();
        gd.horizontalAlignment = SWT.CENTER;
        tlcSimulationLabel.setLayoutData(gd);
        tlcSimulationLabel.setText("Simulation mode");
        tlcSimulationLabel.setVisible(false);
        tlcSimulationLabel.setFont(JFaceResources.getFontRegistry().getItalic(JFaceResources.DIALOG_FONT));
        tlcSearchModeLabel = new Label(generalTopPane, SWT.NONE);
        gd = new GridData();
        gd.horizontalAlignment = SWT.RIGHT;
        gd.grabExcessHorizontalSpace = true;
        tlcSearchModeLabel.setLayoutData(gd);
        tlcStatusLabel = new Label(generalTopPane, SWT.NONE);
        gd = new GridData();
        gd.horizontalAlignment = SWT.RIGHT;
        gd.grabExcessHorizontalSpace = true;
        gd.horizontalIndent = 18;
        tlcStatusLabel.setLayoutData(gd);
        tlcStatusLabel.setFont(JFaceResources.getFontRegistry().getBold(JFaceResources.DIALOG_FONT));
        
        generalErrorPane = new Composite(generalArea, SWT.NONE);
        gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        gd.verticalIndent = 9;
        gd.verticalAlignment = SWT.TOP;
        generalErrorPane.setLayoutData(gd);
        gl = new GridLayout(3, false);
        gl.marginHeight = 6;
        gl.marginWidth = 0;
        gl.horizontalSpacing = 6;
        generalErrorPane.setLayout(gl);
        generalErrorPane.setBackground(ERROR_PANE_BACKGROUND);

        // errors
        // Label createLabel =
        // toolkit.createLabel(statusComposite, "Errors detected:");
        // this.errorStatusHyperLink = toolkit.createHyperlink(statusComposite, "", SWT.RIGHT);
        errorStatusHyperLink = toolkit.createHyperlink(generalErrorPane, "", SWT.NONE);
        errorStatusHyperLink.setBackground(generalErrorPane.getBackground());
        errorStatusHyperLink.setVisible(false);
        
        // fingerprint collision probability
        fingerprintCollisionLabel = new Label(generalErrorPane, SWT.NONE);
        gd = new GridData();
        gd.horizontalAlignment = SWT.CENTER;
        fingerprintCollisionLabel.setLayoutData(gd);
        fingerprintCollisionLabel.setVisible(false);
                
		setErrorPaneVisible(false);

	
        // -------------------------------------------------------------------
        // statistics section
        // There is no description line for this section, so it is
        // necessary to eliminate that bit in the style flags that
        // are passed in. If the bit were not changed to 0, an
        // extra empty line would appear below the title.
        section = FormHelper.createSpaceGrabbingSectionComposite(body, "Statistics", "", toolkit,
        		(sectionFlags | Section.COMPACT) & ~Section.DESCRIPTION, getExpansionListener());
        sections.put(SEC_STATISTICS, section);
        gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.verticalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        gd.grabExcessVerticalSpace = true;
        section.setLayoutData(gd);
        
        final Composite statArea = (Composite) section.getClient();
        gl = new GridLayout(2, false);
        gl.marginHeight = 0;
        gl.marginWidth = 0;
        statArea.setLayout(gl);

        final int heightGuidance = getHeightGuidanceForLabelTextFieldLine(statArea, toolkit);
        
        // progress stats
        createAndSetupStateSpace(statArea, toolkit, heightGuidance);
        
        // coverage stats
        createAndSetupCoverage(statArea, toolkit, heightGuidance);

        
        // -------------------------------------------------------------------
        // Calculator section
		final IPreferenceStore ips = TLCUIActivator.getDefault().getPreferenceStore();
		final boolean eceInItsOwnTab = ips.getBoolean(IModelEditorPreferenceConstants.I_MODEL_EDITOR_SHOW_ECE_AS_TAB);

		calculatorSection = new Composite(body, SWT.NONE);
        gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.verticalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        gd.grabExcessVerticalSpace = !eceInItsOwnTab;
        calculatorSection.setLayoutData(gd);
        gl = new GridLayout();
        gl.marginHeight = 0;
        gl.marginWidth = 0;
        calculatorSection.setLayout(gl);
        calculatorSection.setBackground(calculatorSection.getDisplay().getSystemColor(SWT.COLOR_WHITE));
        
		if (!eceInItsOwnTab) {
			pageShouldDisplayEvaluateConstantUI(true);
		}
        
        // -------------------------------------------------------------------
        // output section
        section = FormHelper.createSpaceGrabbingSectionComposite(body, "User Output",
                "TLC output generated by evaluating Print and PrintT expressions.", toolkit, sectionFlags,
                getExpansionListener());
        sections.put(SEC_OUTPUT, section);
        gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.verticalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        gd.grabExcessVerticalSpace = true;
        section.setLayoutData(gd);
        final Composite outputArea = (Composite) section.getClient();
        outputArea.setLayout(new GridLayout(1, false));
        // output viewer -- see progressOutput comment complaints concerning SWT.WRAP included in the text field flags
        userOutput = FormHelper.createFormsOutputViewer(toolkit, outputArea, textFieldFlags);
		gd = new GridData();
		gd.horizontalAlignment = SWT.FILL;
		gd.verticalAlignment = SWT.FILL;
		gd.grabExcessHorizontalSpace = true;
		gd.grabExcessVerticalSpace = true;
		gd.minimumWidth = 360;
		gd.minimumHeight = 120;
		// while the rational person would say this width hint is pointless and gets ignored, the Eclipse architect
		//		would say "hey - no, we use this behind the scenes to influence word wrap on the text component, 
		//		of course"
		gd.widthHint = 400;
		userOutput.getTextWidget().setLayoutData(gd);
		userOutput.getTextWidget().setFont(JFaceResources.getFont(ITLCPreferenceConstants.I_TLC_OUTPUT_FONT));

        // -------------------------------------------------------------------
        // progress section
        // There is no description line for this section, so it is
        // necessary to eliminate that bit in the style flags that
        // are passed in. If the bit were not changed to 0, an
        // extra empty line would appear below the title.
        section = FormHelper.createSpaceGrabbingSectionComposite(body, "Progress Output", "  ", toolkit,
				(sectionFlags & ~Section.EXPANDED), getExpansionListener());
        sections.put(SEC_PROGRESS, section);
        gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.verticalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        // we don't want to set gd.grabExcessVerticalSpace = true; because we are initially collapsed
        section.setLayoutData(gd);
        final Composite progressArea = (Composite) section.getClient();
        progressArea.setLayout(new GridLayout(1, false));

        // I am regularly stunned by how crappy and quirky SWT is... in this case, if we don't have SWT.WRAP in the,
        //		flags mask, the below maxWidth is observed on expansion of the text area (which we really don't want)
        //		but if we turn on WRAP, then the text area expands to fill the entire width but observes width shrinking
        //		of its parent editor. If we instead use GridLayout (with or without WRAP), width shrinking is 
        //		completely ignored and the width of the text area is the longest line of text...
        progressOutput = FormHelper.createFormsOutputViewer(toolkit, progressArea, textFieldFlags);
		gd = new GridData();
		gd.horizontalAlignment = SWT.FILL;
		gd.verticalAlignment = SWT.FILL;
		gd.grabExcessHorizontalSpace = true;
		gd.grabExcessVerticalSpace = true;
		gd.minimumWidth = 360;
		gd.minimumHeight = 120;
		// while the rational person would say this width hint is pointless and gets ignored, the Eclipse architect
		//		would say "hey - no, we use this behind the scenes to influence word wrap on the text component, 
		//		of course"
		gd.widthHint = 400;
        progressOutput.getTextWidget().setLayoutData(gd);
        progressOutput.getTextWidget().setFont(JFaceResources.getFont(ITLCPreferenceConstants.I_TLC_OUTPUT_FONT));

        final Vector<Control> controls = new Vector<Control>();
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
			if (path == null) {
				// User cancelled the dialog
				return;
			}
			
			// I/O operations should never run inside the UI thread.
			final Job j = new WorkspaceJob("Loading output file...") {
				public IStatus runInWorkspace(final IProgressMonitor monitor) throws CoreException {
					try {
						// Import the file into the Toolbox on the file/resource layer.
						final TLCOutputSourceRegistry modelCheckSourceRegistry = TLCOutputSourceRegistry
								.getModelCheckSourceRegistry();
						modelCheckSourceRegistry
								.removeTLCStatusSource(new Model[] { getModel() });
						getModel().createModelOutputLogFile(new FileInputStream(new File(path)), monitor);
						
						// Once the output has been imported on the
						// file/resource layer, update the UI.
						final Job job = new UIJob("Updating results page with loaded output...") {
							public IStatus runInUIThread(IProgressMonitor monitor) {
								try {
									loadData();
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

		/* (non-Javadoc)
		 * @see org.eclipse.jface.action.Action#isEnabled()
		 */
		public boolean isEnabled() {
			if (getModel().isRunning()) {
				return false;
			}
			return super.isEnabled();
		}
	}

    /**
     * Save data back to model
     */
	public void commit(boolean onSave) {
    	if (expressionEvalInput != null) {
            final String expression = expressionEvalInput.getDocument().get();
            getModel().unsavedSetEvalExpression(expression);
    	}

        super.commit(onSave);
    }

    private void setStartTime(final long msTime) {
    	startTimestamp = msTime;
    	
    	if (msTime < 0) {
			// Leave the starttime text empty on a negative timestamp. A negative one indicates that the
			// model has never been checked
    		// See Long.MIN_VALUE in org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider.initialize()
    		startLabel.setText("Awaiting first run...");
		} else {
			startLabel.setText("Start: " + DATE_FORMATTER.format(new Date(msTime)));
		}
    	
    	generalTopPane.layout(true, true);
    }
    
    private void setEndTime(final long msTime) {
    	if (msTime < 0) {
    		finishLabel.setVisible(false);
		} else {
			finishLabel.setText("End: " + DATE_FORMATTER.format(new Date(msTime)));
    		finishLabel.setVisible(true);
		}
    	
    	generalTopPane.layout(true, true);
    }
    
    private void setCheckpoint(final long msTime) {
    	if (msTime < 0) {
        	lastCheckpointLabel.setVisible(false);
		} else {
        	lastCheckpointLabel.setText("Last checkpoint: " + DATE_FORMATTER.format(new Date(msTime)));
        	lastCheckpointLabel.setVisible(true);
		}
    	
    	generalTopPane.layout(true, true);
    }
    
    private void setSearchMode(final String mode) {
    	if (TLCModelLaunchDataProvider.DEPTH_FIRST_SEARCH.equals(mode)) {
    		tlcSearchModeLabel.setText(TLCModelLaunchDataProvider.DEPTH_FIRST_SEARCH);
    		tlcSearchModeLabel.setVisible(true);
    		tlcSimulationLabel.setVisible(false);
    	} else {
    		tlcSearchModeLabel.setVisible(false);
			tlcSimulationLabel.setVisible(TLCModelLaunchDataProvider.SIMULATION_MODE.equals(mode));
    	}
    	
    	generalTopPane.layout(true, true);
    }
    
    private void setErrorPaneVisible(final boolean visible) {
    	final GridData gd = (GridData)generalErrorPane.getLayoutData();
    	
    	gd.exclude = !visible;
    	generalErrorPane.setLayoutData(gd);
    	
    	generalErrorPane.setVisible(visible);
    }
    
    private int getHeightGuidanceForLabelTextFieldLine(final Composite parent, final FormToolkit toolkit) {
    	final Label l = toolkit.createLabel(parent, "Just Some Concerned Text you get");
    	final Text t = toolkit.createText(parent, "More time text 12345:67890", SWT.FLAT);
    	
    	final int height = Math.max(t.computeSize(SWT.DEFAULT, SWT.DEFAULT).y, l.computeSize(SWT.DEFAULT, SWT.DEFAULT).y);
    	
    	l.dispose();
    	t.dispose();
    	
    	return height;
    }
    
    /**
     * Creates the state space table (initializes the {@link stateSpace} variable)
     * 
     * TODO there's definite commonality between this and createAndSetupCoverage - abstract
     * 
     * @param parent
     * @param toolkit
     * @return the constructed composite
     */
    private Composite createAndSetupStateSpace(final Composite parent, final FormToolkit toolkit, final int headerHeight) {
        final Composite statespaceComposite = toolkit.createComposite(parent, SWT.WRAP);
        GridLayout gl = new GridLayout(1, false);
        gl.marginTop = 0;
        gl.marginBottom = 3;
        gl.marginWidth = 0;
        statespaceComposite.setLayout(gl);
        GridData gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.verticalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        gd.grabExcessVerticalSpace = true;
        gd.horizontalIndent = 0;
        gd.verticalIndent = 0;
        statespaceComposite.setLayoutData(gd);

        
        final Label title
        	= toolkit.createLabel(statespaceComposite, "State space progress (click column header for graph)");
        gd = new GridData();
        gd.heightHint = headerHeight + 2;
        gd.horizontalAlignment = SWT.BEGINNING;
        gd.horizontalIndent = 0;
        gd.verticalIndent = 6;
        title.setLayoutData(gd);
        
        final Composite tableComposite = new Composite(statespaceComposite, SWT.NONE);
        final TableColumnLayout tableColumnLayout = new TableColumnLayout();
        tableComposite.setLayout(tableColumnLayout);
		final Table stateTable
			= toolkit.createTable(tableComposite, (SWT.MULTI | SWT.FULL_SELECTION | SWT.V_SCROLL | SWT.BORDER));
		final StateSpaceLabelProvider sslp = new StateSpaceLabelProvider(this);
        gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.verticalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        gd.grabExcessVerticalSpace = true;
        gd.horizontalIndent = 0;
        gd.verticalIndent = 0;
        gd.minimumWidth = sslp.getMinimumTotalWidth();
        gd.minimumHeight = 100;
        tableComposite.setLayoutData(gd);

        stateTable.setHeaderVisible(true);
        stateTable.setLinesVisible(true);

        sslp.createTableColumns(stateTable, this, tableColumnLayout);
        
        // create the viewer
        stateSpace = new TableViewer(stateTable);

        // create list-based content provider
        stateSpace.setContentProvider(new IStructuredContentProvider() {
            public void inputChanged(Viewer viewer, Object oldInput, Object newInput) { }

            public void dispose() { }

            public Object[] getElements(Object inputElement) {
                if ((inputElement != null) && (inputElement instanceof List)) {
                    return ((List<?>) inputElement).toArray(new Object[((List<?>) inputElement).size()]);
                }
                return null;
            }
        });

        stateSpace.setLabelProvider(sslp);
        getSite().setSelectionProvider(stateSpace);
        
        return statespaceComposite;
    }

    /**
     * Creates the coverage table (initializes the {@link coverageTimestamp} and {@link coverage} variables)
     * 
     * TODO there's definite commonality between this and createAndSetupStateSpace - abstract
     * 
     * @param parent
     * @param toolkit
     * @return returns the containing composite
     */
    private Composite createAndSetupCoverage(final Composite parent, final FormToolkit toolkit, final int headerHeight) {
        final Composite coverageComposite = toolkit.createComposite(parent, SWT.WRAP);
        GridLayout gl = new GridLayout(1, false);
        gl.marginTop = 0;
        gl.marginBottom = 3;
        gl.marginWidth = 0;
        coverageComposite.setLayout(gl);
        GridData gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.verticalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        gd.grabExcessVerticalSpace = true;
        gd.horizontalIndent = 0;
        gd.verticalIndent = 0;
        coverageComposite.setLayoutData(gd);
        
        
        final Composite headerLine = toolkit.createComposite(coverageComposite, SWT.WRAP);
        gl = new GridLayout(2, false);
        gl.marginHeight = 0;
        gl.marginWidth = 0;
        headerLine.setLayout(gl);
        gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        gd.horizontalIndent = 0;
        gd.verticalIndent = 0;
        headerLine.setLayoutData(gd);
        
        final Label title = toolkit.createLabel(headerLine, "Sub-actions of next-state"); // "next-state" term used on MainModelPage too
        gd = new GridData();
        gd.horizontalIndent = 0;
        gd.verticalIndent = 6;
        gd.heightHint = headerHeight + 2;
        gd.horizontalAlignment = SWT.BEGINNING;
        gd.verticalAlignment = SWT.BOTTOM;
        title.setLayoutData(gd);

        this.coverageTimestampText = toolkit.createText(headerLine, "", SWT.FLAT);
        this.coverageTimestampText.setEditable(false);
        this.coverageTimestampText.setMessage("(No numbers recorded yet. Has profiling been enabled on TLC options?)");
        gd = new GridData();
        gd.horizontalIndent = 6;
        gd.verticalIndent = 0;
        gd.minimumWidth = 150;
        gd.grabExcessHorizontalSpace = true;
        gd.horizontalAlignment = SWT.FILL;
        this.coverageTimestampText.setLayoutData(gd);
        

        final Composite tableComposite = new Composite(coverageComposite, SWT.NONE);
        final TableColumnLayout tableColumnLayout = new TableColumnLayout();
        tableComposite.setLayout(tableColumnLayout);
        final Table coverageTable
        	= toolkit.createTable(tableComposite, SWT.MULTI | SWT.FULL_SELECTION | SWT.V_SCROLL | SWT.BORDER);
        final CoverageLabelProvider clp = new CoverageLabelProvider();
        gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.verticalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        gd.grabExcessVerticalSpace = true;
        gd.horizontalIndent = 0;
        gd.verticalIndent = 0;
        gd.minimumWidth = clp.getMinimumTotalWidth();
        gd.heightHint = 100;
        tableComposite.setLayoutData(gd);

        coverageTable.setHeaderVisible(true);
        coverageTable.setLinesVisible(true);
        coverageTable.setToolTipText(CoverageLabelProvider.TOOLTIP);

        clp.createTableColumns(coverageTable, tableColumnLayout);

        // create the viewer
        coverage = new TableViewer(coverageTable);

        coverage.getTable().addMouseListener(new RecordToSourceCoupler(coverage));

        // create list-based content provider
        coverage.setContentProvider(new IStructuredContentProvider() {
            public void inputChanged(Viewer viewer, Object oldInput, Object newInput) { }

            public void dispose() { }

            public Object[] getElements(Object inputElement) {
                if ((inputElement != null) && (inputElement instanceof List)) {
                    return ((List<?>) inputElement).toArray(new Object[((List<?>) inputElement).size()]);
                } else if (inputElement instanceof CoverageInformation) {
                	return ((CoverageInformation) inputElement).getSpecActions().toArray();
                }
                return null;
            }
        });

        coverage.setLabelProvider(clp);
        
        coverage.setComparator(new CoverageViewerComparator());
        for (TableColumn column : coverage.getTable().getColumns()) {
            column.addListener(SWT.Selection, e -> {
                final Item sortColumn = coverage.getTable().getSortColumn();
                int direction = coverage.getTable().getSortDirection();

                if (column.equals(sortColumn)) {
                    direction = direction == SWT.UP ? SWT.DOWN : SWT.UP;
                } else {
                	coverage.getTable().setSortColumn(column);
                    direction = SWT.UP;
                }
                coverage.getTable().setSortDirection(direction);
                coverage.refresh();
            });
        }
        
        getSite().setSelectionProvider(coverage);
        
        return coverageComposite;
    }

    long getStartTimestamp() {
    	return startTimestamp;
    }
    
    TableViewer getStateSpaceTableViewer() {
    	return stateSpace;
    }
    
    /**
     * Returns the StateSpaceInformationItem objects currently being displayed in 
     * the "State space progress" area, except in temporal order--that is, in the
     * opposite order from which they are displayed.
     * 
     * @return
     */
    @SuppressWarnings("unchecked")  // generics cast
	public StateSpaceInformationItem[] getStateSpaceInformation() {
		List<StateSpaceInformationItem> infoList = (List<StateSpaceInformationItem>) stateSpace.getInput();
        StateSpaceInformationItem[] result = new StateSpaceInformationItem[infoList.size()];
        for (int i = 0; i < result.length; i++)
        {
            result[i] = infoList.get(result.length - i - 1);
        }
        return result;

    }

    // this is only ever used to fetch ids SEC_GENERAL and SEC_STATISTICS
	public Set<Section> getSections(String ...sectionIDs) {
		final Set<String> set = new HashSet<String>(Arrays.asList(sectionIDs));
		return sections.entrySet().stream().filter(e -> set.contains(e.getKey())).map(Map.Entry::getValue)
				.collect(Collectors.toSet());
	}
	
	public EvaluateConstantExpressionPage.State getECEContent() {
		if (expressionEvalInput != null) {
			return new EvaluateConstantExpressionPage.State(expressionEvalInput.getDocument(),
					expressionEvalResult.getTextWidget().getText(), noBehaviorModeToggleButton.getSelection());
		}
		
		return null;
	}
	
	public void setECEContent(final EvaluateConstantExpressionPage.State state) {
		if (expressionEvalInput == null) {
			TLCUIActivator.getDefault().logError("Can't set ECE content on null objects.");
		} else {
			expressionEvalInput.setDocument(state.getInputDocument());
			expressionEvalResult.getTextWidget().setText(state.getOutputText());
			noBehaviorModeToggleButton.setSelection(state.getToggleState());
		}
	}
    
	public void setNoBehaviorSpecToggleState(final boolean selected) {
		if (noBehaviorModeToggleButton != null) {
			noBehaviorModeToggleButton.setSelection(selected);
		}
	}
	
	public void pageShouldDisplayEvaluateConstantUI(final boolean shouldShow) {
		final IManagedForm managedForm = getManagedForm();
		
		if (shouldShow) {
			final FormToolkit toolkit = managedForm.getToolkit();
	        final int sectionFlags = Section.TITLE_BAR | Section.TREE_NODE | Section.EXPANDED | SWT.WRAP;
	        final int textFieldFlags = SWT.MULTI | SWT.V_SCROLL | SWT.READ_ONLY | SWT.FULL_SELECTION | SWT.WRAP;
			final EvaluateConstantExpressionPage.BodyContentAssets assets = EvaluateConstantExpressionPage
					.createBodyContent(calculatorSection, toolkit, sectionFlags, textFieldFlags,
							getExpansionListener(), (ModelEditor)getEditor());
			final Section section = assets.getSection();
			
	        sections.put(SEC_EXPRESSION, section);

			expressionEvalInput = assets.getExpressionInput();
	        expressionEvalResult = assets.getExpressionOutput();
	        noBehaviorModeToggleButton = assets.getToggleButton();

	        validateableCalculatorSection = new ValidateableSectionPart(section, this, SEC_EXPRESSION);
	        // This ensures that when the part is made dirty, the model appears unsaved.
	        managedForm.addPart(validateableCalculatorSection);

	        // This makes the widget unsaved when text is entered.
	        expressionEvalInput.getTextWidget().addModifyListener(new DirtyMarkingListener(validateableCalculatorSection, false));

	        getDataBindingManager().bindAttribute(Model.MODEL_EXPRESSION_EVAL, expressionEvalInput, validateableCalculatorSection);
	        
	        section.addExpansionListener(new ExpansionAdapter() {
	            public void expansionStateChanged(final ExpansionEvent e) {
	            	if (e.getState()) {
	            		final GridData gd = new GridData();
	                    gd.horizontalAlignment = SWT.FILL;
	                    gd.verticalAlignment = SWT.FILL;
	                    gd.grabExcessHorizontalSpace = true;
	                    gd.grabExcessVerticalSpace = true;
	                    calculatorSection.setLayoutData(gd);
	            	} else {
	            		final GridData gd = (GridData)calculatorSection.getLayoutData();
	            		final Point size = section.computeSize(SWT.DEFAULT, SWT.DEFAULT);
	            		
	            		gd.grabExcessVerticalSpace = e.getState();
	            		gd.heightHint = size.y;

		            	calculatorSection.setLayoutData(gd);
	            	}
	            }
	        });
		} else if (validateableCalculatorSection != null) {
			sections.remove(SEC_EXPRESSION);
			
			managedForm.removePart(validateableCalculatorSection);
			
			validateableCalculatorSection = null;
			expressionEvalInput = null;
			expressionEvalResult = null;
			noBehaviorModeToggleButton = null;
			
			for (final Control control : calculatorSection.getChildren()) {
				control.dispose();
			}
			
			getDataBindingManager().unbindSectionFromPage(SEC_EXPRESSION, getId());
		}
		
		final GridData gd = (GridData)calculatorSection.getLayoutData();
		gd.grabExcessVerticalSpace = shouldShow;
		calculatorSection.setLayoutData(gd);
		
		getManagedForm().reflow(true);
	}

	@Override
	public void close() throws IOException {
		getModelEditor().resultsPageIsClosing();
		
		final DataBindingManager dm = getDataBindingManager();
		dm.unbindSectionAndAttribute(Model.MODEL_EXPRESSION_EVAL);
		dm.unbindSectionFromPage(SEC_EXPRESSION, getId());
	}

	
	private class GeneralSectionExpansionHoopJumper extends ExpansionAdapter implements Consumer<Boolean> {
        public void expansionStateChanged(final ExpansionEvent e) {
        	accept(Boolean.valueOf(e.getState()));
        }

        public void accept(final Boolean expand) {
        	if (expand.booleanValue()) {
        		final Composite c = (Composite)generalSection.getClient();
        		final GridData gd = (GridData)generalSection.getLayoutData();
        		
        		gd.heightHint = collapsedSectionHeight + c.computeSize(SWT.DEFAULT, SWT.DEFAULT).y;

                generalSection.setLayoutData(gd);
                generalSection.getParent().layout(true, true);
        	} else {
        		final GridData gd = new GridData();
                gd.horizontalAlignment = SWT.FILL;
                gd.grabExcessHorizontalSpace = true;
                gd.verticalAlignment = SWT.TOP;
                generalSection.setLayoutData(gd);
                
                collapsedSectionHeight = generalSection.computeSize(SWT.DEFAULT, SWT.DEFAULT).y;
        	}
        }
	}
	
	
	/**
	 * In an ideal world, we rely upon the associated SWT widgets being able to return a set value for visible and then
	 * 	just base our view state on those, except we experience load data in situations in which the "actual" visible
	 *  value does not match what has been set.
	 */
	static class ErrorPaneViewState {
		private final AtomicBoolean m_displayErrorLink;
		private final AtomicBoolean m_displayFingerprint;
		private final AtomicBoolean m_displayZeroCount;
		
		ErrorPaneViewState() {
			m_displayErrorLink = new AtomicBoolean(false);
			m_displayFingerprint = new AtomicBoolean(false);
			m_displayZeroCount = new AtomicBoolean(false);
		}
		
		void setErrorLinkDisplay(final boolean display) {
			m_displayErrorLink.set(display);
		}
		
		boolean errorLinkIsDisplayed() {
			return m_displayErrorLink.get();
		}
		
		void setFingerprintDisplay(final boolean display) {
			m_displayFingerprint.set(display);
		}
		
		boolean fingerprintIsDisplayed() {
			return m_displayFingerprint.get();
		}
		
		void clearState() {
			m_displayErrorLink.set(false);
			m_displayFingerprint.set(false);
			m_displayZeroCount.set(false);
		}
		
		boolean shouldDisplay() {
			return m_displayErrorLink.get() || m_displayFingerprint.get() || m_displayZeroCount.get();
		}
	}
}
