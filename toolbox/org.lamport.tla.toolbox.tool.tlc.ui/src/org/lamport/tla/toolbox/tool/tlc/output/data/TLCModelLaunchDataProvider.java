/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Simon Zambrovski - initial API and implementation
 ******************************************************************************/

package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.Hashtable;
import java.util.List;
import java.util.Vector;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.IDialogSettings;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.DocumentRewriteSession;
import org.eclipse.jface.text.DocumentRewriteSessionType;
import org.eclipse.jface.text.FindReplaceDocumentAdapter;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.output.ITLCOutputListener;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCError.Order;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCRegion;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCRegionContainer;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.st.Location;
import tlc2.model.Assignment;
import tlc2.model.Formula;
import tlc2.output.EC;
import tlc2.output.MP;
import util.TLAConstants;

/**
 * Container for the data about the model launch
 * @author Simon Zambrovski
 */
public class TLCModelLaunchDataProvider implements ITLCOutputListener
{
	public static final String STATESORTORDER = "STATESORTORDER";

    public static final String NO_OUTPUT_AVAILABLE = "No output is available";

    public static final String NO_ERRORS = "No errors";
    // strings for current status reporting
    public static final String NOT_RUNNING = "Not running";
    public static final String COMPUTING_INIT = "Computing initial states";
    public static final String RECOVERING = "Recovering from checkpoint";
    public static final String COMPUTING_REACHABLE = "Computing reachable states";
    public static final String CHECKPOINTING = "Checkpointing";
    public static final String CHECKING_LIVENESS_FINAL = "Checking final liveness";
    public static final String CHECKING_LIVENESS = "Checking liveness";
    public static final String SERVER_RUNNING = "Master waiting for workers";
    public static final String SINGLE_WORKER_REGISTERED = " worker registered";
    public static final String MULTIPLE_WORKERS_REGISTERED = " workers registered";
    // strings for the types of searches
    public static final String BREADTH_FIRST_SEARCH = "Breadth-first search";
    public static final String DEPTH_FIRST_SEARCH = "Depth-first search";
    // string for simulation mode
    public static final String SIMULATION_MODE = "Simulation";

    // pattern for the output of evaluating constant expressions
    public static final Pattern CONSTANT_EXPRESSION_OUTPUT_PATTERN = Pattern.compile("(?s)" + TLAConstants.BEGIN_TUPLE
            + "[\\s]*" + Pattern.quote(TLAConstants.CONSTANT_EXPRESSION_EVAL_IDENTIFIER) + "[\\s]*" + TLAConstants.COMMA
            + "(.*)"/*calc output group*/
            + TLAConstants.END_TUPLE);

    
    
    // presenters for the current process
    private final CopyOnWriteArrayList<ITLCModelLaunchDataPresenter> m_dataPresenters;
    // list of errors
    protected List<TLCError> errors;
    // start time
    protected long startTimestamp;
    // end time
    protected long finishTimestamp;
    // tlc mode (BFS|DFS|Simu)
    protected String tlcMode;
    // last checkpoint time
    protected long lastCheckpointTimeStamp;
    // coverage at
    protected String coverageTimestamp;
    // reports current status of model checking
    protected String currentStatus;
    // reports the probability of a fingerprint collision
    protected String fingerprintCollisionProbability;
    // coverage items
    protected CoverageInformation coverageInfo;
    // One of the coverage infos indicate zero coverage.
    protected boolean zeroCoverage = false;
    // progress information
    protected List<StateSpaceInformationItem> progressInformation;

    // last detected error
    protected TLCError lastDetectedError;
    // flag indicating that the job / file output is finished
    protected boolean isDone;
    // progress output
    protected Document progressOutput;
    // user output
    protected Document userOutput;
    // calc output
    protected String constantExprEvalOutput;
    // the model, which is represented by the current launch data provider
    private final Model model;
    // flag indicating that TLC has started
    // currently this is used to indicate
	// that tlc output not surrounded by message tags
	// should be put in the user output widget. This does not indicate the state of
	// the TLC process. Instead it only indicates that the TLC process is past
	// the spec parsing stage with SANY.
    protected boolean isTLCStarted = false;

    protected int numWorkers = 0;

	private int fpIndex;

	private boolean isSymmetryWithLiveness = false;
	private boolean isConstraintsWithLiveness = false;
	
	private final Object parsingLock;
	private final AtomicBoolean parsing;
	
	public TLCModelLaunchDataProvider(final Model tlcModel) {
    	Assert.isNotNull(tlcModel);
        model = tlcModel;
        
        m_dataPresenters = new CopyOnWriteArrayList<>();

        // init provider, but not connect it to the source!
        initialize();

        parsingLock = new Object();
        parsing = new AtomicBoolean(true);

		synchronized (parsingLock) {
			/*
			 * interested in the output for the model
			 */
			parsing.set(connectToSourceRegistry());
        }
    }
	
	public void waitForParsingFinish() {
		if (parsing.get()) {
			synchronized (parsingLock) {
				try {
					parsingLock.wait();
				} catch (final Exception e) { }
			}
		}
	}

    /**
     * Resets the values to defaults
     */
    protected void initialize()
    {
        isDone = false;
        isTLCStarted = false;
        errors = new Vector<TLCError>();
        lastDetectedError = null;
        model.removeMarkers(ModelHelper.TLC_MODEL_ERROR_MARKER_TLC);

        coverageInfo = new CoverageInformation();
        progressInformation = new Vector<StateSpaceInformationItem>();
        startTimestamp = Long.MIN_VALUE;
        finishTimestamp = Long.MIN_VALUE;
        tlcMode = "";
        lastCheckpointTimeStamp = Long.MIN_VALUE;
        coverageTimestamp = "";
        setCurrentStatus(NOT_RUNNING);
        setFingerprintCollisionProbability("");
        progressOutput = new Document(NO_OUTPUT_AVAILABLE);
        userOutput = new Document(NO_OUTPUT_AVAILABLE);
        constantExprEvalOutput = "";
        isSymmetryWithLiveness = false;
        zeroCoverage = false;
    }

    /**
     * Inform the view, if any
     * @param fieldId
     */
	protected void informPresenter(final int fieldId) {
    	m_dataPresenters.stream().forEach((presenter) -> {
            presenter.modelChanged(this, fieldId);
    	});
    }

    /**
     * Populate data to the presenter 
     */
	public void populate() {
		for (int i = 0; i < ITLCModelLaunchDataPresenter.ALL_FIELDS.length; i++) {
			informPresenter(ITLCModelLaunchDataPresenter.ALL_FIELDS[i]);
		}
	}

    /**
     * Name of the model
     */
    public Model getModel()
    {
        return model;
    }

	public void onDone() {
        /*
         * If the last message output by TLC
         * was an error, then this error will not
         * be added to errors by the method onOutput. The method
         * onOutput assumes that there will be at least one
         * message that is not an error at the end of the output
         * of TLC. This is not always the case. An error such as
         * "The system cannot find the file specified" will be the last
         * error output by TLC. Therefore, such a message
         * must be added here so that it gets shown
         * to the user. If lastDetectedError is not null
         * then it points to an error that has not been added
         * to the list errors. It must be added to this list to
         * be shown to the user.
         */
		if (lastDetectedError != null) {
			this.errors.add(lastDetectedError);
			informPresenter(ITLCModelLaunchDataPresenter.ERRORS);
		}

        // TLC is no longer running
        this.setCurrentStatus(NOT_RUNNING);
        informPresenter(ITLCModelLaunchDataPresenter.CURRENT_STATUS);
        isDone = true;
        if (zeroCoverage) {
        	// the logic for whatever reason in ResultPage doesn't display zero coverage information unless 
        	//		the data provider is done.
            informPresenter(ITLCModelLaunchDataPresenter.COVERAGE);
        }
        
        synchronized (parsingLock) {
        	try {
        		parsingLock.notifyAll();
        	} catch (final Exception e) { }
        	finally {
        		parsing.set(false);
        	}
        }
    }

    public void onNewSource()
    {
        // everything that was saved should be erased
        initialize();
        populate();
    }

	public void onOutput(final ITypedRegion region, final String text) {
        // restarting
        if (isDone)
        {
            isTLCStarted = false;
            isDone = false;
        }

        String outputMessage = text;
        if (region instanceof TLCRegion)
        {
            TLCRegion tlcRegion = (TLCRegion) region;
            int severity = tlcRegion.getSeverity();
            int messageCode = tlcRegion.getMessageCode();

            switch (severity) {
            case MP.STATE:
                Assert.isNotNull(this.lastDetectedError,
                        "The state encountered without the error describing the reason for it. This is a bug.");
                this.lastDetectedError.addState(TLCState.parseState(outputMessage, getModelName()));
                break;
            case MP.ERROR:
            case MP.TLCBUG:
            case MP.WARNING:

                switch (messageCode) {
                // errors to skip
                case EC.TLC_BEHAVIOR_UP_TO_THIS_POINT:
                case EC.TLC_COUNTER_EXAMPLE:
                    break;
                    
                // send to progress output
                case EC.TLC_FEATURE_UNSUPPORTED:
                    setDocumentText(this.progressOutput, outputMessage, true);
                    break;
                case EC.TLC_FEATURE_UNSUPPORTED_LIVENESS_SYMMETRY:
                	this.isSymmetryWithLiveness = true;
                    setDocumentText(this.progressOutput, outputMessage, true);
                    informPresenter(ITLCModelLaunchDataPresenter.WARNINGS);
                    break;
                case EC.TLC_FEATURE_LIVENESS_CONSTRAINTS:
                	this.isConstraintsWithLiveness = true;
                    setDocumentText(this.progressOutput, outputMessage, true);
                    informPresenter(ITLCModelLaunchDataPresenter.WARNINGS);
                    break;
                    
                // usual errors
                default:
                    if (this.lastDetectedError != null)
                    {
                        // something is detected which is not an error
                        // and the error trace is not empty
                        // add the trace to the error list
                        this.errors.add(lastDetectedError);

                        informPresenter(ITLCModelLaunchDataPresenter.ERRORS);
                        this.lastDetectedError = null;
                    }
                    // create an error
                    this.lastDetectedError = createError(tlcRegion, text);
                    break;
                }
                break;
            case MP.NONE:

                if (lastDetectedError != null)
                {
                    // something is detected which is not an error
                    // and the error trace is not empty
                    // add the trace to the error list
                    this.errors.add(lastDetectedError);

                    informPresenter(ITLCModelLaunchDataPresenter.ERRORS);
                    this.lastDetectedError = null;
                }

				// Order of case statements matters. There are no "break" statements because - by default - it should go to the document. 
                switch (messageCode) {
                // Progress information
                case EC.TLC_VERSION:
                case EC.TLC_SANY_START:
                case EC.TLC_SANY_END:
                    // case EC.TLC_SUCCESS:
                case EC.TLC_PROGRESS_START_STATS_DFID:
                case EC.TLC_INITIAL_STATE:
                case EC.TLC_COMPUTING_INIT_PROGRESS:
                case EC.TLC_STATS:
                case EC.TLC_STATS_DFID:
                case EC.TLC_STATS_SIMU:
                case EC.TLC_SEARCH_DEPTH:
                case EC.TLC_STATE_GRAPH_OUTDEGREE:
                case EC.TLC_LIVE_IMPLIED:
                case EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_LOADED:
                    setDocumentText(this.progressOutput, outputMessage, true);
                    break;
                case EC.TLC_MODE_MC:
                    this.tlcMode = BREADTH_FIRST_SEARCH;
					this.fpIndex = getFPIndex(outputMessage);
                    informPresenter(ITLCModelLaunchDataPresenter.TLC_MODE);
                    setDocumentText(this.progressOutput, outputMessage, true);
                    break;
                case EC.TLC_MODE_MC_DFS:
                    this.tlcMode = DEPTH_FIRST_SEARCH;
					this.fpIndex = getFPIndex(outputMessage);
                    informPresenter(ITLCModelLaunchDataPresenter.TLC_MODE);
                    setDocumentText(this.progressOutput, outputMessage, true);
                    break;
                case EC.TLC_MODE_SIMU:
                    this.tlcMode = SIMULATION_MODE;
                    informPresenter(ITLCModelLaunchDataPresenter.TLC_MODE);
                    setDocumentText(this.progressOutput, outputMessage, true);
                    break;
                case EC.TLC_SUCCESS:
                    this.setFingerprintCollisionProbability(extractCollisionProbability(outputMessage));
                    informPresenter(ITLCModelLaunchDataPresenter.FINGERPRINT_COLLISION_PROBABILITY);
                    break;
                case EC.TLC_COMPUTING_INIT:
                    this.setCurrentStatus(COMPUTING_INIT);
                    informPresenter(ITLCModelLaunchDataPresenter.CURRENT_STATUS);
                    setDocumentText(this.progressOutput, outputMessage, true);
                    break;
                case EC.TLC_INIT_GENERATED1:
                case EC.TLC_INIT_GENERATED2:
					if (addOrReplaceProgressInformation(StateSpaceInformationItem.parseInit(outputMessage))) {
						informPresenter(ITLCModelLaunchDataPresenter.PROGRESS);
					}
                case EC.TLC_INIT_GENERATED3:
                case EC.TLC_INIT_GENERATED4:
                    this.setCurrentStatus(COMPUTING_REACHABLE);
                    informPresenter(ITLCModelLaunchDataPresenter.CURRENT_STATUS);
                    setDocumentText(this.progressOutput, outputMessage, true);
                    break;
                case EC.TLC_CHECKPOINT_START:
                    this.setCurrentStatus(CHECKPOINTING);
                    informPresenter(ITLCModelLaunchDataPresenter.CURRENT_STATUS);
                    setDocumentText(this.progressOutput, outputMessage, true);
                    break;
                case EC.TLC_CHECKPOINT_END:
                    this.setCurrentStatus(COMPUTING_REACHABLE);
                    informPresenter(ITLCModelLaunchDataPresenter.CURRENT_STATUS);
                    this.lastCheckpointTimeStamp = GeneralOutputParsingHelper.parseTLCTimestamp(outputMessage);
                    informPresenter(ITLCModelLaunchDataPresenter.LAST_CHECKPOINT_TIME);
                    setDocumentText(this.progressOutput, outputMessage, true);
                    break;
                case EC.TLC_CHECKING_TEMPORAL_PROPS:
                    if (outputMessage.contains("complete")) {
                    	this.setCurrentStatus(CHECKING_LIVENESS_FINAL);
                    } else {
                    	this.setCurrentStatus(CHECKING_LIVENESS);
                    }
                    informPresenter(ITLCModelLaunchDataPresenter.CURRENT_STATUS);
                    setDocumentText(this.progressOutput, outputMessage, true);
                    break;
                case EC.TLC_CHECKING_TEMPORAL_PROPS_END:
					this.setCurrentStatus(COMPUTING_REACHABLE);
					informPresenter(ITLCModelLaunchDataPresenter.CURRENT_STATUS);
                    setDocumentText(this.progressOutput, outputMessage, true);
                    break;
                case EC.TLC_CHECKPOINT_RECOVER_START:
                    this.setCurrentStatus(RECOVERING);
                    informPresenter(ITLCModelLaunchDataPresenter.CURRENT_STATUS);
                    setDocumentText(this.progressOutput, outputMessage, true);
                    break;
                case EC.TLC_CHECKPOINT_RECOVER_END:
                case EC.TLC_CHECKPOINT_RECOVER_END_DFID:
                    this.setCurrentStatus(COMPUTING_REACHABLE);
                    informPresenter(ITLCModelLaunchDataPresenter.CURRENT_STATUS);
                    setDocumentText(this.progressOutput, outputMessage, true);
                    break;
                case EC.TLC_STARTING:
                    isTLCStarted = true;
                    this.startTimestamp = GeneralOutputParsingHelper.parseTLCTimestamp(outputMessage);

                    informPresenter(ITLCModelLaunchDataPresenter.START_TIME);
                    break;
                case EC.TLC_FINISHED:
                    this.setCurrentStatus(NOT_RUNNING);
                    informPresenter(ITLCModelLaunchDataPresenter.CURRENT_STATUS);
                    this.finishTimestamp = GeneralOutputParsingHelper.parseTLCTimestamp(outputMessage);
                    informPresenter(ITLCModelLaunchDataPresenter.END_TIME);
                    break;
                case EC.TLC_PROGRESS_STATS_DFID:
                case EC.TLC_PROGRESS_SIMU:
                case EC.TLC_PROGRESS_STATS:
                    if (addOrReplaceProgressInformation(StateSpaceInformationItem.parse(outputMessage))) {
                    	informPresenter(ITLCModelLaunchDataPresenter.PROGRESS);
                    }
                    break;
                // Coverage information
                case EC.TLC_COVERAGE_START:
                    this.coverageTimestamp = CoverageInformationItem.parseCoverageTimestamp(outputMessage);
                    this.coverageInfo = new CoverageInformation(model.getSavedTLAFiles());
                    informPresenter(ITLCModelLaunchDataPresenter.COVERAGE_TIME);
                    informPresenter(ITLCModelLaunchDataPresenter.COVERAGE);
                    break;
                case EC.TLC_COVERAGE_PROPERTY:
                    this.coverageInfo.add(ActionInformationItem.parseProp(outputMessage, getModelName()));
                    informPresenter(ITLCModelLaunchDataPresenter.COVERAGE);
                    break;
                case EC.TLC_COVERAGE_INIT:
                    this.coverageInfo.add(ActionInformationItem.parseInit(outputMessage, getModelName()));
                    informPresenter(ITLCModelLaunchDataPresenter.COVERAGE);
                    break;
                case EC.TLC_COVERAGE_NEXT:
                    this.coverageInfo.add(ActionInformationItem.parseNext(outputMessage, getModelName()));
                    informPresenter(ITLCModelLaunchDataPresenter.COVERAGE);
                    break;
                case EC.TLC_COVERAGE_VALUE_COST:
                    CoverageInformationItem item = CoverageInformationItem.parseCost(outputMessage, getModelName());
                    this.coverageInfo.add(item);
                    if (item.getCount() == 0) {
                    	zeroCoverage = true;
                    }
                    informPresenter(ITLCModelLaunchDataPresenter.COVERAGE);
                    break;
                case EC.TLC_COVERAGE_VALUE:
                	item = CoverageInformationItem.parse(outputMessage, getModelName());
                    this.coverageInfo.add(item);
                    if (item.getCount() == 0) {
                    	zeroCoverage = true;
                    }
                    informPresenter(ITLCModelLaunchDataPresenter.COVERAGE);
                    break;
                case EC.TLC_COVERAGE_END_OVERHEAD:
                	if (getModel().isRunning()) {
                		informPresenter(ITLCModelLaunchDataPresenter.COVERAGE_END_OVERHEAD);
                		break;
                	}
                case EC.TLC_COVERAGE_END:
                    informPresenter(ITLCModelLaunchDataPresenter.COVERAGE_END);
                    break;
                case EC.TLC_DISTRIBUTED_SERVER_RUNNING:
                	numWorkers = 0;
                	this.setCurrentStatus(SERVER_RUNNING);
                    informPresenter(ITLCModelLaunchDataPresenter.CURRENT_STATUS);
                    setDocumentText(this.progressOutput, outputMessage, true);
                    break;
                case EC.TLC_DISTRIBUTED_WORKER_REGISTERED:
                	if (++numWorkers <= 1) {
                		this.setCurrentStatus(numWorkers + SINGLE_WORKER_REGISTERED);
                	} else {
                		this.setCurrentStatus(numWorkers + MULTIPLE_WORKERS_REGISTERED);
                	}
                    informPresenter(ITLCModelLaunchDataPresenter.CURRENT_STATUS);
                    setDocumentText(this.progressOutput, outputMessage, true);
                    break;
                case EC.TLC_DISTRIBUTED_WORKER_DEREGISTERED:
                	if (--numWorkers <= 1) {
                		this.setCurrentStatus(numWorkers + SINGLE_WORKER_REGISTERED);
                	} else {
                		this.setCurrentStatus(numWorkers + MULTIPLE_WORKERS_REGISTERED);
                	}
                    informPresenter(ITLCModelLaunchDataPresenter.CURRENT_STATUS);
                    setDocumentText(this.progressOutput, outputMessage, true);
                    break;
                // send the following errors to the process output log    
                case EC.TLC_DISTRIBUTED_EXCEED_BLOCKSIZE:
                case EC.TLC_DISTRIBUTED_WORKER_LOST:
                    setDocumentText(this.progressOutput, outputMessage, true);
                    break;
                default:
                    setDocumentText(this.userOutput, outputMessage, true);
                    informPresenter(ITLCModelLaunchDataPresenter.USER_OUTPUT);
                    break;
                }
                break;
            default:
                throw new IllegalArgumentException("This is a bug, the TLCToken with unexpected severity detected: "
                        + severity);
            }

        } else
        {
            if (isTLCStarted)
            {
                // SANY output is finished
                // remaining output from TLC without message
                // tags can be put in the user output widget
                // or in the calculator output widget

                // The following code searches for the
                // output generated by the calculator.
                // If found, it removes this output from the string
                // that will be put in user output, and puts
                // it in the calc output.
                Matcher constExprEvalOutputMatcher = CONSTANT_EXPRESSION_OUTPUT_PATTERN.matcher(outputMessage);
                if (constExprEvalOutputMatcher.find())
                {
                    // There is only one group in the pattern.
                    // It contains the constant expression value
                    String constExprEvalOutput = outputMessage.substring(constExprEvalOutputMatcher.start(1),
                            constExprEvalOutputMatcher.end(1));
                    // Sometimes TLC prints a space before or after
                    // the value, so we remove this.
                    this.constantExprEvalOutput = constExprEvalOutput.trim();
                    informPresenter(ITLCModelLaunchDataPresenter.CONST_EXPR_EVAL_OUTPUT);
                    /*
                     * Remove the result of constant expression evaluation plus
                     * the new line and return characters from the string to be placed
                     * in user output.
                     * 
                     * If the new line and return characters are not removed, there will
                     * be a blank line in the user output field where the constant expression value
                     * would have appeared
                     */
                    outputMessage = outputMessage.replaceFirst(CONSTANT_EXPRESSION_OUTPUT_PATTERN.toString() + "\r\n",
                            "");
                }
                if (outputMessage.length() != 0)
                {
                    setDocumentText(this.userOutput, outputMessage, true);
                    informPresenter(ITLCModelLaunchDataPresenter.USER_OUTPUT);
                }
                // TLCUIActivator.getDefault().logDebug("Unknown type detected: " + region.getType() + " message " + outputMessage);
            } else
            {
                // SANY output
                // should be put in progress output widget
                setDocumentText(this.progressOutput, outputMessage, true);
                informPresenter(ITLCModelLaunchDataPresenter.PROGRESS_OUTPUT);
            }
        }
    }

	static int getFPIndex(final String startupMessage) {
		final Matcher matcher = startupMessagePattern.matcher(startupMessage);
		if (matcher.find()) {
			return Integer.parseInt(matcher.group(2));
		}
		return 0; // legacy support
	}

    /**
     * @param latest
     * @return true iff the presenter should be updated
     */
    private boolean addOrReplaceProgressInformation(final StateSpaceInformationItem latest) {
    	if (!this.progressInformation.isEmpty()) {
    		final StateSpaceInformationItem head = this.progressInformation.get(0);
    		if (head.equals(latest)) {
    			this.progressInformation.set(0, latest);
    			return false;
    		} else {
    			this.progressInformation.add(0, latest);
    			if (this.progressInformation.size() > 1) {
    				// Set the predecessor to not be the most recent
    				// progress information.
    				this.progressInformation.get(1).setMostRecent(false);
    			}
    			return true;
    		}
    	} else {
    		this.progressInformation.add(latest);
    		return true;
    	}
	}

	/**
     * Destroy and disconnect
     */
    public void destroy()
    {
        TLCOutputSourceRegistry.getModelCheckSourceRegistry().disconnect(this);
    }

    /**
     * Creates an error object
     * <br>This is a factory method
     * 
     * @param tlcRegion a region marking the error information in the document
     * @param message the message represented by the region
     * @return the TLC Error representing the error
     */
    protected TLCError createError(TLCRegion tlcRegion, String message)
    {
        // the root of the error trace
		final IDialogSettings dialogSettings = Activator.getDefault().getDialogSettings();
        final boolean stateSortOrder = dialogSettings.getBoolean(STATESORTORDER);
		final TLCError topError = new TLCError(Order.valueOf(stateSortOrder));

        if (tlcRegion instanceof TLCRegionContainer)
        {
            TLCRegionContainer container = (TLCRegionContainer) tlcRegion;
            // read out the subordinated regions
            ITypedRegion[] regions = container.getSubRegions();

            // currently, there can be at most three regions
            Assert.isTrue(regions.length < 3, "Unexpected error region structure, this is a bug.");

            // iterate over regions
            for (int i = 0; i < regions.length; i++)
            {
                // the region itself is a TLC region, detect the child error
                if (regions[i] instanceof TLCRegion)
                {
                    TLCError cause = createError((TLCRegion) regions[i], message);
                    topError.setCause(cause);
                } else
                {
                    // read the error from message
                    String errorMessage;

                    /*
                     * Retrieve the MC file and create a document provider. This document
                     * provider will be used to connect to the file editor input for
                     * the MC file so that a Document representation of the file can
                     * be created in the following try block. We disconnect the document
                     * provider in the finally block for this try block in order to avoid
                     * a memory leak.
                     */
                    IFile mcFile = getModel().getTLAFile();
                    FileEditorInput mcFileEditorInput = new FileEditorInput(mcFile);
                    FileDocumentProvider mcFileDocumentProvider = new FileDocumentProvider();

                    try
                    {
                        // this is the error text
                        errorMessage = message;// tlcOutputDocument.get(tlcRegion.getOffset(), tlcRegion.getLength());

                        // create the error document
                        Document errorDocument = new Document();
                        errorDocument.set(errorMessage);

                        boolean markerInstalled = false;

                        // Connect to the file editor input
                        // so that a document can be created.
                        mcFileDocumentProvider.connect(mcFileEditorInput);

                        // the document connected to the MC file
                        IDocument mcDocument = mcFileDocumentProvider.getDocument(mcFileEditorInput);
                        // the search adapter on the MC file
                        FindReplaceDocumentAdapter mcSearcher = new FindReplaceDocumentAdapter(mcDocument);

                        // find the ids generated from the ModelWriter (in MC.tla file) in the error message
                        IRegion[] ids = ModelHelper.findIds(errorMessage);

                        // generate property object for every id
                        // initialize the variable here, which will hold the properties
                        @SuppressWarnings("unchecked")
						Hashtable<String, Object>[] props = new Hashtable[ids.length];

                        // search in the MC file for the ids
                        for (int j = 0; j < ids.length; j++)
                        {
                            // isolate id's from the TLC output
                            String id = errorDocument.get(ids[j].getOffset(), ids[j].getLength());
                            // retrieve coordinates of the id in the MC file
                            int[] coordinates = ModelHelper.calculateCoordinates(mcDocument, mcSearcher, id);
                            // report the error case
                            if (ModelHelper.EMPTY_LOCATION.equals(coordinates))
                            {
                                throw new CoreException(new Status(IStatus.ERROR, TLCUIActivator.PLUGIN_ID,
                                        "Provided id " + id + " not found in the model file."));
                            }
                            // create the error properties for this id
                            // this method find the corresponding attribute and
                            // create the map with attributes, required to create a marker
                            props[j] = ModelHelper.createMarkerDescription(mcFile, mcDocument, mcSearcher,
                                    errorMessage, IMarker.SEVERITY_ERROR, coordinates);

                            // read the attribute name
                            String attributeName = (String) props[j]
                                    .get(ModelHelper.TLC_MODEL_ERROR_MARKER_ATTRIBUTE_NAME);

                            // read the attribute index
                            Integer attributeIndex = (Integer) props[j]
                                    .get(ModelHelper.TLC_MODEL_ERROR_MARKER_ATTRIBUTE_IDX);

                            if (attributeName != null)
                            {
                                String idReplacement = null;
                                // some attributes are lists
                                if (ModelHelper.isListAttribute(attributeName))
                                {
									final List<String> attributeValue = (List<String>) model
											.getAttribute(attributeName, new ArrayList<String>(0));
                                    int attributeNumber = (attributeIndex != null) ? attributeIndex.intValue() : 0;

                                    if (IModelConfigurationConstants.MODEL_PARAMETER_CONSTANTS.equals(attributeName))
                                    {
                                    	// MK 07/25/2017: Correctly show error when constant is assigned a non-constant.
                                        final List<Assignment> valueList = ModelHelper.deserializeAssignmentList(attributeValue);
                                        if (valueList.size() >= (attributeNumber + 1)) {
	                                        final Assignment assignment = valueList.get(attributeNumber);
	                                        idReplacement = assignment.getRight();
                                        } else {
                                        	idReplacement = "'LL claims this should not happen. See Bug in TLCModelLaunchDataProvider.'";
                                        }
                                    } else
                                    {
                                        // invariants and properties
                                        final List<Formula> valueList = Formula.deserializeFormulaList(attributeValue);
                                        
                                        // @see bug #98 (if root cause has been fixed, remove if/else)
                                        if (valueList.size() >= (attributeNumber + 1)) {
                                        	Formula value = valueList.get(attributeNumber);
                                        	idReplacement = value.getFormula();
                                        } else {
                                            idReplacement = "'No value in valueList " + attributeValue + " for " + attributeNumber
													+ ". Bug in TLCModelLaunchDataProvider.'";
                                        }
                                    }
                                } else
                                {
                                    // others are just strings
                                    idReplacement = model.getAttribute(attributeName, ModelHelper.EMPTY_STRING);
                                }
                                // patch the message

                                errorMessage = errorMessage.substring(0, errorMessage.indexOf(id)) + idReplacement
                                        + errorMessage.substring(errorMessage.indexOf(id) + id.length());
                                // errorMessage = errorMessage.replaceAll(id, idReplacement);
                            } else
                            {
                                throw new CoreException(
                                        new Status(
                                                IStatus.ERROR,
                                                TLCUIActivator.PLUGIN_ID,
                                                "Provided id "
                                                        + id
                                                        + " maps to an attribute that was not found in the model. This is a bug."));
                            }
                        }
                        // find the locations inside the text
                        IRegion[] locations = ModelHelper.findLocations(errorMessage);
                        // the content on given location, or null, if location not in MC file
                        String[] regionContent = new String[locations.length];

                        // iterate over locations
                        for (int j = 0; j < locations.length; j++)
                        {
                            // restore the location from the region
                        	String locationString = "";
                        	try {
								locationString = errorDocument.get(locations[j].getOffset(), locations[j]
                        				.getLength());
							} catch (BadLocationException ble) {
								// Do not break from the loop when the spaghetti code above crashes for a
								// whatever reason (life is too short). The region (locations!?) might point to
								// another file which cannot be mapped to errorDocument which will throw the BLE.
								continue;
							}
                            Location location = Location.parseLocation(locationString);
                            // look only for location in the MC file
							if (location.source().equals(mcFile.getName().substring(0,
									mcFile.getName().length() - TLAConstants.Files.TLA_EXTENSION.length()))) {
                                IRegion region = AdapterFactory.locationToRegion(mcDocument, location);
                                regionContent[j] = mcDocument.get(region.getOffset(), region.getLength());
                                // replace the location statement in the error message
                                // with the string in the MC file to which it points
                                if (locationString != null && regionContent[j] != null)
                                {
                                    errorMessage = errorMessage.replace(locationString, regionContent[j]);
                                }
                            }
                        }

                        /* ----------------------------------------------------
                         * At this point the error message string does not contain any generated ids and
                         * locations. Set it as a message inside of all marker property maps  
                         */
                        
                        /*
                         * Hack to fix bug added by LL on 19 July 2013.
                         * If the string errorMessage is too long, the call of ModelHelper.installModelProblemMarker
                         * produces an exception deep inside the Eclipse methods that are called, which results
                         * in no error being reported by the Toolbox.  (Experimentation suggests that "too long" is 
                         * more than 64K characters.)  The following code was therefore added to shorten the message.  
                         * (A very long error message is of dubious value.)  Since the stuff at the end of the
                         * message is likely to be more interesting than the stuff in the middle, characters in
                         * the middle are removed.
                         */
                        int msgLen = errorMessage.length() ;
                        if (msgLen > 50000) {  	
                        	errorMessage = errorMessage.substring(0, 30000) + "  ...stuff deleted here...  " 
                        			          + errorMessage.substring(msgLen - 20000, msgLen);
                        }
                        
                        for (int j = 0; j < props.length; j++)
                        {
                            // patch the error marker
                            props[j].put(IMarker.MESSAGE, errorMessage);
                            // install error marker
                            model.setMarker(props[j], ModelHelper.TLC_MODEL_ERROR_MARKER_TLC);
                            markerInstalled = true;
                        }

                        // there were no ids and no locations
                        // the error is just a generic error in the model
                        if (!markerInstalled)
                        {
                            Hashtable<String, Object> prop = ModelHelper.createMarkerDescription(errorMessage, IMarker.SEVERITY_ERROR);
                            model.setMarker(prop, ModelHelper.TLC_MODEL_ERROR_MARKER_TLC);
                        }

                        // set error text
                        topError.setMessage(errorMessage);
                        // set error code
                        topError.setErrorCode(tlcRegion.getMessageCode());

                    } catch (BadLocationException e)
                    {
                        TLCUIActivator.getDefault().logError("Error parsing the error message", e);
                    } catch (CoreException e)
                    {
                        TLCUIActivator.getDefault().logError("Error parsing the error message", e);
                    } finally
                    {
                        /*
                         * The document provider is not needed. Always disconnect it to avoid a memory leak.
                         * 
                         * Keeping it connected only seems to provide synchronization of
                         * the document with file changes. That is not necessary in this context.
                         */
                        mcFileDocumentProvider.disconnect(mcFileEditorInput);
                    }

                }
            }
        }

        return topError;
    }

    private static final String CR = "\n";
    private static final String EMPTY = "";

	private static final Pattern startupMessagePattern = Pattern
			.compile("^Running (depth|breadth)-first search Model-Checking with fp ([0-9]+) and seed "
					+ "[-0-9]+ with [0-9]+ worker[s]? on [0-9]+ cores with .*? heap and .*? offheap memory (\\[pid: [0-9]+\\])? \\(.*\\).$");

    /**
     * Sets text to a document
     * @param document
     * @param message
     * @param append
     * @throws BadLocationException
     * Has to be run from non-UI thread
     */
	public static synchronized void setDocumentText(final Document document, final String message,
			final boolean append) {

		UIHelper.runUIAsync(new Runnable() {
			public void run() {
				try {
					DocumentRewriteSession rewriteSession;
					if (append && !isDefaultLabel(document)) {
						rewriteSession = document.startRewriteSession(DocumentRewriteSessionType.SEQUENTIAL);
						// append to existing document (0 length is valid and means message is going to be appended)
						document.replace(document.getLength(), 0, message + ((message.endsWith(CR)) ? EMPTY : CR));
					} else {
						rewriteSession = document.startRewriteSession(DocumentRewriteSessionType.STRICTLY_SEQUENTIAL);
						// replace of complete document
						document.replace(0, document.getLength(), message + ((message.endsWith(CR)) ? EMPTY : CR));
					}
					document.stopRewriteSession(rewriteSession);
				} catch (BadLocationException ignored) {
				}
			}
		});
	}
	
	/**
	 * @param document
	 * @return true iff the current content of the document is
	 *         {@link TLCModelLaunchDataProvider#NO_OUTPUT_AVAILABLE}
	 * @throws BadLocationException
	 */
	private static boolean isDefaultLabel(final IDocument document) throws BadLocationException {
		return document.getLength() == NO_OUTPUT_AVAILABLE.length()
				&& document.get(0, NO_OUTPUT_AVAILABLE.length()) != null
				&& NO_OUTPUT_AVAILABLE.equals(document.get(0, NO_OUTPUT_AVAILABLE.length()));
	}

    /**
     *  Connects this provider to the tlc output source registry.
     *  
     *  There are two different tlc output source registries,
     *  one for trace exploration and one for model checking. This
     *  connects to the one for model checking.
     */
	protected boolean connectToSourceRegistry() {
		return TLCOutputSourceRegistry.getModelCheckSourceRegistry().connect(this);
    }

    /**
     * Add a presenter.
     * @param presenter
     */
    public void addDataPresenter(final ITLCModelLaunchDataPresenter presenter) {
    	m_dataPresenters.add(presenter);
    	populate();
    }
    
    /**
     * Remove a presenter added via {@link #addDataPresenter(ITLCModelLaunchDataPresenter)}
     * @param presenter
     */
    public void removeDataPresenter(final ITLCModelLaunchDataPresenter presenter) {
    	m_dataPresenters.remove(presenter);
    	populate();
    }

    public List<TLCError> getErrors()
    {
        return errors;
    }

    public void setErrors(List<TLCError> errors)
    {
        this.errors = errors;
    }

    public long getStartTimestamp()
    {
        return startTimestamp;
    }

    public long getFinishTimestamp()
    {
        return finishTimestamp;
    }
    
    public String getTLCMode() {
    	return tlcMode;
    }

    public String getCoverageTimestamp()
    {
        return coverageTimestamp;
    }

    public void setCoverageTimestamp(String coverageTimestamp)
    {
        this.coverageTimestamp = coverageTimestamp;
    }

    public CoverageInformation getCoverageInfo()
    {
        return coverageInfo;
    }

    public boolean hasZeroCoverage() {
    	return zeroCoverage;
    }
    
    public List<StateSpaceInformationItem> getProgressInformation()
    {
        return progressInformation;
    }

    public void setProgressInformation(List<StateSpaceInformationItem> progressInformation)
    {
        this.progressInformation = progressInformation;
    }

    public Document getUserOutput()
    {
        return userOutput;
    }

    public Document getProgressOutput()
    {
        return progressOutput;
    }

    public long getLastCheckpointTimeStamp()
    {
        return lastCheckpointTimeStamp;
    }
    
    public void setCurrentStatus(String currentStatus)
    {
        this.currentStatus = currentStatus;
        
    }

    public String getCurrentStatus()
    {
        return currentStatus;
    }

	public boolean isDone() {
		return isDone;
	}

    /**
     * @param fingerprintCollisionProbability the fingerprintCollisionProbability to set
     */
    public void setFingerprintCollisionProbability(String fingerprintCollisionProbability)
    {
        this.fingerprintCollisionProbability = fingerprintCollisionProbability;
    }

    /**
     * @return the fingerprintCollisionProbability
     */
    public String getFingerprintCollisionProbability()
    {
        return fingerprintCollisionProbability;
    }

    public String getCalcOutput()
    {
        return constantExprEvalOutput;
    }
    
    private static final Pattern collisionProbabilityPattern = Pattern.compile(
			"^Model checking completed\\. No error has been found\\.\\n  Estimates of the probability "
			+ "that TLC did not check all reachable states\\n  because two distinct states had the "
			+ "same fingerprint:\\n  calculated \\(optimistic\\):  val = "
			+ "([0-9]*\\.?[0-9]+[eE][-+]?[0-9]+?)" // group 1
			+ "(\\n  based on the actual fingerprints:  val = "
			+ "([0-9]*\\.?[0-9]+[eE][-+]?[0-9]+?))?$"); // group 3 iff present (group 2 is last two lines)

    /**
     * Extracts the fingerprint collision probability information line
     * from the TLC_SUCCESS message output by TLC when it finishes.
     * This is a hack that must be recoded if TLC's output format
     * changes.
     * 
     * @param outputMessage
     * @return
     */
    private String extractCollisionProbability(String outputMessage)
    {
		final Matcher matcher = collisionProbabilityPattern.matcher(outputMessage);
		if (matcher.find()) {
			final String optimistic = matcher.group(1);
			final String actual = matcher.group(3);
			if (actual != null) {
				return String.format("calculated: %s  observed: %s", optimistic, actual);
			} else {
				return String.format("calculated: %s", optimistic);
			}
		}
		return ""; // legacy support
    }
    
	/**
	 * @return The model name
	 */
	protected String getModelName() {
		// defined here so subclasses can override which ain't backed by a real
		// file (e.g. unit test)
		return getModel().getName();
	}
	
	public String toString() {
		return getModel().getSpec().getName() + "___" + getModelName();
	}

	public int getFPIndex() {
		return this.fpIndex;
	}

	public boolean isSymmetryWithLiveness() {
		return isSymmetryWithLiveness;
	}

	public boolean isConstraintsWithLiveness() {
		return isConstraintsWithLiveness;
	}

	private final static SimpleDateFormat SDF = new SimpleDateFormat(
			"yyyy-MM-dd HH:mm:ss");
	
	public static Date parseDate(final String str) {
		try {
			return SDF.parse(str);
		} catch (ParseException e) {
			return new Date();
		}
	}

	public static String formatInterval(final long firstTS, final long secondTS) {
		final long interval = secondTS - firstTS;
		final long hr = TimeUnit.MILLISECONDS.toHours(interval);
		final long min = TimeUnit.MILLISECONDS.toMinutes(interval - TimeUnit.HOURS.toMillis(hr));
		final long sec = TimeUnit.MILLISECONDS
				.toSeconds(interval - TimeUnit.HOURS.toMillis(hr) - TimeUnit.MINUTES.toMillis(min));

		return String.format("%02d:%02d:%02d", hr, min, sec);
	}
}
