package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.List;
import java.util.Vector;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITypedRegion;
import org.lamport.tla.toolbox.tool.tlc.output.ITLCOutputListener;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCRegion;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCRegionContainer;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.CoverageInformationItem;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.GeneralOutputParsingHwelper;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.StateSpaceInformationItem;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.TLCError;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.TLCState;
import org.lamport.tla.toolbox.util.UIHelper;

import tlc2.output.EC;
import tlc2.output.MP;

/**
 * Container for the data about the model launch
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCModelLaunchDataProvider implements ITLCOutputListener
{
    public static final String NO_OUTPUT_AVAILABLE = "No execution data is available";

    // presenter for the current process
    private ITLCModelLaunchDataPresenter presenter;
    // list of errors
    private List errors;
    // start time
    private String startTimestamp;
    // end time
    private String finishTimestamp;
    // coverage at
    private String coverageTimestamp;
    // coverage items
    private List coverageInfo;
    // progress information
    private List progressInformation;

    // last detected error
    private TLCError lastDetectedError;
    // flag indicating that the job / file output is finished
    private boolean isDone = false;
    // progress output
    private Document progressOutput;
    // user output
    private Document userOutput;
    // the model, which is represented by the current launch data provider
    private ILaunchConfiguration config;

    public TLCModelLaunchDataProvider(ILaunchConfiguration config)
    {
        this.config = config;
        initialize();
    }

    /**
     * Resets the values to defaults
     */
    private void initialize()
    {
        errors = new Vector();
        coverageInfo = new Vector();
        progressInformation = new Vector();
        startTimestamp = "";
        finishTimestamp = "";
        coverageTimestamp = "";

        progressOutput = new Document(NO_OUTPUT_AVAILABLE);
        userOutput = new Document(NO_OUTPUT_AVAILABLE);
        
        TLCOutputSourceRegistry.getStatusRegistry().connect(this);
        informPresenter(ITLCModelLaunchDataPresenter.USER_OUTPUT);
        informPresenter(ITLCModelLaunchDataPresenter.PROGRESS_OUTPUT);
    }

    /**
     * Inform the view, if any
     * @param fieldId
     */
    private void informPresenter(int fieldId) 
    {
        if (presenter != null) 
        {
            presenter.modelChanged(this, fieldId);
        }
    }
    
    /**
     * Populate data to the presenter 
     */
    public void populate()
    {
        for (int i=0; i < ITLCModelLaunchDataPresenter.ALL_FIELDS.length; i++) 
        {
            informPresenter(ITLCModelLaunchDataPresenter.ALL_FIELDS[i]);
        }
    }
    
    /**
     * Name of the model
     */
    public String getProcessName()
    {
        // the model filename is good because it is unique
        return config.getFile().getName();
    }

    public void onDone()
    {
        isDone = true;
    }

    public void onNewSource()
    {
        // everything that was saved should be erased
        initialize();
        
        populate();
    }

    public void onOutput(ITypedRegion region, IDocument document)
    {
        // restarting
        if (isDone)
        {
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
            case MP.STATE:
                Assert.isNotNull(this.lastDetectedError,
                        "The state encountered without the error describing the reason for it. This is a bug.");
                this.lastDetectedError.addState(TLCState.parseState(outputMessage));
                break;
            case MP.ERROR:
            case MP.TLCBUG:
            case MP.WARNING:

                switch (messageCode) {
                // errors to skip
                case EC.TLC_BEHAVIOR_UP_TO_THIS_POINT:
                case EC.TLC_COUNTER_EXAMPLE:
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
                    this.lastDetectedError = TLCModelLaunchDataProvider.createError(tlcRegion, document);
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

                switch (messageCode) {
                // Progress information
                case EC.TLC_VERSION:
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
                case EC.TLC_LIVE_IMPLIED:
                    setDocumentText(this.progressOutput, outputMessage, true);
                    break;
                case EC.TLC_STARTING:
                    this.startTimestamp = GeneralOutputParsingHwelper.parseTLCTimestamp(outputMessage);
                    informPresenter(ITLCModelLaunchDataPresenter.START_TIME);
                    break;
                case EC.TLC_FINISHED:
                    this.finishTimestamp = GeneralOutputParsingHwelper.parseTLCTimestamp(outputMessage);
                    informPresenter(ITLCModelLaunchDataPresenter.END_TIME);
                    break;

                case EC.TLC_PROGRESS_STATS:
                    this.progressInformation.add(StateSpaceInformationItem.parse(outputMessage));

                    break;
                // Coverage information
                case EC.TLC_COVERAGE_START:
                    this.coverageTimestamp = CoverageInformationItem.parseCoverageTimestamp(outputMessage);
                    this.coverageInfo = new Vector();
                    informPresenter(ITLCModelLaunchDataPresenter.COVERAGE_TIME);
                    informPresenter(ITLCModelLaunchDataPresenter.COVERAGE);
                    break;
                case EC.TLC_COVERAGE_VALUE:
                    this.coverageInfo.add(CoverageInformationItem.parse(outputMessage));
                    informPresenter(ITLCModelLaunchDataPresenter.COVERAGE);
                    break;
                case EC.TLC_COVERAGE_END:
                    break;
                default:
                    setDocumentText(this.userOutput, outputMessage, true);
                    break;
                }
                break;
            default:
                throw new IllegalArgumentException("This is a bug, the TLCToken with unexpected severity detected: "
                        + severity);
            }

        } else
        {
            setDocumentText(this.userOutput, outputMessage, true);
            // TLCUIActivator.logDebug("Unknown type detected: " + region.getType() + " message " + outputMessage);
        }
    }

    public void destroy()
    {
        TLCOutputSourceRegistry.getStatusRegistry().disconnect(this);
    }
    

    /**
     * Creates an error object
     * @param tlcRegion
     * @param document
     * @return
     */
    private static TLCError createError(TLCRegion tlcRegion, IDocument document)
    {
        TLCError topError = new TLCError();
        if (tlcRegion instanceof TLCRegionContainer)
        {
            TLCRegionContainer container = (TLCRegionContainer) tlcRegion;
            ITypedRegion[] regions = container.getSubRegions();
            Assert.isTrue(regions.length < 3, "Unexpected error region structure, this is a bug.");
            for (int i = 0; i < regions.length; i++)
            {
                if (regions[i] instanceof TLCRegion)
                {
                    TLCError cause = createError((TLCRegion) regions[i], document);
                    topError.setCause(cause);
                } else
                {
                    String output;
                    try
                    {
                        output = document.get(tlcRegion.getOffset(), tlcRegion.getLength());
                        topError.setMessage(output);
                        topError.setErrorCode(tlcRegion.getMessageCode());
                    } catch (BadLocationException e)
                    {
                        TLCUIActivator.logError("Error parsing the error message", e);
                    }
                }
            }
        }

        return topError;
    }

    /**
     * Sets text to a document
     * @param document
     * @param message
     * @param append
     * @throws BadLocationException
     * Has to be run from non-UI thread
     */
    public static synchronized void setDocumentText(final IDocument document, final String message, final boolean append)
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
     * Retrieves the config
     * @return config this launch data provider is representing
     */
    public ILaunchConfiguration getConfig()
    {
        return this.config;
    }

    
    public void setPresenter(ITLCModelLaunchDataPresenter presenter)
    {
        this.presenter = presenter;
    }

    public List getErrors()
    {
        return errors;
    }

    public void setErrors(List errors)
    {
        this.errors = errors;
    }

    public String getStartTimestamp()
    {
        return startTimestamp;
    }

    public void setStartTimestamp(String startTimestamp)
    {
        this.startTimestamp = startTimestamp;
    }

    public String getFinishTimestamp()
    {
        return finishTimestamp;
    }

    public void setFinishTimestamp(String finishTimestamp)
    {
        this.finishTimestamp = finishTimestamp;
    }

    public String getCoverageTimestamp()
    {
        return coverageTimestamp;
    }

    public void setCoverageTimestamp(String coverageTimestamp)
    {
        this.coverageTimestamp = coverageTimestamp;
    }

    public List getCoverageInfo()
    {
        return coverageInfo;
    }

    public void setCoverageInfo(List coverageInfo)
    {
        this.coverageInfo = coverageInfo;
    }

    public List getProgressInformation()
    {
        return progressInformation;
    }

    public void setProgressInformation(List progressInformation)
    {
        this.progressInformation = progressInformation;
    }

    public Document getUserOutput()
    {
        return userOutput;
    }

    public void setUserOutput(Document userOutput)
    {
        this.userOutput = userOutput;
    }

    public Document getProgressOutput()
    {
        return progressOutput;
    }

    public void setProgressOutput(Document progressOutput)
    {
        this.progressOutput = progressOutput;
    }

}
