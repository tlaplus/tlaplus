package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.FindReplaceDocumentAdapter;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.TraceExpressionInformationHolder;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelWriter;

/**
 * A data provider for runs of the trace explorer. This mostly uses the methods from
 * {@link TLCModelLaunchDataProvider}, but it also performs some processing
 * of an error trace, if one is produced.
 * 
 * @author Daniel Ricketts
 *
 */
public class TraceExplorerDataProvider extends TLCModelLaunchDataProvider
{

    // a hashmap containing information about trace expressions if this
    // provider is for a run of the trace explorer
    // the key is the variable name used for the expression, the value
    // is an instance of TraceExpressionInformationHolder corresponding
    // to the expression.
    private Hashtable traceExpressionDataTable;

    public TraceExplorerDataProvider(ILaunchConfiguration config)
    {
        super(config);

    }

    /** 
     * This is currently called by the constructor of TLCModelLaunchDataProvider
     * 
     * There are two different tlc output source registries,
     * one for trace exploration and one for model checking. This
     * connects to the one for trace exploration.
     */
    protected void connectToSourceRegistry()
    {
        TLCOutputSourceRegistry.getTraceExploreSourceRegistry().connect(this);
    }

    public void onDone()
    {
        super.onDone();

        getTraceExpressionsInformation();

        processTraceForTraceExplorer();
    }

    /**
     * Collects and stores trace expression information for later use.
     */
    private void getTraceExpressionsInformation()
    {
        // erase existing information
        if (traceExpressionDataTable == null)
        {
            traceExpressionDataTable = new Hashtable();
        } else
        {
            traceExpressionDataTable.clear();
        }

        try
        {
            // retrieve the TE file
            // create a document provider, in order to create a document and the
            // search adapter
            IFile teFile = ModelHelper.getTraceExplorerTLAFile(getConfig());
            FileEditorInput teFileEditorInput = new FileEditorInput((IFile) teFile);
            FileDocumentProvider teFileDocumentProvider = new FileDocumentProvider();

            teFileDocumentProvider.connect(teFileEditorInput);

            // the document connected to the TE file
            IDocument teDocument = teFileDocumentProvider.getDocument(teFileEditorInput);

            // the search adapter on the TE file
            FindReplaceDocumentAdapter teSearcher = new FindReplaceDocumentAdapter(teDocument);

            // search for comments containing the information about trace explorer expressions
            String regularExpression = FindReplaceDocumentAdapter.escapeForRegExPattern("\\* ") + ":[0-2]:"
                    + ModelWriter.TRACE_EXPR_VAR_SCHEME + "_[0-9]{17,}:.*\n";
            IRegion region = teSearcher.find(0, regularExpression, true, true, false, true);

            while (region != null)
            {
                System.out.println(teDocument.get(region.getOffset(), region.getLength()));
                // found a region
                // first character should be the level of the expression
                String commentString = teDocument.get(region.getOffset(), region.getLength());
                // commentString should be of the form "\* :x:___trace_var_12321312312312:expr"
                // where x is the level of the expression
                String[] stringSections = commentString.split(":", 4);
                int level = Integer.parseInt(stringSections[1]);
                String variableName = stringSections[2];
                String expression = stringSections[3];

                TraceExpressionInformationHolder expressionData = new TraceExpressionInformationHolder(expression,
                        null, variableName);
                expressionData.setLevel(level);
                this.traceExpressionDataTable.put(variableName.trim(), expressionData);

                region = teSearcher.find(region.getOffset() + region.getLength(), regularExpression, true, true, false,
                        true);
            }

        } catch (CoreException e)
        {
            TLCUIActivator.logError("Error finding trace expression information in TE.tla file.", e);
        } catch (BadLocationException e)
        {
            TLCUIActivator.logError("Error finding trace expression information in TE.tla file.", e);
        }
    }

    /**
     * Performs processing for errors produces after a run of the trace explorer.
     * 
     * In particular, this changes the names of the variables corresponding to trace
     * explorer expressions to the actual expressions. It also shifts the values of expressions
     * of level 2. For an expressions of level 2 (expression with primed variables), the value in
     * state x becomes the original value in state x+1. The value in the final state of such
     * expressions is equal to "--".
     * 
     * 
     */
    private void processTraceForTraceExplorer()
    {
        List originalTrace = getOriginalTrace();
        Assert.isNotNull(originalTrace, "Could not get original trace after running trace explorer. This is a bug.");
        try
        {
            Iterator it = getErrors().iterator();
            while (it.hasNext())
            {
                TLCError error = (TLCError) it.next();

                if (error.hasTrace())
                {
                    List newTrace = error.getStates();

                    Iterator newTraceIt = newTrace.iterator();
                    Iterator originalTraceIt = originalTrace.iterator();

                    TLCState currentStateNewTrace = (TLCState) newTraceIt.next();
                    TLCState nextStateNewTrace = null;

                    TLCState currentStateOriginalTrace = (TLCState) originalTraceIt.next();

                    /*
                     * The following values are used in a bit of a hack to deal with 
                     * back to state traces.
                     * 
                     * isBackToStateOrStutteringTrace: flag indicating if the trace is a back to
                     * state trace or a stuttering trace
                     * 
                     * totalNumStates: total number of states in the trace NOT including
                     * the state labeled "Back to state x". This number is meaningless
                     * if the trace is not a back to state trace.
                     * 
                     * stateNum: counter giving the state number of currentState within the
                     * following while loop
                     * 
                     * The hack is necessary for the following reason. 
                     */
                    boolean isBackToStateOrStutteringTrace = getConfig().getAttribute(
                            IModelConfigurationConstants.IS_TRACE_BACK_TO_STATE, false)
                            || getConfig().getAttribute(IModelConfigurationConstants.IS_TRACE_STUTTERING, false);
                    int totalNumStates = getConfig().getAttribute(IModelConfigurationConstants.TRACE_NUM_STATES,
                            newTrace.size());
                    int stateNum = 0;

                    while (newTraceIt.hasNext())
                    {
                        stateNum++;

                        nextStateNewTrace = (TLCState) newTraceIt.next();

                        TLCVariable[] currentStateNewTraceVariables = currentStateNewTrace.getVariables();
                        TLCVariable[] nextStateNewTraceVariables = nextStateNewTrace.getVariables();

                        // iterate through the variables
                        for (int i = 0; i < currentStateNewTraceVariables.length; i++)
                        {
                            // This code assumes that the variables are in the same order in each state
                            String variableName = currentStateNewTraceVariables[i].getName();
                            // if next state is back to state or stuttering, it has no variables, so the code
                            // contained within the if block would cause an NPE
                            if (!nextStateNewTrace.isBackToState() && !nextStateNewTrace.isStuttering())
                            {
                                Assert.isTrue(variableName.equals(nextStateNewTraceVariables[i].getName()),
                                        "Variables are not in the same order in each state. This is unexpected.");
                            }

                            // retrieve the object containing the data corresponding to the variable.
                            // this object will be null if the variable currently being looked at does
                            // not represent a trace explorer expression
                            // If the variable does represent a trace explorer expression, then the following
                            // object will contain the variable name, the expression, and the level of the expression
                            TraceExpressionInformationHolder traceExpressionData = (TraceExpressionInformationHolder) traceExpressionDataTable
                                    .get(variableName.trim());

                            if (traceExpressionData != null)
                            {
                                // we have located a trace expression variable

                                // if next state is back to state or stuttering, it has no variables, so the
                                // code contained within this if block would not apply
                                if (!nextStateNewTrace.isBackToState() && !nextStateNewTrace.isStuttering()
                                        && traceExpressionData.getLevel() == 2)
                                {
                                    // found expression with primed variables
                                    // shift the value from the next state to the current state
                                    currentStateNewTraceVariables[i].setValue(nextStateNewTraceVariables[i].getValue());

                                }

                                // set the name to be the expression the variable represents
                                currentStateNewTraceVariables[i].setName(traceExpressionData.getExpression());

                            }
                        }

                        // remove extra states
                        if (stateNum >= totalNumStates && isBackToStateOrStutteringTrace
                                && !nextStateNewTrace.isBackToState() && !nextStateNewTrace.isStuttering())
                        {
                            newTraceIt.remove();
                        }

                        currentStateNewTrace = nextStateNewTrace;
                    }

                    // fix the final state
                    if (!currentStateNewTrace.isStuttering() && !currentStateNewTrace.isBackToState())
                    {
                        TLCVariable[] currentStateVariables = currentStateNewTrace.getVariables();

                        // iterate through the variables
                        for (int i = 0; i < currentStateVariables.length; i++)
                        {

                            TraceExpressionInformationHolder traceExpressionData = (TraceExpressionInformationHolder) traceExpressionDataTable
                                    .get(currentStateVariables[i].getName().trim());

                            if (traceExpressionData != null)
                            {
                                // we have located a trace expression variable

                                if (traceExpressionData.getLevel() == 2)
                                {
                                    // expression with primed variables
                                    // shift the value from the next state to the current state
                                    currentStateVariables[i].setValue(TLCVariableValue.parseValue("\"--\""));
                                }

                                // set the name to be the expression the variable represents
                                currentStateVariables[i].setName(traceExpressionData.getExpression());
                            }
                        }
                    }
                }
            }
        } catch (CoreException e)
        {
            TLCUIActivator.logError("Error processing trace after running trace explorer.", e);
        }
    }

    private List getOriginalTrace()
    {
        TLCModelLaunchDataProvider originalTraceProvider = TLCOutputSourceRegistry.getModelCheckSourceRegistry()
                .getProvider(getConfig());
        List errors = originalTraceProvider.getErrors();
        if (errors != null)
        {
            Iterator it = errors.iterator();
            while (it.hasNext())
            {
                TLCError error = (TLCError) it.next();
                if (error.hasTrace())
                {
                    return error.getStates();
                }
            }
        }

        // no trace found
        return null;
    }

}
