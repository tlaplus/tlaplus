package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.Arrays;
import java.util.Comparator;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.FindReplaceDocumentAdapter;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.tool.tlc.launch.TraceExpressionInformationHolder;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCRegion;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCRegionContainer;
import org.lamport.tla.toolbox.tool.tlc.traceexplorer.TraceExplorerHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelWriter;

import tlc2.output.EC;

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
    private static String TE_ERROR_HEADER = "Error(s) from running the Trace Explorer:\n";

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
                    + ModelWriter.TRACE_EXPR_VAR_SCHEME + "_[0-9]{17,}:[\\s\\S]*?"
                    + Pattern.quote(ModelWriter.CONSTANT_EXPRESSION_EVAL_IDENTIFIER) + "\n";
            IRegion region = teSearcher.find(0, regularExpression, true, true, false, true);

            while (region != null)
            {
                // found a region
                // first character should be the level of the expression
                String commentString = teDocument.get(region.getOffset(), region.getLength());
                // commentString should be of the form "\* :x:___trace_var_12321312312312:expr"$!@$!@$!@$!@$!""
                // where x is the level of the expression
                String[] stringSections = commentString.split(":", 4);
                int level = Integer.parseInt(stringSections[1]);
                String variableName = stringSections[2];
                // should be expr"$!@$!@$!@$!@$!" where "$!@$!@$!@$!@$!" is the delimiter
                String expressionAndDelimiter = stringSections[3];
                String expression = expressionAndDelimiter.substring(0, expressionAndDelimiter
                        .indexOf(ModelWriter.CONSTANT_EXPRESSION_EVAL_IDENTIFIER));

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
     * Performs processing for the error and the error trace produced after a run of the trace explorer.
     * This method replaces the message of the error with a trace produced by the trace explorer with
     * the message from the original error with a trace for which the trace explorer was run if that message
     * should be shown to the user.
     * 
     * This method does the following to a trace:
     * 
     * 1.) Changes the names of the variables corresponding to trace
     * explorer expressions to the actual expressions.
     * 
     * 2.) It also shifts the values of expressions
     * of level 2. For an expressions of level 2 (expression with primed variables), the value in
     * state x becomes the original value in state x+1. The value in the final state of such
     * expressions is equal to "--".
     * 
     * 3.) Changes the state labels "<Action ... in module TE> State (num = 3)" to the state labels
     * of the original trace. The goal is to have no reference to module TE.
     * 
     * 4.) Puts the variables representing the trace explorer expressions before the actual
     * variables in each state.
     * 
     * 5.) Removes any extra states produced by the trace explorer. This can sometimes occur when
     * evaluating expressions for a looping ("Back to state") trace and for a stuttering trace. This can
     * be illustrated by an example. Consider the following trace:



    <Initial predicate> <State num 1>
    x=0

    <Action ...> <State num 2>
    x=1

    <Back to state 1>




    The user wants to evaluate the following expression:

    x' >= x

    The toolbox uses the following as init and next:

    Init ==
     /\ x=0
     /\ __trace_var_213123 = "--"

    Next ==
     \/ /\ x=0
        /\ x'=1
        /\ __trace_var_213123' = (x'>=x)
     \/ /\ x=1
        /\ x'=0
        /\ __trace_var_213123' = (x'>=x)

    We check the following property:

    prop_23432 ==
    ~([]<>(x=1)/\[]<>(x=0))

    This produces the following trace:



    <Initial predicate> <State num 1>
    x=0
    __trace_var_213123 = "--"

    <Action ...> <State num 2>
    x=1
    __trace_var_213123 = TRUE

    <Action ...> <State num 3>
    x=0
    __trace_var_213123 = FALSE

    <Back to state 2>



    Note the additional state with x=0 and __trace_var_213123 = FALSE. We shift the values for
    expressions with primed variables up by one state, so this extra state is necessary for
    producing the value for the expression "x' >= x" in the second state of the trace (In non-looping
    traces, there is no value for the expression in the final state, so we simply assign it
    the value "--".) The processing by this method eliminates this extra state but uses the value for
    __trace_var_213123, so that the following trace can be displayed to the user:



    <Initial predicate> <State num 1>
    x=0
    (x' >= x)    =     TRUE

    <Action ...> <State num 2>
    x=1
    (x' >= x)    =    FALSE

    <Back to state 1>

     */
    private void processTraceForTraceExplorer()
    {
        // retrieve the error with a trace for which the trace explorer was run
        TLCError originalErrorWithTrace = TraceExplorerHelper.getErrorOfOriginalTrace(getConfig());
        Assert.isNotNull(originalErrorWithTrace,
                "Could not get original trace after running trace explorer. This is a bug.");

        // retrieve the original trace
        // this is necessary for items (3) and (5) from the list in the
        // documentation for this method
        List originalTrace = originalErrorWithTrace.getStates();
        Assert.isNotNull(originalTrace, "Could not get original trace after running trace explorer. This is a bug.");

        // iterate through the errors to find one with a trace
        Iterator it = getErrors().iterator();
        while (it.hasNext())
        {
            TLCError error = (TLCError) it.next();

            if (error.hasTrace())
            {
                // Set the message, cause, and code of the error to the message of the original
                // error for which the trace explorer was run if the new error
                // message is for an invariant or property violation or deadlock. An invariant
                // or property violation or deadlock indicates that the trace explorer ran
                // successfully.
                int errorCode = error.getErrorCode();
                if (errorCode == EC.TLC_DEADLOCK_REACHED || errorCode == EC.TLC_TEMPORAL_PROPERTY_VIOLATED
                        || errorCode == EC.TLC_INVARIANT_VIOLATED_BEHAVIOR
                        || errorCode == EC.TLC_INVARIANT_VIOLATED_INITIAL)
                {
                    error.setErrorCode(originalErrorWithTrace.getErrorCode());
                    error.setMessage(originalErrorWithTrace.getMessage());
                    error.setCause(originalErrorWithTrace.getCause());
                } else
                {
                    error.setMessage(TE_ERROR_HEADER + error.getMessage());
                }

                // a comparator used for sorting the variables within each
                // state so that the variables representing the trace explorer
                // expressions appear first in each state
                Comparator varComparator = new Comparator() {

                    public int compare(Object arg0, Object arg1)
                    {
                        TLCVariable var0 = (TLCVariable) arg0;
                        TLCVariable var1 = (TLCVariable) arg1;
                        if ((var0.isTraceExplorerVar() && var1.isTraceExplorerVar())
                                || (!var0.isTraceExplorerVar() && !var1.isTraceExplorerVar()))
                        {
                            // both represent TE expressions or neither does
                            // use string comparison to make sure
                            // that the variables appear in the same order
                            // in every state
                            return var0.getName().compareTo(var1.getName());
                        } else if (var0.isTraceExplorerVar())
                        {
                            // var0 should appear before
                            return -1;
                        } else
                        {
                            // var1 represents TE expression, so it should appear before
                            return 1;
                        }
                    }
                };

                // found an error with a trace

                // this is the trace produced by the run
                // of TLC for the trace explorer
                List newTrace = error.getStates();

                Iterator newTraceIt = newTrace.iterator();
                Iterator originalTraceIt = originalTrace.iterator();

                TLCState currentStateNewTrace = (TLCState) newTraceIt.next();
                TLCState nextStateNewTrace = null;

                TLCState currentStateOriginalTrace = (TLCState) originalTraceIt.next();

                /*
                 * The following while loop performs items 1-4 for some of the states.
                 * In particular, if the original trace has n states and the trace produced
                 * by the trace explorer has m states, this loop performs
                 * items 1-4 for states 1 through min(n-1, m-1). The trace produced by the
                 * trace explorer can be shorter than the original trace if there is a TLC error
                 * during evaluation of one of the states. The trace produced by the trace explorer
                 * can be longer than the original trace as in the example of item 5.
                 * 
                 * The final state of the trace produced by the trace explorer is processed
                 * after this loop. Item 5 is also accomplished after this loop.
                 */
                while (newTraceIt.hasNext() && originalTraceIt.hasNext())
                {

                    // change the label of the state of newTrace to the label of the state
                    // of the original trace
                    currentStateNewTrace.setLabel(currentStateOriginalTrace.getLabel());

                    // set the location of the current state of the new trace
                    currentStateNewTrace.setLocation(currentStateOriginalTrace.getModuleLocation());

                    // need to get the next state in order to perform any
                    // shifting of expression values (item 2 in the documentation)
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

                            // If next state is back to state or stuttering, it has no variables, so the
                            // code contained within this if block would not apply. It should be unnecessary
                            // to check for this because the while loop should terminate before this happens.
                            if (!nextStateNewTrace.isBackToState() && !nextStateNewTrace.isStuttering()
                                    && traceExpressionData.getLevel() == 2)
                            {
                                // found expression with primed variables
                                // shift the value from the next state to the current state
                                currentStateNewTraceVariables[i].setValue(nextStateNewTraceVariables[i].getValue());

                            }

                            // set the name to be the expression the variable represents
                            currentStateNewTraceVariables[i].setName(traceExpressionData.getExpression());

                            // flag this as a variable representing a trace explorer expression
                            currentStateNewTraceVariables[i].setTraceExplorerVar(true);

                        }
                    }

                    // sort the variables so that the variables representing trace explorer
                    // expressions appear first
                    Arrays.sort(currentStateNewTraceVariables, varComparator);

                    currentStateNewTrace = nextStateNewTrace;

                    currentStateOriginalTrace = (TLCState) originalTraceIt.next();
                }

                /*
                 * Remove any extra states (item 5).
                 * 
                 * This is only necessary for looping or stuttering traces
                 * (n elements in original trace, m elements in new trace)-
                 *       if (m >= n) remove states n..m
                 *       else do nothing
                 *       
                 * if (m >= n), the new trace will be left with n-1 elements.
                 * Later code adds the final stuttering or "back to state" state
                 * to these traces.
                 * 
                 * There should never be extra states for non-looping, non-stuttering
                 * traces.
                 */
                if ((currentStateOriginalTrace.isBackToState() || currentStateOriginalTrace.isStuttering())
                        && newTrace.size() >= originalTrace.size())
                {
                    newTrace.subList(originalTrace.size() - 1, newTrace.size()).clear();
                }

                // new trace should now be no longer than the original trace
                Assert.isTrue(newTrace.size() <= originalTrace.size(),
                        "States from trace explorer trace not removed properly.");

                // fix the final state
                TLCState finalStateOriginalTrace = (TLCState) originalTrace.get(originalTrace.size() - 1);

                if (newTrace.size() < originalTrace.size() - 1
                        || (!finalStateOriginalTrace.isStuttering() && !finalStateOriginalTrace.isBackToState()))
                {
                    /*
                     *  For a non-looping and non-stuttering state, just set the expressions
                     *  with primed variables equal to "--" for the last state.
                     *  
                     *  Do the same thing if the new trace is less than the original trace size minus 1.
                     *  This means there was a TLC error before evaluating all of the states, so
                     *  even if the original trace finished with a looping state or a stuttering state, the
                     *  trace that is displayed to the user should not. It should terminate before the TLC error
                     *  occurred.
                     */

                    TLCState finalStateNewTrace = (TLCState) newTrace.get(newTrace.size() - 1);

                    // state in the original trace at the same position as finalStateNewTrace
                    TLCState samePositionOriginalTrace = (TLCState) originalTrace.get(newTrace.size() - 1);

                    // set the label of the final state of the new trace
                    finalStateNewTrace.setLabel(samePositionOriginalTrace.getLabel());

                    // set the location of the final state of the new trace
                    finalStateNewTrace.setLocation(samePositionOriginalTrace.getModuleLocation());

                    TLCVariable[] finalStateNewTraceVariables = finalStateNewTrace.getVariables();

                    // iterate through the variables
                    for (int i = 0; i < finalStateNewTraceVariables.length; i++)
                    {

                        TraceExpressionInformationHolder traceExpressionData = (TraceExpressionInformationHolder) traceExpressionDataTable
                                .get(finalStateNewTraceVariables[i].getName().trim());

                        if (traceExpressionData != null)
                        {
                            // we have located a trace expression variable

                            if (traceExpressionData.getLevel() == 2)
                            {
                                // expression with primed variables
                                // shift the value from the next state to the current state
                                finalStateNewTraceVariables[i].setValue(TLCVariableValue.parseValue("\"--\""));
                            }

                            // set the name to be the expression the variable represents
                            finalStateNewTraceVariables[i].setName(traceExpressionData.getExpression());
                            // flag this as a variable representing a trace explorer expression
                            finalStateNewTraceVariables[i].setTraceExplorerVar(true);
                        }
                    }

                    // sort the variables of the final state
                    Arrays.sort(finalStateNewTraceVariables, varComparator);
                } else if (finalStateOriginalTrace.isBackToState())
                {
                    error.addState(TLCState.BACK_TO_STATE(finalStateOriginalTrace.getStateNumber()));
                } else
                {
                    // stuttering trace
                    error.addState(TLCState.STUTTERING_STATE(finalStateOriginalTrace.getStateNumber()));
                }

            } else
            {
                // error does not have trace
                // indicate that it is an error from the trace explorer
                error.setMessage(TE_ERROR_HEADER + error.getMessage());
            }
        }
    }

    /**
     * Creates an error without any replacement of text from the error message reported by TLC.
     */
    protected TLCError createError(TLCRegion tlcRegion, IDocument tlcOutputDocument)
    {
        // the root of the error trace
        TLCError topError = new TLCError();

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
                    TLCError cause = createError((TLCRegion) regions[i], tlcOutputDocument);
                    topError.setCause(cause);
                } else
                {
                    try
                    {
                        // set error text
                        topError.setMessage(tlcOutputDocument.get(tlcRegion.getOffset(), tlcRegion.getLength()));
                        // set error code
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

}
