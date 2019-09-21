package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.dialogs.IDialogSettings;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.FindReplaceDocumentAdapter;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.tool.tlc.launch.TraceExpressionInformationHolder;
import org.lamport.tla.toolbox.tool.tlc.model.Formula;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.model.ModelWriter;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCError.Order;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCRegion;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCRegionContainer;
import org.lamport.tla.toolbox.tool.tlc.traceexplorer.TraceExplorerHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.view.TLCErrorView;
import org.lamport.tla.toolbox.util.LegacyFileDocumentProvider;
import org.lamport.tla.toolbox.util.UIHelper;

import tlc2.output.EC;

/**
 * A data provider for runs of the trace explorer. This mostly uses the methods from
 * {@link TLCModelLaunchDataProvider}, but it also performs some processing
 * of an error trace, if one is produced.
 * 
 * @author Daniel Ricketts
 */
public class TraceExplorerDataProvider extends TLCModelLaunchDataProvider
{
    private static String TE_ERROR_HEADER = "Error(s) from running the Trace Explorer:\n";

    
    // a hashmap containing information about trace expressions if this
    // provider is for a run of the trace explorer
    // the key is the variable name used for the expression, the value
    // is an instance of TraceExpressionInformationHolder corresponding
    // to the expression.
    private Hashtable<String, TraceExpressionInformationHolder> traceExpressionDataTable;

    public TraceExplorerDataProvider(Model model)
    {
        super(model);
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

        final IEditorPart activeEditor = UIHelper.getActiveEditor();
		if (activeEditor != null) {
			if (activeEditor instanceof ModelEditor) {
				final ModelEditor activeModelEditor = (ModelEditor) activeEditor;
				if (activeModelEditor.getModel() != null) {
					UIHelper.runUIAsync(() -> {
						TLCErrorView.updateErrorView(activeModelEditor);
					});
				}
			}
		}
    }

    /**
     * Collects and stores trace expression information for later use.
     */
    private void getTraceExpressionsInformation()
    {
    	if (traceExpressionDataTable == null) {
			// getTraceExpressionsInformation is called implicitly when
			// super(config) is called in the constructor. Thus, we have to
			// initialize it here.
    		traceExpressionDataTable = new Hashtable<String, TraceExpressionInformationHolder>();
    	}
        // erase existing information
        traceExpressionDataTable.clear();

        /*
         * Retrieve the TE file and create a document provider. This document
         * provider will be used to connect to the file editor input for
         * the TE file so that a Document representation of the file can
         * be created in the following try block. We disconnect the document
         * provider in the finally block for this try block in order to avoid
         * a memory leak.
         */
        IFile teFile = getModel().getTraceExplorerTLAFile();
        FileEditorInput teFileEditorInput = new FileEditorInput((IFile) teFile);
		// Use LegacyFileDocumentProvider to fix race condition which causes Trace
		// Explorer Exploration to label the expression as __trace_var_XXXXXXXX instead
		// of the actual expression. The broken label is accompanied by an exception:
        // java.lang.IllegalArgumentException: Attempted to beginRule: F/DijkstraMutex/Model_1, 
        // does not match outer scope rule: org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate$MutexRule@1e6cad2d
        FileDocumentProvider teFileDocumentProvider = new LegacyFileDocumentProvider();
        try
        {

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
            TLCUIActivator.getDefault().logError("Error finding trace expression information in TE.tla file.", e);
        } catch (BadLocationException e)
        {
            TLCUIActivator.getDefault().logError("Error finding trace expression information in TE.tla file.", e);
        } finally
        {
            /*
             * The document provider is not needed. Always disconnect it to avoid a memory leak.
             * 
             * Keeping it connected only seems to provide synchronization of
             * the document with file changes. That is not necessary in this context.
             */
            teFileDocumentProvider.disconnect(teFileEditorInput);
        }
    }

    /**
     * Performs processing for the error and the error trace produced after a run of the trace explorer.
     * 
     * This method (and nested ones) does the following to a trace:
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

     * 6.) If the trace explorer ran successfully, this method changes several attributes
     * of the error trace produced by the trace explorer. It changes
     * the following three attributes:
     *  - error message
     *  - error code
     *  - cause
     * 
     * It sets these attributes equal to those attributes for
     * the error trace produced by the last run of model checking on
     * the model for which the trace explorer was run.
     * 
     * 7.) If the run of the trace explorer was successful, then we set the list
     * of errors for this data provider in the following way :
     * 
     *  - Copy the list of errors from the original run of TLC.
     *  - In the copied list, replace the original trace error with the new trace
     *    error created by the successful run of the trace explorer.
     */
    private void processTraceForTraceExplorer()
    {
        // retrieve the error with a trace for which the trace explorer was run
        final TLCError originalErrorWithTrace = TraceExplorerHelper.getErrorOfOriginalTrace(getModel());
        if (originalErrorWithTrace == null)
        {
            // the trace explorer is meaningless if the original trace cannot be recovered
            // all errors should be cleared
            getErrors().clear();
            return;
        }

        /*
         * The following will point to the error containing the trace for the
         * run of the trace explorer, iff the run of the trace explorer was successful.
         * The run was successful if TLC was able to evaluate the trace explorer
         * expressions at every possible state of the original trace.
         * 
         * The value of successfulTEError is set in the following while loop, if the
         * run was successful.
         */
        TLCError successfulTEError = null;

        final Map<String, Formula> traceExplorerExpressions = getModel().getNamedTraceExplorerExpressionsAsFormula();
  
        // iterate through the errors to find one with a trace
        Iterator<TLCError> it = getErrors().iterator();
        while (it.hasNext())
        {
            TLCError error = it.next();

            if (error.hasTrace())
            {
        		// Set the message, cause, and code of the error to the message of the original
        		// error for which the trace explorer was run if the new error
        		// message is for an invariant or property violation or deadlock. An invariant
        		// or property violation or deadlock indicates that the trace explorer ran
        		// successfully. This is item (6).
        		int errorCode = error.getErrorCode();
        		if (errorCode == EC.TLC_DEADLOCK_REACHED || errorCode == EC.TLC_TEMPORAL_PROPERTY_VIOLATED
        		        || errorCode == EC.TLC_INVARIANT_VIOLATED_BEHAVIOR
        		        || errorCode == EC.TLC_INVARIANT_VIOLATED_INITIAL)
        		{
        		    error.setErrorCode(originalErrorWithTrace.getErrorCode());
        		    error.setMessage(originalErrorWithTrace.getMessage());
        		    error.setCause(originalErrorWithTrace.getCause());

        		    successfulTEError = error;
        		} else
        		{
        		    error.setMessage(TE_ERROR_HEADER + error.getMessage());
        		}
        		
                error.applyFrom(originalErrorWithTrace, traceExplorerExpressions, traceExpressionDataTable,
						getModel().getName());

            } else
            {
                // error does not have trace
                // indicate that it is an error from the trace explorer
                error.setMessage(TE_ERROR_HEADER + error.getMessage());
            }
        }

        /*
         * The following accomplishes item 7 from the above documentation.
         */
        if (successfulTEError != null)
        {
            List<TLCError> originalErrors = TLCOutputSourceRegistry.getModelCheckSourceRegistry().getProvider(getModel())
                    .getErrors();
            List<TLCError> newErrors = new LinkedList<TLCError>();
            Iterator<TLCError> iterator = originalErrors.iterator();
            while (iterator.hasNext())
            {
                TLCError next = iterator.next();
                if (next == originalErrorWithTrace)
                {
                    newErrors.add(successfulTEError);
                } else
                {
                    newErrors.add(next);
                }
            }

            setErrors(newErrors);
        }

    }

    /**
     * Creates an error without any replacement of text from the error message reported by TLC.
     * 
     * This overrides the method in TLCModelLaunchDataProvider because that method does a lot
     * of work to search for Strings such as inv_2354234343434 in the error message and replace
     * them with the actual invariant from the MC.tla file. The user should never see anything from
     * the TE file, so this work is unnecessary for the trace explorer.
     * 
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
                    // set error text
                    topError.setMessage(message);
                    // set error code
                    topError.setErrorCode(tlcRegion.getMessageCode());
                }
            }
        }
        return topError;

    }

}
