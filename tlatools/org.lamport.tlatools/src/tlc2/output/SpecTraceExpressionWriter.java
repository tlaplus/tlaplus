package tlc2.output;

import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import tlc2.model.Assignment;
import tlc2.model.Formula;
import tlc2.model.MCState;
import tlc2.model.MCVariable;
import tlc2.model.TraceExpressionInformationHolder;
import tlc2.tool.impl.ModelConfig;
import util.TLAConstants;

/**
 * This is a reified class of spec writer which can produce specs capable of containing trace expressions; it is also
 * 	the parent class for a more specialized version used by the toolbox, {@code TraceExpressionModelWriter}.
 */
public class SpecTraceExpressionWriter extends AbstractSpecWriter {
	private static final String TRACE_EXPRESSION_VARIABLE = "TraceExp";
	private static final String TRI_INDENT = TLAConstants.INDENT + TLAConstants.INDENT + TLAConstants.INDENT;
	
	/**
	 * This will generate three identifiers equal to the initial and next state
	 * predicate for the trace, and the action constraint.
	 * 
	 * @param tlaBuffer the buffer into which the TLA code will be placed
	 * @param cfgBuffer if non-null, the buffer into which the CFG code will be placed
	 * @param trace
	 * @param expressionData data on trace explorer expressions, can be null
	 * @return String[], first element is the identifier for the initial state predicate,
	 * second element is the identifier for the next-state action, the third element is the identifier for
	 * the action contraint
	 * @see #addInitNextToBuffers(StringBuilder, StringBuilder, List, TraceExpressionInformationHolder[], String, String, String)
	 */
	public static String[] addInitNextToBuffers(final StringBuilder tlaBuffer, final StringBuilder cfgBuffer,
			final List<MCState> trace, final TraceExpressionInformationHolder[] expressionData) {
	    final String initId = SpecWriterUtilities.getValidIdentifier(TLAConstants.Schemes.INIT_SCHEME);
	    final String nextId = SpecWriterUtilities.getValidIdentifier(TLAConstants.Schemes.NEXT_SCHEME);
	    final String actionConstraintId = SpecWriterUtilities.getValidIdentifier(TLAConstants.Schemes.ACTIONCONSTRAINT_SCHEME);
	
	    addInitNextToBuffers(tlaBuffer, cfgBuffer, trace, expressionData, initId, nextId, actionConstraintId);
	
	    return new String[] { initId, nextId, actionConstraintId };
	}
	
	/**
	 * This calls:
	 * 	{@code addInitNextToBuffers(tlaBuffer, cfgBuffer, trace, expressionData, initId, nextId, actionConstraintId, TLAConstants.Schemes.NEXT_SCHEME, false);}
	 * 
	 * @param tlaBuffer the buffer into which the TLA code will be placed
	 * @param cfgBuffer if non-null, the buffer into which the CFG code will be placed
	 * @param trace
	 * @param expressionData data on trace explorer expressions, can be null
	 * @param initId the identifier to be used for the initial state predicate, cannot be null
	 * @param nextId the identifier to be used for the next-state action, cannot be null
	 * @param actionConstraintId the indentified used for the action constraint
	 * @see #addInitNextToBuffers(StringBuilder, StringBuilder, List, TraceExpressionInformationHolder[], String, String, String, String)
	 */
	public static void addInitNextToBuffers(final StringBuilder tlaBuffer, final StringBuilder cfgBuffer,
			final List<MCState> trace, final TraceExpressionInformationHolder[] expressionData, final String initId,
			final String nextId, final String actionConstraintId) {
		addInitNextToBuffers(tlaBuffer, cfgBuffer, trace, expressionData, initId, nextId, actionConstraintId,
							 TLAConstants.Schemes.NEXT_SCHEME, false);
	}

	/**
	 * This calls:
	 * 	{@code addInitNextToBuffers(cfgBuffer, trace, expressionData, initId, nextId, actionConstraintId, nextSubActionBasename, leaveStubsForTraceExpression);}
	 * and then concatenates the returned {@code StringBuilder} instances in order to tlaBuffer.
	 * 
	 * @param tlaBuffer the buffer into which the TLA code will be placed
	 * @param cfgBuffer if non-null, the buffer into which the CFG code will be placed
	 * @param trace
	 * @param expressionData data on trace explorer expressions, can be null
	 * @param initId the identifier to be used for the initial state predicate, cannot be null
	 * @param nextId the identifier to be used for the next-state action, cannot be null
	 * @param actionConstraintId the identifier used for the action constraint
	 * @param nextSubActionBasename the base string to be used as the prefix to unique names for next sub-actions
	 * @param leaveStubsForTraceExpression if true, then a variable will be defined {@link TRACE_EXPRESSION_VARIABLE},
	 * 						yet commented out, and similarly conjoined, but commented out in the SpecTE Init and Next
	 * 						declarations
	 */
	public static void addInitNextToBuffers(final StringBuilder tlaBuffer, final StringBuilder cfgBuffer,
			final List<MCState> trace, final TraceExpressionInformationHolder[] expressionData, final String initId,
			final String nextId, final String actionConstraintId, final String nextSubActionBasename,
			final boolean leaveStubsForTraceExpression) {
		final StringBuilder[] tlaBuffers = addInitNextToBuffers(cfgBuffer, trace, expressionData, initId, nextId,
				actionConstraintId, nextSubActionBasename, leaveStubsForTraceExpression);
		
		tlaBuffer.append(tlaBuffers[0].toString());
		tlaBuffer.append(tlaBuffers[1].toString());
	}

	/**
	 * This will set initId equal to the initial state predicate, nextId equal to the next state
	 * action for the trace, and actionConstraintId equal to the action constraint for the trace.
	 * If expressionData is not null, it should contain information about trace explorer expressions. This
	 * information is used to appropriately put the variables representing trace explorer expressions
	 * in the trace. In the following example, trace explorer expressions are used, but if expressionData
	 * is null, those variables will not appear in the init and next definitions, but everything else will be the same.
	 * 
	 * Note: In the following example, the expressions expr1,...,expr6, texpr1, texpr2 can take up multiple
	 * lines.
	 * 
	 * Consider the following trace:
	 * 
	 * <Initial predicate> <State num 1>
	 * var1=expr1
	 * var2=expr2
	 * 
	 * <Action...> <State num 2>
	 * var1=expr3
	 * var2=expr4
	 * 
	 * <Action...> <State num 3>
	 * var1=expr5
	 * var2=expr6
	 * 
	 * The user has defined two expressions in the trace explorer:
	 * 
	 * texpr1 (level 2 represented by var3)
	 * texpr2 (level 1 represented by var4)
	 * 
	 * This method defines the following identifiers:
	 * 
	 * init_4123123123 ==
	 * var1=(
	 * expr1
	 * )/\
	 * var2=(
	 * expr2
	 * )/\
	 * var3=(
	 * "--"
	 * )/\
	 * var4=(
	 * texpr2
	 * )
	 * 
	 * next_12312312312 ==
	 * (var1=(
	 * expr1
	 * )/\
	 * var2=(
	 * expr2
	 * )/\
	 * var1'=(
	 * expr3
	 * )/\
	 * var2'=(
	 * expr4
	 * )/\
	 * var3'=(
	 * texpr1
	 * )/\
	 * var4'=(
	 * texpr2
	 * )')
	 * \/
	 * (var1=(
	 * expr3
	 * )/\
	 * var2=(
	 * expr4
	 * )/\
	 * var1'=(
	 * expr5
	 * )/\
	 * var2'=(
	 * expr6
	 * )/\
	 * var3'=(
	 * texpr1
	 * )/\
	 * var4'=(
	 * texpr2
	 * )')
	 * 
	 * If the last state is back to state i, then this method treats
	 * the trace as if it has the state labeled "Back to state i" removed and
	 * replaced with a copy of state i.
	 * 
	 * If the last state is stuttering, then this method treats the trace as if it
	 * has the state labeled "Stuttering" removed and replaced with a copy
	 * of the state before the state labeled "Stuttering".
	 * 
	 * @param cfgBuffer if non-null, the buffer into which the CFG code will be placed
	 * @param trace
	 * @param expressionData data on trace explorer expressions, can be null
	 * @param initId the identifier to be used for the initial state predicate, cannot be null
	 * @param nextId the identifier to be used for the next-state action, cannot be null
	 * @param actionConstraintId the indentified used for the action constraint
	 * @param nextSubActionBasename the base string to be used as the prefix to unique names for next sub-actions
	 * @param leaveStubsForTraceExpression if true, then a variable will be defined {@link TRACE_EXPRESSION_VARIABLE},
	 * 						yet commented out, and similarly conjoined, but commented out in the SpecTE Init and Next
	 * 						declarations
	 * @return an array of length 2, the first element is a buffer containing all trace expression subaction
	 * 				declarations followed by the action constraint definition; the second element is a buffer
	 * 				containing a potential VARIABLE stub for the trace expression variable, followed by the
	 * 				definitions for Init and finally Next.
	 */
	public static StringBuilder[] addInitNextToBuffers(final StringBuilder cfgBuffer,
													   final List<MCState> trace,
													   final TraceExpressionInformationHolder[] expressionData,
													   final String initId, final String nextId,
													   final String actionConstraintId,
													   final String nextSubActionBasename,
													   final boolean leaveStubsForTraceExpression) {
		if (trace.size() > 0) {
	        final Iterator<MCState> it = trace.iterator();
	        MCState currentState = it.next();
	        final StringBuilder subActionsAndConstraint = new StringBuilder();
	        final StringBuilder initAndNext = new StringBuilder();
	
	        /*******************************************************
	         * Add the init definition.                            *
	         *******************************************************/
			if (cfgBuffer != null) {
				cfgBuffer.append(TLAConstants.CR);
				cfgBuffer.append(TLAConstants.CR).append(TLAConstants.KeyWords.INIT).append(TLAConstants.CR);
				cfgBuffer.append(initId).append(TLAConstants.CR);
			}
			
			if (leaveStubsForTraceExpression) {
				initAndNext.append(TLAConstants.COMMENT).append(TLAConstants.KeyWords.VARIABLE).append(' ');
				initAndNext.append(TRACE_EXPRESSION_VARIABLE).append(TLAConstants.CR).append(TLAConstants.CR);
			}
	
			initAndNext.append(TLAConstants.COMMENT).append("TRACE INIT definition ");
			initAndNext.append(TLAConstants.TraceExplore.TRACE_EXPLORE_INIT).append(TLAConstants.CR);
			initAndNext.append(initId).append(TLAConstants.DEFINES_CR);
	        final MCVariable[] vars = currentState.getVariables();
	
	        // variables from spec
			for (int i = 0; i < vars.length; i++) {
	            final MCVariable var = vars[i];
	            /*
	             *    /\ var = (
	             *            expr
	             *          )
	             */
	            initAndNext.append(TLAConstants.INDENTED_CONJUNCTIVE);
	            initAndNext.append(var.getName()).append(TLAConstants.EQ).append(TLAConstants.L_PAREN);
	            initAndNext.append(TLAConstants.CR);
	            
	            initAndNext.append(var.getValueAsStringReIndentedAs(TRI_INDENT)).append(TLAConstants.CR);
	            
	            initAndNext.append(TLAConstants.INDENT).append(TLAConstants.INDENT);
	            initAndNext.append(TLAConstants.R_PAREN).append(TLAConstants.CR);
	        }
	
	        // variables representing trace explorer expressions
			if (expressionData != null) {
				for (int i = 0; i < expressionData.length; i++) {
	                final TraceExpressionInformationHolder expressionInfo = expressionData[i];
	                initAndNext.append(TLAConstants.INDENTED_CONJUNCTIVE);
	                initAndNext.append(expressionInfo.getVariableName()).append(TLAConstants.EQ);
	                initAndNext.append(TLAConstants.L_PAREN).append(TLAConstants.CR);
	
	                initAndNext.append(TRI_INDENT);
					if (expressionInfo.getLevel() == 2) {
	                    // add "--" if the expression is temporal level
						initAndNext.append(TLAConstants.TRACE_NA);
					} else {
	                    // add the actual expression if it is not temporal level
						initAndNext.append(expressionInfo.getIdentifier());
	                }
	
					initAndNext.append(TLAConstants.CR).append(TLAConstants.INDENT).append(TLAConstants.INDENT);
		            initAndNext.append(TLAConstants.R_PAREN).append(TLAConstants.CR);
	            }
	        }
			
			if (leaveStubsForTraceExpression) {
				initAndNext.append(TLAConstants.COMMENT).append(TLAConstants.INDENTED_CONJUNCTIVE);
				initAndNext.append(TRACE_EXPRESSION_VARIABLE).append(TLAConstants.EQ);
				initAndNext.append(TLAConstants.KeyWords.TRUE).append(TLAConstants.CR);
			}
	
			initAndNext.append(CLOSING_SEP).append(TLAConstants.CR);
	
	        /**********************************************************
	         *  Now add the next state actions definition             *
	         **********************************************************/
			if (cfgBuffer != null) {
				cfgBuffer.append(TLAConstants.COMMENT).append(TLAConstants.KeyWords.NEXT).append(" definition");
				cfgBuffer.append(TLAConstants.CR).append(TLAConstants.KeyWords.NEXT).append(TLAConstants.CR);
				cfgBuffer.append(nextId).append(TLAConstants.CR);
			}
	
	        MCState nextState;
	        final boolean isSingleState;
			if (it.hasNext()) {
				nextState = it.next();
				isSingleState = false;
			} else {
	            nextState = currentState;
	            isSingleState = true;
	        }
	
	        /*
	         * MAK 09/25/2019: Previously, TE.tla was a next-state relation consisting of
	         * disjuncts of (unnamed) sub-actions:
	         * 
	         * Next_123 == (x=1 /\ x'=2) \/ (x=2 /\ x'=3) \/ ... \/ (x=42 /\ x'=42)
	         * 
	         * At runtime, TLC created an Action for each sub-action of the next-state
	         * relation (42 for the example above).
	         */
	        final StringBuilder nextDisjunctBuffer = new StringBuilder();
	        nextDisjunctBuffer.append(nextId).append(TLAConstants.DEFINES_CR);
	        final String firstIndent;
			if (leaveStubsForTraceExpression) {
				nextDisjunctBuffer.append(TLAConstants.TLA_AND).append(' ');
				firstIndent = " ";
			} else {
				firstIndent = TLAConstants.INDENT;
			}
	        
	        final StringBuilder actionConstraintBuffer = new StringBuilder();
	        actionConstraintBuffer.append(actionConstraintId).append(TLAConstants.DEFINES_CR);
	        actionConstraintBuffer.append(TLAConstants.BEGIN_TUPLE).append(TLAConstants.CR);
	
			if (cfgBuffer != null) {
				cfgBuffer.append(TLAConstants.COMMENT).append("Action Constraint definition").append(TLAConstants.CR);
				cfgBuffer.append(TLAConstants.COMMENT).append(TLAConstants.KeyWords.ACTION_CONSTRAINT).append(TLAConstants.CR);
				cfgBuffer.append(TLAConstants.COMMENT).append(actionConstraintId).append(TLAConstants.CR);
			}

	        int subActionIndex = 0;
			while (nextState != null) {
				final String nextDisjunct = String.format("%s_sa_%d", nextSubActionBasename, subActionIndex);
				nextDisjunctBuffer.append((subActionIndex == 0) ? firstIndent : TLAConstants.INDENT);
				nextDisjunctBuffer.append(TLAConstants.TLA_OR).append(' ').append(nextDisjunct).append(TLAConstants.CR);
		        actionConstraintBuffer.append(nextDisjunct);
		        	        	
		        subActionsAndConstraint.append(TLAConstants.COMMENT).append("TRACE Sub-Action definition ");
		        subActionsAndConstraint.append(subActionIndex++).append(TLAConstants.CR);
		        subActionsAndConstraint.append(nextDisjunct).append(TLAConstants.DEFINES_CR);
	            /*
	             * Handle Back to state and stuttering.
	             * 
	             * nextState is assigned to the state which the "Back to state"
	             * or "Stuttering" state represents. If nextState is "Back to state i",
	             * then it is assigned to state i. If nextState is "Stuttering", then
	             * it is assigned to the current state.
	             */
				if (nextState.isBackToState()) {
					nextState = trace.get(nextState.getStateNumber() - 1);
				} else if (nextState.isStuttering()) {
					nextState = currentState;
				}
	
	            /*
	             * Write the action:
	             * 
	             * (/\ var1=(
	             * expr1
	             * )
	             * /\ var2=(
	             * expr2
	             * )
	             * /\ var1'=(
	             * expr3
	             * )
	             * /\ var2'=(
	             * expr4
	             * ))
	             */
				subActionsAndConstraint.append(TLAConstants.INDENT).append(TLAConstants.L_PAREN).append(TLAConstants.CR);
	
	            final MCVariable[] currentStateVars = currentState.getVariables();
	            final MCVariable[] nextStateVars = nextState.getVariables();
	
	            /*
	             * Iterate through current state variables. This adds:
	             * 
	             * /\ var1=(
	             * expr1
	             * )
	             * /\ var2=(
	             * expr2
	             * )
	             * 
	             */
				for (int i = 0; i < currentStateVars.length; i++) {
					final MCVariable currentStateVar = currentStateVars[i];
					subActionsAndConstraint.append(TLAConstants.INDENT).append(TLAConstants.INDENTED_CONJUNCTIVE);
					subActionsAndConstraint.append(currentStateVar.getName()).append(TLAConstants.EQ);
					subActionsAndConstraint.append(TLAConstants.L_PAREN).append(TLAConstants.CR);
					subActionsAndConstraint.append(currentStateVar.getValueAsStringReIndentedAs(TRI_INDENT + TLAConstants.INDENT));
					subActionsAndConstraint.append(TLAConstants.CR);
					subActionsAndConstraint.append(TRI_INDENT).append(TLAConstants.R_PAREN).append(TLAConstants.CR);
	            }
	
	            /*
	             * If the trace is a single state, make the next state
	             * action never enabled. The model will deadlock in the initial state.
	             * This adds:
	             * 
	             * /\ FALSE
	             */
				if (isSingleState) {
					subActionsAndConstraint.append(TLAConstants.INDENT).append(TLAConstants.INDENTED_CONJUNCTIVE);
					subActionsAndConstraint.append("FALSE").append(TLAConstants.CR);
	            }
	
	            /*
	             * Iterate through next state variables. This adds:
	             * 
	             * /\ var1'=(
	             * expr3
	             * )
	             * /\ var2'=(
	             * expr4
	             * )
	             */
				for (int i = 0; i < currentStateVars.length; i++) {
	                final MCVariable nextStateVar = nextStateVars[i];
	                subActionsAndConstraint.append(TLAConstants.INDENT).append(TLAConstants.INDENTED_CONJUNCTIVE);
	                subActionsAndConstraint.append(nextStateVar.getName()).append(TLAConstants.PRIME);
	                subActionsAndConstraint.append(TLAConstants.EQ).append(TLAConstants.L_PAREN).append(TLAConstants.CR);
					subActionsAndConstraint.append(nextStateVar.getValueAsStringReIndentedAs(TRI_INDENT + TLAConstants.INDENT));
					subActionsAndConstraint.append(TLAConstants.CR);
					subActionsAndConstraint.append(TRI_INDENT).append(TLAConstants.R_PAREN).append(TLAConstants.CR);
	            }
	
	            /*
	             * Iterate through the trace explorer expressions if there are any. This adds:
	             * 
	             * /\ var3'=(
	             * texpr1
	             * )
	             * /\ var4'=(
	             * texpr2
	             * )'
	             * 
	             */
				if (expressionData != null) {
					for (int i = 0; i < expressionData.length; i++) {
	                    final TraceExpressionInformationHolder expressionInfo = expressionData[i];
		                subActionsAndConstraint.append(TLAConstants.INDENT).append(TLAConstants.INDENTED_CONJUNCTIVE);
	                    subActionsAndConstraint.append(expressionInfo.getVariableName()).append(TLAConstants.PRIME);
	                    subActionsAndConstraint.append(TLAConstants.EQ).append(TLAConstants.L_PAREN).append(TLAConstants.CR);
	                    subActionsAndConstraint.append(TRI_INDENT);
	                    subActionsAndConstraint.append(expressionInfo.getIdentifier()).append(TLAConstants.CR);
	                    subActionsAndConstraint.append(TRI_INDENT).append(TLAConstants.R_PAREN);
	
						if (expressionInfo.getLevel() < 2) {
							subActionsAndConstraint.append(TLAConstants.PRIME);
	                    }
						subActionsAndConstraint.append(TLAConstants.CR);
	                }
	            }
	
				subActionsAndConstraint.append(TLAConstants.INDENT).append(TLAConstants.R_PAREN);
				subActionsAndConstraint.append(TLAConstants.CR).append(TLAConstants.CR);
	
				if (it.hasNext()) {
	                actionConstraintBuffer.append(TLAConstants.COMMA);
	            }
				actionConstraintBuffer.append(TLAConstants.CR);
	
	            currentState = nextState;
	
				if (it.hasNext()) {
					nextState = it.next();
				} else {
					nextState = null;
				}
	        }
	
	        initAndNext.append(TLAConstants.COMMENT).append("TRACE NEXT definition ");
	        initAndNext.append(TLAConstants.TraceExplore.TRACE_EXPLORE_NEXT).append(TLAConstants.CR);
	        initAndNext.append(nextDisjunctBuffer.toString());
			
			if (leaveStubsForTraceExpression) {
				initAndNext.append(TLAConstants.COMMENT).append(TLAConstants.TLA_AND).append(' ');
				initAndNext.append(TRACE_EXPRESSION_VARIABLE).append(TLAConstants.PRIME).append(TLAConstants.EQ);
				initAndNext.append(TRACE_EXPRESSION_VARIABLE).append(TLAConstants.CR);
			}
	        
			initAndNext.append(TLAConstants.CR).append(TLAConstants.CR);
	        
			
			/**
			 * Action Constraint
			 */
			subActionsAndConstraint.append(TLAConstants.COMMENT).append("TRACE Action Constraint definition ");
			subActionsAndConstraint.append(TLAConstants.TraceExplore.TRACE_EXPLORE_ACTION_CONSTRAINT);
			subActionsAndConstraint.append(TLAConstants.CR).append(actionConstraintBuffer.toString());
			subActionsAndConstraint.append(TLAConstants.END_TUPLE).append("[TLCGet(\"level\")]");

			subActionsAndConstraint.append(CLOSING_SEP).append(TLAConstants.CR);

			
	        return new StringBuilder[] { subActionsAndConstraint, initAndNext };
	    }
		
		return new StringBuilder[] { new StringBuilder(), new StringBuilder() };
	}

	public static String addTraceFunctionToBuffers(final StringBuilder tlaBuffer, final StringBuilder cfgBuffer,
			final List<MCState> input, final String id, final String configId) {
		// Filter stuttering or back2state instances from trace.
		final List<MCState> trace = input.stream()
				.filter(state -> !state.isBackToState() && !state.isStuttering())
				.collect(Collectors.toList());
		
		if (trace.isEmpty()) {
			return addArrowAssignmentIdToBuffers(tlaBuffer, cfgBuffer,
					new Assignment(TLAConstants.TraceExplore.TRACE, new String[0], TLAConstants.BEGIN_TUPLE + TLAConstants.END_TUPLE),
					id, configId);
	    }
		
		// Trace
		final StringBuilder traceFunctionDef = new StringBuilder();
		traceFunctionDef.append(TLAConstants.INDENT).append(TLAConstants.BEGIN_TUPLE).append(TLAConstants.CR);
		for (int j = 0; j < trace.size(); j++) {
			final MCState state = trace.get(j);

			traceFunctionDef.append(TLAConstants.INDENT).append(TLAConstants.L_PAREN).append(state.asSimpleRecord()).append(TLAConstants.R_PAREN);

			if (j < trace.size() - 1) {
				traceFunctionDef.append(TLAConstants.COMMA).append(TLAConstants.CR);
			}
		}
		traceFunctionDef.append(TLAConstants.CR).append(TLAConstants.INDENT).append(TLAConstants.END_TUPLE);
		traceFunctionDef.append(CLOSING_SEP).append(TLAConstants.CR);
		
		return addArrowAssignmentIdToBuffers(tlaBuffer, cfgBuffer,
				new Assignment(TLAConstants.TraceExplore.TRACE, new String[0], traceFunctionDef.toString()),
				id, configId);
	}
	
	
	public SpecTraceExpressionWriter() {
		super(true);
	}
	
	/**
	 * This only changes the tla file. This method generates and adds a variable declaration
	 * for each expression in the list. It also creates an identifier for each
	 * expression and defines the identifier to be that expression.
	 * It returns an array of {@link TraceExpressionInformationHolder} where each element
	 * contains the expression, the identifier, and the variable name.
	 * 
	 * If the expressions are x' + y and x > 3, The tla file will contain something like
	 * 
	 *\* comment line
	 * VARIABLES __trace_var_21034978347834, __trace_var_90234782309
	 * 
	 * \* comment line
	 * trace_def_3214234234234 ==
	 * x' + y
	 * ----
	 * 
	 * \* comment line
	 * trace_def_2342342342342 ==
	 * x > 3
	 * ----
	 * 
	 * @param expressions a list of formulas, each one an expression the user wants to have evaluated
	 * at each state of the trace
	 * @return array of {@link TraceExpressionInformationHolder} where each element
	 * contains the expression, the identifier, and the variable name
	 */
	public TraceExpressionInformationHolder[] createAndAddVariablesAndDefinitions(final List<Formula> expressions,
			final String attributeName) {
		final TraceExpressionInformationHolder[] expressionData
								= TraceExpressionInformationHolder.createHolders(expressions, attributeName);
	
	    addVariablesAndDefinitions(expressionData, attributeName, true);
	
	    return expressionData;
	}
	
	@Override
	public void addPrimer(final String moduleFilename, final String extendedModuleName) {
		addPrimer(moduleFilename, extendedModuleName, new HashSet<>());
	}

	/**
	 * Adds MODULE and EXTENDS statements.
	 */
	public void addPrimer(
			final String moduleFilename,
			final String extendedModuleName,
			final Set<String> extraExtendedModules) {
		if (extendedModuleName != null) {
			extraExtendedModules.add(extendedModuleName);
		}
		
		tlaBuffer.append(SpecWriterUtilities.getExtendingModuleContent(moduleFilename,
				extraExtendedModules.toArray(new String[extraExtendedModules.size()])));
	}
	
	/**
	 * Adds the trace expression stub to the TE spec.
	 * This is an alias function which applies the identity transformation
	 * to the spec's variables, with some comments explaining how to add
	 * additional transformations for custom trace expressions.
	 * @param moduleName Name of original module.
	 * @param teName Name of trace expression.
	 * @param variables Spec variables; transformed by identity.
	 */
	public void addTraceExpressionStub(String moduleName, String teName, final List<String> variables) {
		this.tlaBuffer.append(teName + TLAConstants.DEFINES + TLAConstants.CR);
		this.tlaBuffer
				.append(TLAConstants.INDENT + TLAConstants.L_SQUARE_BRACKET + TLAConstants.CR);

		// Create local string build for expression and comments so we can indent everything together in the end.
		StringBuilder localBuffer = new StringBuilder();

		localBuffer.append(TLAConstants.COMMENT).append(String.format("To hide variables of the `%s` spec from the error trace,", moduleName)).append(TLAConstants.CR);
		localBuffer.append(TLAConstants.COMMENT).append("remove the variables below.  The trace will be written in the order").append(TLAConstants.CR);
		localBuffer.append(TLAConstants.COMMENT).append("of the fields of this record.").append(TLAConstants.CR);
		
		localBuffer.append(
				variables.stream().map(var -> var + TLAConstants.RECORD_ARROW + var).collect(Collectors
						.joining(TLAConstants.CR + TLAConstants.COMMA))).append(TLAConstants.CR).append(TLAConstants.CR);	
						
		localBuffer.append(TLAConstants.COMMENT).append("Put additional constant-, state-, and action-level expressions here:").append(TLAConstants.CR);
		localBuffer.append(TLAConstants.COMMENT).append(",_stateNumber |-> _TEPosition").append(TLAConstants.CR);
		
		if (variables.size() > 0) {
			// Check that exists at least one variable so we can use
			// in the commented trace expressions.
			String someVar = variables.get(0);
			
			localBuffer.append(TLAConstants.COMMENT).append(String.format(",_%sUnchanged |-> %s = %s'", someVar, someVar, someVar)).append(TLAConstants.CR).append(TLAConstants.CR);
			localBuffer.append(TLAConstants.COMMENT).append(String.format("Format the `%s` variable as Json value.", someVar)).append(TLAConstants.CR);
			localBuffer.append(TLAConstants.COMMENT).append(String.format(",_%sJson |->", someVar)).append(TLAConstants.CR);
			localBuffer.append(TLAConstants.COMMENT + TLAConstants.INDENT).append("LET J == INSTANCE Json").append(TLAConstants.CR);
			localBuffer.append(TLAConstants.COMMENT + TLAConstants.INDENT).append(String.format("IN J!ToJson(%s)", someVar))
				.append(TLAConstants.CR).append(TLAConstants.CR);
			
			localBuffer.append(TLAConstants.COMMENT).append("Lastly, you may build expressions over arbitrary sets of states by").append(TLAConstants.CR);
			localBuffer.append(TLAConstants.COMMENT).append("leveraging the _TETrace operator.  For example, this is how to").append(TLAConstants.CR);
			localBuffer.append(TLAConstants.COMMENT).append("count the number of times a spec variable changed up to the current").append(TLAConstants.CR);
			localBuffer.append(TLAConstants.COMMENT).append("state in the trace.").append(TLAConstants.CR);
			localBuffer.append(TLAConstants.COMMENT).append(String.format(",_%sModCount |->", someVar)).append(TLAConstants.CR);
			localBuffer.append(TLAConstants.COMMENT + TLAConstants.INDENT).append("LET F[s \\in DOMAIN _TETrace] ==").append(TLAConstants.CR);
			localBuffer.append(TLAConstants.COMMENT + TLAConstants.INDENT + TLAConstants.INDENT).append("IF s = 1 THEN 0").append(TLAConstants.CR);
			localBuffer.append(TLAConstants.COMMENT + TLAConstants.INDENT + TLAConstants.INDENT)
				.append(String.format("ELSE IF _TETrace[s].%s # _TETrace[s-1].%s", someVar, someVar)).append(TLAConstants.CR);
			localBuffer.append(TLAConstants.COMMENT + TLAConstants.INDENT + TLAConstants.INDENT + TLAConstants.INDENT)
				.append("THEN 1 + F[s-1] ELSE F[s-1]").append(TLAConstants.CR);
			localBuffer.append(TLAConstants.COMMENT + TLAConstants.INDENT).append("IN F[_TEPosition - 1]").append(TLAConstants.CR);		
		}
		
		this.tlaBuffer.append(indentString(localBuffer.toString(), 2));
		this.tlaBuffer.append(TLAConstants.CR + TLAConstants.INDENT + TLAConstants.R_SQUARE_BRACKET + TLAConstants.CR + TLAConstants.CR);		
	}

	public void addViewConfig(final String view) {
		cfgBuffer.append(TLAConstants.CR).append(TLAConstants.KeyWords.VIEW).append(TLAConstants.CR);
		cfgBuffer.append(TLAConstants.INDENT).append(view).append(TLAConstants.CR);
	}
	
	public void addView(String vars) {
		addViewConfig(TLAConstants.TraceExplore.VIEW);
		
		tlaBuffer.append(TLAConstants.CR).append(TLAConstants.TraceExplore.VIEW).append(TLAConstants.DEFINES_CR);
		tlaBuffer.append(TLAConstants.INDENT).append(TLAConstants.BEGIN_TUPLE)
				.append(vars + ", IF TLCGet(\"level\") = " + TLAConstants.TraceExplore.SPEC_TETRACE_LASSO_END
						+ " + 1 THEN " + TLAConstants.TraceExplore.SPEC_TETRACE_LASSO_START + " ELSE TLCGet(\"level\")")
				.append(TLAConstants.END_TUPLE);
		tlaBuffer.append(TLAConstants.CR);
	}

	public void addFooter() {
		tlaBuffer.append(getTLAModuleClosingTag());
	}
	
	/**
	 * This only changes the tla file. This method adds a variable declaration
	 * for each element of traceExpressionData and, if the flag addDefinitions is true,
	 * defines the identifier of each element to be the expression for that element.
	 * 
	 * If the expressions are x' + y and x > 3, The tla file will contain something like
	 * 
	 *\* comment line
	 * VARIABLES __trace_var_21034978347834, __trace_var_90234782309
	 * 
	 * \* comment line
	 * trace_def_3214234234234 ==
	 * x' + y
	 * ----
	 * 
	 * \* comment line
	 * trace_def_2342342342342 ==
	 * x > 3
	 * ----
	 * 
	 * @param traceExpressionData information about the trace expressions
	 * @param attributeName
	 * @param addDefinitions whether or not to define each identifier as the expression
	 */
	public void addVariablesAndDefinitions(final TraceExpressionInformationHolder[] traceExpressionData, final String attributeName,
			final boolean addDefinitions) {
		if (traceExpressionData.length == 0) {
	        return;
	    }
	
	    final StringBuilder variableDecls = new StringBuilder();
	    final StringBuilder definitions = new StringBuilder();
		for (int i = 0; i < traceExpressionData.length; i++) {
	        final TraceExpressionInformationHolder expressionInfo = traceExpressionData[i];
	
	        variableDecls.append(expressionInfo.getVariableName());
	        // we add a comma after every variable except for the last
	        if (i != traceExpressionData.length - 1)
	        {
	            variableDecls.append(TLAConstants.COMMA);
	        }
	
	        if (addDefinitions)
	        {
	            // define the identifier corresponding to this expression - looks like:
	            // \* comment line
	            // trace_def_213123123123 ==
	            // expression
	            // ----
	            definitions.append(TLAConstants.COMMENT).append("TRACE EXPLORER identifier definition ");
	            definitions.append(TLAConstants.ATTRIBUTE).append(attributeName).append(TLAConstants.COLON);
	            definitions.append(i).append(TLAConstants.CR);
	            definitions.append(expressionInfo.getIdentifier()).append(TLAConstants.DEFINES_CR);
	            definitions.append(expressionInfo.getExpression()).append(CLOSING_SEP).append(TLAConstants.CR);
	        }
	    }
	
	    // variable declaration
	    tlaBuffer.append(TLAConstants.COMMENT).append("TRACE EXPLORER variable declaration ");
	    tlaBuffer.append(TLAConstants.ATTRIBUTE).append(attributeName).append(TLAConstants.CR);
	    tlaBuffer.append("VARIABLES ").append(variableDecls.toString()).append(CLOSING_SEP).append(TLAConstants.CR);
	
		if (addDefinitions) {
	        // append the expression definitions
	        tlaBuffer.append(definitions.toString());
	    }
	}

	/**
	 * Adds the invariant ~(P) where P is the formula describing finalState. The format
	 * in the tla file is as follows:
	 * 
	 * _inv ==
	 * ~(
	 * P
	 * )
	 * ----
	 * 
	 * @param finalState
	 */
	private void addInvariant(final MCState finalState) {
	    final String id = SpecWriterUtilities.getValidIdentifierNoTimestamp(TLAConstants.Schemes.INVARIANT_SCHEME);
	    cfgBuffer.append(TLAConstants.CR).append(TLAConstants.KeyWords.INVARIANT).append(TLAConstants.CR);
	    cfgBuffer.append(TLAConstants.INDENT).append(id).append(TLAConstants.CR);
	
	    tlaBuffer.append(TLAConstants.CR).append(id).append(TLAConstants.DEFINES_CR);
	    tlaBuffer.append(TLAConstants.INDENT).append(TLAConstants.TLA_NOT).append(TLAConstants.L_PAREN).append(TLAConstants.CR);
	    
		// The main reason why we generate an invariant compared to the much simpler
		// deadlock checking is noted in addProperties below (thank you simulation mode).
		// Another reason is that we want to allow users to be able to amend the te
		// spec to check the original Init/Next or Spec in place of the generated
		// _init/_next (to a) quickly check if a spec change addresses the error causing
		// the error trace, and b) print the original action names). With this variant
	    // of the te spec, there might no longer be a deadlock (Worker.java doesn't report
	    // deadlocks if states are excluded from the model due to action- and
	    // state-constraints).
	    //
		// A less important side-effect of checking _inv -formulated as ~(SomeState)- is
		// that it brings the variable values in the canonical order defined by the
		// original invariant. Let  x # [ b |-> 42, a |-> 23 ]  be the invariant in the
	    // original spec.  With deadlock checking, the error trace might report the 
	    // value in the opposite order:  x = [ a |-> 23, b |-> 42 ].
	    // 
	    // An undesired side-effect of checking _inv are occasional silly expressions that
	    // some might call type mismatches. For example, let the value of the x variable
	    // above in first state of an error trace be a special "NULL" value and 
	    // [ b |-> 1, a |-> 2 ] in the other states leading up to the error state. 
	    // Checking the generated _inv on the initial state would cause TLC to fail with
	    // the evaluation error stemming from the silly expression
	    // "NULL" # [ b |-> 42, a |-> 23 ].  Thus, we conjoin  TLCGet("level") # Len(_TETrace)
	    // to  SomeState  to prevent evaluating silly expressions.  On the upside, this
	    // asserts the correct error trace should the previously described spec variant
	    // with the original Init/Next be checked; a trace could be too short if a state
	    // exluded by the action-constraint violated  SomeState.
		tlaBuffer.append(getStateConjunction(finalState, "TLCGet(\"level\") = Len(_TETrace)")).append(TLAConstants.CR);
		tlaBuffer.append(TLAConstants.INDENT).append(TLAConstants.R_PAREN);
	}

	public void addProperties(final List<MCState> trace) {
		addProperties(trace, null);
	}

	public void addProperties(final List<MCState> trace, String specName) {
        MCState finalState = trace.get(trace.size() - 1);
        boolean isBackToState = finalState.isBackToState();
        boolean isStuttering = finalState.isStuttering();

        // add temporal property or invariant depending on type of trace
        // read the method comments to see the form of the invariant or property
        if (isStuttering)
        {
            addStutteringProperty(trace.get(trace.size() - 2));
        } else if (isBackToState)
        {
            addBackToStateProperty(trace.get(trace.size() - 2), trace.get(finalState.getStateNumber() - 1));
        } else
        {
            // checking deadlock eliminates the need for the following
			// MAK 06/26/2020: write.addInvariant(finalState) below used to be commented
			// with the comment above about deadlock checking taking care of it. The
			// statement is wrong when an error-trace is not the shortest possible trace,
			// because bfs (run with TE) on such a trace might a) shorten it and b) no
			// longer deadlocks. This is possible with traces that come out of TLC's
			// simulation mode.
			// Assume any spec and an invariant such as TLCGet("level") < n for some n \in Nat
        	// (larger n increase the probability of a behavior with a sequence of stuttering
        	// steps). If the simulator happens to generate a behavior with a sequence of
			// stuttering step, the generated TE.tla will define a behavior that allows infinite
			// stuttering (for each stuttering step, there will be a disjunct in the disjuncts
			// of the next-state relation), which is not a deadlock. We could require the
        	// simulator to run with the "-difftrace" command-line parameter, which will remove
        	// successive stuttering steps.  However, it seems like an unnecessary requirement
        	// given that checking an invariant instead of deadlock has no drawback.
			// I ran into this issue when I used the simulator to generate very long traces
			// (1000+) for a spec (AsyncGameOfLife.tla) that models an Asynchronous Cellular
			// Automaton (https://uhra.herts.ac.uk/bitstream/handle/2299/7041/102007.pdf),
			// to use as input for Will Schultz's animation module (result at
			// https://github.com/lemmy/tlaplus_specs/blob/master/AsyncGameOfLifeAnimBlinker.mp4).
            addInvariant(finalState);
        }

		tlaBuffer.append(CLOSING_SEP).append(TLAConstants.CR);
        
		// Do not require to pass -deadlock on the command-line (properties assert that
		// TLC re-finds the error-trace).		
		cfgBuffer.append(TLAConstants.CR).append(ModelConfig.CheckDeadlock).append(TLAConstants.CR);
		cfgBuffer.append(TLAConstants.INDENT + TLAConstants.COMMENT).append(ModelConfig.CheckDeadlock).append(" off because of PROPERTY or INVARIANT above.")
				.append(TLAConstants.CR);
		cfgBuffer.append(TLAConstants.INDENT).append(TLAConstants.FALSE);
	}

	/**
	 * Adds the temporal property ~<>[](P) where P is the formula describing finalState.
	 * The format in the tla file is as follows:
	 * 
	 * _prop ==
	 * ~<>[](
	 * P
	 * )
	 * ----
	 * 
	 * @param finalState
	 */
	private void addStutteringProperty(final MCState finalState) {
	    String id = SpecWriterUtilities.getValidIdentifierNoTimestamp(TLAConstants.Schemes.PROP_SCHEME);
	    cfgBuffer.append(TLAConstants.CR).append(TLAConstants.KeyWords.PROPERTY).append(TLAConstants.CR);
	    cfgBuffer.append(TLAConstants.INDENT).append(id).append(TLAConstants.CR);
	
	    tlaBuffer.append(TLAConstants.CR).append(id).append(TLAConstants.DEFINES_CR);
	    tlaBuffer.append(TLAConstants.INDENT + TLAConstants.TLA_NOT).append(TLAConstants.TLA_EVENTUALLY_ALWAYS);
	    tlaBuffer.append(TLAConstants.L_PAREN).append(TLAConstants.CR).append(getStateConjunction(finalState));
	    tlaBuffer.append(TLAConstants.CR).append(TLAConstants.INDENT + TLAConstants.R_PAREN);
	}

	/**
	 * Adds the temporal property ~([]<>P /\ []<>Q), where P is the formula describing finalState and 
	 * Q the formula describing backToState. The formatting in the tla file is as follows:
	 * 
	 * _prop ==
	 * ~(([]<>(
	 * P
	 * ))/\([]<>(
	 * Q
	 * )))
	 * ----
	 * 
	 * @param finalState
	 * @param backToState
	 */
	private void addBackToStateProperty(final MCState finalState, final MCState backToState) {
	    final String id = SpecWriterUtilities.getValidIdentifierNoTimestamp(TLAConstants.Schemes.PROP_SCHEME);
	    cfgBuffer.append(TLAConstants.CR).append(TLAConstants.KeyWords.PROPERTY).append(TLAConstants.CR);
	    cfgBuffer.append(TLAConstants.INDENT).append(id).append(TLAConstants.CR);
	    
		tlaBuffer.append(TLAConstants.CR).append(id).append(TLAConstants.DEFINES_CR);

		StringBuilder localBuffer = new StringBuilder();
	    localBuffer.append(TLAConstants.TLA_NOT).append(TLAConstants.L_PAREN).append(TLAConstants.L_PAREN);
	    localBuffer.append(TLAConstants.TLA_INF_OFTEN).append(TLAConstants.L_PAREN).append(TLAConstants.CR);
	    localBuffer.append(getStateConjunction(finalState)).append(TLAConstants.CR).append(TLAConstants.R_PAREN);
	    localBuffer.append(TLAConstants.R_PAREN).append(TLAConstants.TLA_AND).append(TLAConstants.L_PAREN);
	    localBuffer.append(TLAConstants.TLA_INF_OFTEN).append(TLAConstants.L_PAREN).append(TLAConstants.CR);
	    localBuffer.append(getStateConjunction(backToState)).append(TLAConstants.CR).append(TLAConstants.R_PAREN);
	    localBuffer.append(TLAConstants.R_PAREN).append(TLAConstants.R_PAREN);

		// Writes local buffer back to tla buffer with some iation.
		tlaBuffer.append(indentString(localBuffer.toString(), 1));
	}

	/**
	 * Writes comments that will be used for associating variable names with expressions
	 * and will give the level of each expression. In particular, for each expression "expr"
	 * with level x and variable name ___trace_var_3242348934343 this
	 * will append the following comment to the tla file:
	 * 
	 * \* :x:___trace_var_3242348934343:expr"$!@$!@$!@$!@$!"
	 * 
	 * @param traceExpressionData
	 */
	public void addInfoComments(final TraceExpressionInformationHolder[] traceExpressionData) {
		for (final TraceExpressionInformationHolder expressionData : traceExpressionData) {
	        tlaBuffer.append(TLAConstants.COMMENT).append(TLAConstants.COLON).append(expressionData.getLevel());
	        tlaBuffer.append(TLAConstants.COLON).append(expressionData.getVariableName()).append(TLAConstants.COLON);
	        tlaBuffer.append(expressionData.getExpression()).append(TLAConstants.CONSTANT_EXPRESSION_EVAL_IDENTIFIER);
	        tlaBuffer.append(TLAConstants.CR);
	    }
	}

	/**
	 * @see #addInitNextToBuffers(StringBuilder, StringBuilder, List, TraceExpressionInformationHolder[])
	 */
	public String[] addInitNext(final List<MCState> trace) {
		return addInitNextToBuffers(tlaBuffer, cfgBuffer, trace, null);
	}

	/**
	 * @see #addInitNextToBuffers(StringBuilder, StringBuilder, List, TraceExpressionInformationHolder[], String, String, String)
	 */
	public void addInitNext(final List<MCState> trace, final TraceExpressionInformationHolder[] expressionData,
							final String initId, String nextId, final String actionConstraintId) {
		addInitNextToBuffers(tlaBuffer, cfgBuffer, trace, expressionData, initId, nextId, actionConstraintId);
	}

	/**
	 * @see #addInitNextToBuffers(StringBuilder, StringBuilder, List, TraceExpressionInformationHolder[], String, String, String, String, boolean)
	 */
	public void addInitNext(final List<MCState> trace, final TraceExpressionInformationHolder[] expressionData,
							final String initId, String nextId, final String actionConstraintId,
							final String nextSubActionBasename) {
		addInitNextToBuffers(tlaBuffer, cfgBuffer, trace, expressionData, initId, nextId, actionConstraintId,
							 nextSubActionBasename, true);
	}
	
	public void addInitNext(final List<MCState> trace, final String initId, String nextId,
			final String actionConstraintId, final String nextSubActionBasename) {
		addInitNext(trace, null, initId, nextId, actionConstraintId, nextSubActionBasename);
	}

	public void addInitNextTraceFunction(final List<MCState> trace, final String teSpecModuleName, final List<String> vars, ModelConfig modelConfig) {
		/*******************************************************
         * Add the init definition.                            *
         *******************************************************/
		if (cfgBuffer != null) {
			cfgBuffer.append(TLAConstants.CR);
			cfgBuffer.append(TLAConstants.CR).append(TLAConstants.KeyWords.INIT).append(TLAConstants.CR);
			cfgBuffer.append(TLAConstants.INDENT).append(TLAConstants.TraceExplore.SPEC_TE_INIT).append(TLAConstants.CR);
		}

		tlaBuffer.append(TLAConstants.TraceExplore.SPEC_TE_INIT).append(TLAConstants.DEFINES_CR);
		
        // variables from spec
		for (String var : vars) {
            tlaBuffer.append(TLAConstants.INDENTED_CONJUNCTIVE);
            tlaBuffer.append(var).append(TLAConstants.EQ).append("_TETrace[1].").append(var);
            tlaBuffer.append(TLAConstants.CR);
        }
		
		tlaBuffer.append(TLAConstants.SEP).append(TLAConstants.CR).append(TLAConstants.CR);

		// Get final state so we can check if this trace is for a safety
		// or liveness property.
		final MCState finalState = trace.get(trace.size() - 1);		
				
		final String nextId = TLAConstants.TraceExplore.SPEC_TE_NEXT;

        /************************************************
         *  Now add the next state relation             *
         ************************************************/
		if (cfgBuffer != null) {	
			cfgBuffer.append(TLAConstants.CR).append(TLAConstants.KeyWords.NEXT).append(TLAConstants.CR);
			cfgBuffer.append(TLAConstants.INDENT).append(nextId).append(TLAConstants.CR);
		}		
		
		// _next ==
		tlaBuffer.append(nextId).append(TLAConstants.DEFINES_CR);

		if (trace.size() == 1) {
			tlaBuffer.append(TLAConstants.INDENT).append(TLAConstants.INDENTED_CONJUNCTIVE);
			tlaBuffer.append(TLAConstants.FALSE).append(TLAConstants.CR);
		} else {
			tlaBuffer.append(TLAConstants.INDENTED_CONJUNCTIVE).append("\\E i,j \\in DOMAIN _TETrace:")
					.append(TLAConstants.CR);
			tlaBuffer.append(TLAConstants.INDENT).append(TLAConstants.INDENTED_CONJUNCTIVE).append(TLAConstants.TLA_OR)
					.append(TLAConstants.SPACE).append(TLAConstants.TLA_AND).append(" j = i + 1")
					.append(TLAConstants.CR);
			tlaBuffer.append(TLAConstants.INDENT).append(TLAConstants.INDENT).append(TLAConstants.SPACE)
					.append(TLAConstants.SPACE).append(TLAConstants.INDENTED_CONJUNCTIVE)
					.append("i = TLCGet(\"level\")").append(TLAConstants.CR);
			// Back to state?
			if (finalState.isBackToState()) {
				// Instead of this disjunct, we could append backToState to the trace function
				// (_TETrace). Len(_TETrace) would however be off by one.
				tlaBuffer.append(TLAConstants.INDENT).append(TLAConstants.INDENT).append("   ")
						.append(TLAConstants.TLA_OR).append(TLAConstants.SPACE).append(TLAConstants.TLA_AND)						
						// `_TTraceLassoEnd` is a constant which contains the last state of the lasso.
						.append(" i = ").append(TLAConstants.TraceExplore.SPEC_TETRACE_LASSO_END).append(TLAConstants.CR);
				tlaBuffer.append(TLAConstants.INDENT).append(TLAConstants.INDENT).append("  ")
						// `_TTraceLassoStart` is a constant which contains the first state of the lasso.
						.append(TLAConstants.INDENTED_CONJUNCTIVE).append("j = ").append(TLAConstants.TraceExplore.SPEC_TETRACE_LASSO_START)
						.append(TLAConstants.CR);
			}
			for (String var : vars) {
	            // x = _TETrace[_TEPosition].x
				tlaBuffer.append(TLAConstants.INDENT).append(TLAConstants.INDENTED_CONJUNCTIVE);
				tlaBuffer.append(var).append(" ").append(TLAConstants.EQ).append("_TETrace[i].")
						.append(var);
				tlaBuffer.append(TLAConstants.CR);

				// x' = _TETrace[_TEPosition+1].x
				tlaBuffer.append(TLAConstants.INDENT).append(TLAConstants.INDENTED_CONJUNCTIVE);
				tlaBuffer.append(var).append(TLAConstants.PRIME);
				tlaBuffer.append(TLAConstants.EQ).append("_TETrace[j].").append(var);
				tlaBuffer.append(TLAConstants.CR);
	        }
		}

		String jsonComment = TLAConstants.INDENT + TLAConstants.COMMENT;
		if (System.getProperty("TLC_TRACE_EXPLORER_JSON_UNCOMMENTED") != null) {
			// For tests, it's valuable to check the json output, so we remove the
			// comment through a JVM property.
			jsonComment = "";
		}

		tlaBuffer.append(TLAConstants.CR).append(TLAConstants.COMMENT)
			.append("Uncomment the ASSUME below to write the states of the error trace").append(TLAConstants.CR);
		tlaBuffer.append(TLAConstants.COMMENT).append("to the given file in Json format. Note that you can pass any tuple").append(TLAConstants.CR);
		tlaBuffer.append(TLAConstants.COMMENT).append("to `JsonSerialize`. For example, a sub-sequence of _TETrace.").append(TLAConstants.CR);
		tlaBuffer.append(jsonComment).append(TLAConstants.KeyWords.ASSUME).append(TLAConstants.CR);
		tlaBuffer.append(jsonComment + TLAConstants.INDENT).append("LET J == INSTANCE Json").append(TLAConstants.CR);
		tlaBuffer.append(jsonComment + TLAConstants.INDENT + TLAConstants.INDENT)
			.append(String.format("IN J!JsonSerialize(\"%s.json\", _TETrace)", teSpecModuleName)).append(TLAConstants.CR);		

		tlaBuffer.append(TLAConstants.CR);
	}

	public String addTraceFunction(final List<MCState> input) {
		final String identifier = SpecWriterUtilities.getValidIdentifier(TLAConstants.Schemes.DEFOV_SCHEME);
		return addTraceFunctionToBuffers(tlaBuffer, cfgBuffer, input, identifier, identifier);
	}

	public String addTraceFunction(final List<MCState> input, final String id, final String configId) {
		return addTraceFunctionToBuffers(tlaBuffer, cfgBuffer, input, id, configId);
	}

	/*
	 * See https://github.com/tlaplus/tlaplus/issues/482 for why we create the
	 * _SpecTETraceDef symbol. In short, it leads to faster evaluation because TLC's
	 * caching kicks in.
	 * 
	 * The reason why the trace function is in a dedicated module (via monolith spec
	 * functionality) is to make it easy for users to edit SpecTE to replace the
	 * TLA+ encoded trace function with a significantly more efficient binary
	 * encoding to work around deficiencies in SANY and semantic processing.
	 */
	public void addTraceFunctionInstance(final String moduleName) {
		/* With EWD840_TE as moduleName:
           _trace ==
               LET EWD840_TETrace == INSTANCE EWD840_TETrace
               IN EWD840_EWD840_TETrace!trace
		   ----
		 */
		// This expression has temporal level because of the INSTANCE statement
		// and the fact that the module  EWD840_TETrace  indirectly extends
		// the original spec  EWD840.  The tlc2.tool.impl.SymbolNodeValueLookupProvider
		// over-approximates the level of expressions and cannot figure out that
		// the  EWD840_TETrace  module is a constant/variable-free spec.
		// Assuming the specs below, the fact that the expr has temporal level
		// has the following side effect. The first conjunct of  MyInit  is not
		// evaluated as part of the initial predicate.  Only the second conjunct,
		// i.e., the in-lined  Init  gets evaluated.
		//
		//   VARIABLES v
		//   Init == v \in 1..42
		//   Next == ...
		//   Spec == Init /\ [][Next]_v
		//
		// a te spec:
		//
		//   _trace == ...
		//   MyInit ==
		//       /\ v = _trace[1].v
		//       /\ v \in 1..42 \* Init in-lined
		//
		// and a config:
		//
		//   CONSTANT Init <- MyInit
		//   SPECIFICATION Spec
		//
		tlaBuffer
				.append(String.format("%s ==%s%sLET %s == INSTANCE %s%s%sIN %s!%s",
						TLAConstants.TraceExplore.SPEC_TETRACE_TRACE, TLAConstants.CR, TLAConstants.INDENT,
						moduleName, moduleName, TLAConstants.CR, TLAConstants.INDENT, moduleName,
						TLAConstants.TraceExplore.SPEC_TETRACE_TRACE_DEF))
				.append(TLAConstants.CR).append(TLAConstants.SEP).append(TLAConstants.CR);
	}

	public void addTraceExpressionInstance(final String moduleName) {
		/* With EWD840_TE as moduleName:
           _expression ==
               LET EWD840_TEExpression == INSTANCE EWD840_TEExpression
               IN EWD840_EWD840_TEExpression!expression
		   ----
		 */
		tlaBuffer
				.append(String.format("%s ==%s%sLET %s == INSTANCE %s%s%sIN %s!%s",
						TLAConstants.TraceExplore.SPEC_TE_TTRACE_EXPRESSION, TLAConstants.CR, TLAConstants.INDENT,
						moduleName, moduleName, TLAConstants.CR, TLAConstants.INDENT, moduleName,
						TLAConstants.TraceExplore.SPEC_TE_TRACE_EXPRESSION))
				.append(TLAConstants.CR).append(TLAConstants.SEP).append(TLAConstants.CR).append(TLAConstants.CR);
	}

    /**
     * Returns a string representing the formula describing the state.
     * If the state has var1=expr1, var2 = expr2, and var3=expr3, then this returns:
     * 
     * var1 = (expr1)
     * /\
     * var2 = (expr2)
	 * /\
	 * var3 = (expr3)          
     * 
     * The expressions expr1, expr2, and expr3 can take up multiple lines.
	 * 
	 * The expressions are idented twice.
     * 
     * This will return null if the state is stuttering or back to state.
     * 
     * @param state
     * @return
     */
	private static String getStateConjunction(final MCState state) {
		return getStateConjunction(state, null);
	}
	
	private static String getStateConjunction(final MCState state, final String prefixConjunct) {
		if (state.isBackToState()) {
			return null;
		} else if (state.isStuttering()) {
			return null;
		} else {
            final StringBuilder formula = new StringBuilder();
            if (prefixConjunct != null) {
            	formula.append(prefixConjunct).append(TLAConstants.CR).append(TLAConstants.TLA_AND).append(TLAConstants.CR);
            }
            final MCVariable[] vars = state.getVariables();
			for (int i = 0; i < vars.length; i++) {
				final MCVariable var = vars[i];
				formula.append(var.getName()).append(TLAConstants.EQ).append(TLAConstants.L_PAREN);
				formula.append(var.getValueAsString()).append(TLAConstants.R_PAREN);

				// append /\ except for the last variable
				if (i != (vars.length - 1)) {
                    formula.append(TLAConstants.CR).append(TLAConstants.TLA_AND).append(TLAConstants.CR);
                }
            }

            return indentString(formula.toString(), 2);
        }
    }

	public StringBuilder append(String str) {
		return tlaBuffer.append(str);
	}
	
	public String toString() {
		return tlaBuffer.toString();
	}

	public String getComment() {
		return tlaBuffer.toString().replaceFirst("^", "\\\\*").replaceAll("\n", "\n\\\\*");
	}

	/**
	 * Indent n times a entire multiline string.
	 */
	static public String indentString(String s, int n) {
		final String idnt = new String(new char[n]).replace("\0", TLAConstants.INDENT);
		return idnt + String.join(TLAConstants.CR + idnt, s.split(TLAConstants.CR));
	}

	public void wrapConfig(String moduleFilename) {
		// Header
		final StringBuilder buffer = new StringBuilder();
		buffer.append("\n").append(TLAConstants.SEP).append(' ').append("CONFIG").append(' ');
		buffer.append(moduleFilename).append(' ').append(TLAConstants.SEP).append('\n');
		cfgBuffer.insert(0, buffer);
		
		// Footer
		cfgBuffer.append(getTLAModuleClosingTag());
	}
}
