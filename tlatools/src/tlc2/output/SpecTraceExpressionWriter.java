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
import util.TLAConstants;

/**
 * This is the abstract class of spec writers which produce specs capable of containing trace expressions.
 */
public class SpecTraceExpressionWriter extends AbstractSpecWriter {
	private static final String TRACE_EXPRESSION_VARIABLE = "TraceExp";
	
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
	 * @param actionConstraintId the indentified used for the action constraint
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
	 * 				definitions for Init and finally Next. This will return null if {@code trace.size() == 0}
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
				cfgBuffer.append(TLAConstants.COMMENT).append(TLAConstants.KeyWords.INIT).append(" definition");
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
	            
	            initAndNext.append(TLAConstants.INDENT).append(TLAConstants.INDENT).append(TLAConstants.INDENT);
	            initAndNext.append(var.getValueAsString()).append(TLAConstants.CR);
	            
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
	
	                initAndNext.append(TLAConstants.INDENT).append(TLAConstants.INDENT).append(TLAConstants.INDENT);
					if (expressionInfo.getLevel() == 2) {
	                    // add "--" if the expression is temporal level
						initAndNext.append(TLAConstants.TRACE_NA);
					} else {
	                    // add the actual expression if it is not temporal level
						initAndNext.append(expressionInfo.getExpression());
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
	         * relation (42 for the example above). For each state generated during
	         * breadth-first search, all Actions were evaluated, but the assumption was
	         * that only the one corresponding to the level of the current state would
	         * generate a valid successor state. However, this is not true if a trace expression This poses two problems:
	         * 1)  Actions may 
	         * 
	         * However, for some next-state relations
	         * 
	         * Non-determinism in trace expression
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
					subActionsAndConstraint.append(TLAConstants.L_PAREN).append(currentStateVar.getValueAsString());
					subActionsAndConstraint.append(TLAConstants.R_PAREN).append(TLAConstants.CR);
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
	                subActionsAndConstraint.append(TLAConstants.EQ).append(TLAConstants.L_PAREN);
	                subActionsAndConstraint.append(nextStateVar.getValueAsString()).append(TLAConstants.R_PAREN);
					subActionsAndConstraint.append(TLAConstants.CR);
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
	                    subActionsAndConstraint.append(TLAConstants.INDENT).append(TLAConstants.INDENT).append(TLAConstants.INDENT);
	                    subActionsAndConstraint.append(expressionInfo.getExpression()).append(TLAConstants.CR);
	                    subActionsAndConstraint.append(TLAConstants.INDENT).append(TLAConstants.INDENT).append(TLAConstants.INDENT);
	                    subActionsAndConstraint.append(TLAConstants.R_PAREN);
	
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
	        
			
			subActionsAndConstraint.append(TLAConstants.COMMENT).append("TRACE Action Constraint definition ");
			subActionsAndConstraint.append(TLAConstants.TraceExplore.TRACE_EXPLORE_ACTION_CONSTRAINT);
			subActionsAndConstraint.append(TLAConstants.CR).append(actionConstraintBuffer.toString());
			subActionsAndConstraint.append(TLAConstants.END_TUPLE).append("[TLCGet(\"level\")]");

			subActionsAndConstraint.append(CLOSING_SEP).append(TLAConstants.CR);

			
	        return new StringBuilder[] { subActionsAndConstraint, initAndNext };
	    }
		
		return null;
	}

	public static void addTraceFunctionToBuffers(final StringBuilder tlaBuffer, final StringBuilder cfgBuffer,
			final List<MCState> input) {
		// Filter stuttering or back2state instances from trace.
		final List<MCState> trace = input.stream()
				.filter(state -> !state.isBackToState() && !state.isStuttering())
				.collect(Collectors.toList());
		
		if (trace.isEmpty()) {
			return;
	    }
		
		// Trace
		final StringBuilder traceFunctionDef = new StringBuilder();
		traceFunctionDef.append(TLAConstants.BEGIN_TUPLE).append(TLAConstants.CR);
		for (int j = 0; j < trace.size(); j++) {
			final MCState state = trace.get(j);

			traceFunctionDef.append(TLAConstants.L_PAREN).append(state.asSimpleRecord()).append(TLAConstants.R_PAREN);

			if (j < trace.size() - 1) {
				traceFunctionDef.append(TLAConstants.COMMA).append(TLAConstants.CR);
			}
		}
		traceFunctionDef.append(TLAConstants.CR).append(TLAConstants.END_TUPLE);
		traceFunctionDef.append(CLOSING_SEP).append(TLAConstants.CR);
		
		addArrowAssignmentToBuffers(tlaBuffer, cfgBuffer,
				new Assignment(TLAConstants.TraceExplore.TRACE, new String[0], traceFunctionDef.toString()),
				TLAConstants.Schemes.DEFOV_SCHEME);
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
	
	public void addPrimer(final String moduleFilename, final String extendedModuleName, final Set<String> extraExtendedModules) {
		if (extendedModuleName != null) {
			extraExtendedModules.add(extendedModuleName);
		}
		
		// Not sure why this is required by TE.tla.
		extraExtendedModules.add("TLC");
		
		// A TE spec has to extend Toolbox to have access to _TETrace and _TEPosition
		// operators.
		extraExtendedModules.add("Toolbox");
		
		tlaBuffer.append(SpecWriterUtilities.getExtendingModuleContent(moduleFilename,
				extraExtendedModules.toArray(new String[extraExtendedModules.size()])));
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
	 * inv_12312321321 ==
	 * ~(
	 * P
	 * )
	 * ----
	 * 
	 * @param finalState
	 */
	public void addInvariant(final MCState finalState) {
	    final String id = SpecWriterUtilities.getValidIdentifier(TLAConstants.Schemes.INVARIANT_SCHEME);
	    cfgBuffer.append(TLAConstants.COMMENT).append(TLAConstants.KeyWords.INVARIANT).append(" definition");
	    cfgBuffer.append(TLAConstants.CR).append(TLAConstants.KeyWords.INVARIANT).append(TLAConstants.CR);
	    cfgBuffer.append(id).append(TLAConstants.CR);
	
	    tlaBuffer.append(TLAConstants.COMMENT).append(TLAConstants.KeyWords.INVARIANT).append(" definition");
	    tlaBuffer.append(TLAConstants.CR).append(id).append(TLAConstants.DEFINES_CR);
	    tlaBuffer.append(TLAConstants.TLA_NOT).append(TLAConstants.L_PAREN).append(TLAConstants.CR);
	    tlaBuffer.append(getStateConjunction(finalState)).append(TLAConstants.CR).append(TLAConstants.R_PAREN);
	
	    tlaBuffer.append(CLOSING_SEP).append(TLAConstants.CR);
	}

	/**
	 * Adds the temporal property ~<>[](P) where P is the formula describing finalState.
	 * The format in the tla file is as follows:
	 * 
	 * prop_23112321 ==
	 * ~<>[](
	 * P
	 * )
	 * ----
	 * 
	 * @param finalState
	 */
	public void addStutteringProperty(final MCState finalState) {
	    String id = SpecWriterUtilities.getValidIdentifier(TLAConstants.Schemes.PROP_SCHEME);
	    cfgBuffer.append(TLAConstants.COMMENT).append(TLAConstants.KeyWords.PROPERTY).append(" definition");
	    cfgBuffer.append(TLAConstants.CR).append(TLAConstants.KeyWords.PROPERTY).append(TLAConstants.CR);
	    cfgBuffer.append(id).append(TLAConstants.CR);
	
	    tlaBuffer.append(TLAConstants.COMMENT).append(TLAConstants.KeyWords.PROPERTY).append(" definition");
	    tlaBuffer.append(TLAConstants.CR).append(id).append(TLAConstants.DEFINES_CR);
	    tlaBuffer.append(TLAConstants.TLA_NOT).append(TLAConstants.TLA_EVENTUALLY_ALWAYS);
	    tlaBuffer.append(TLAConstants.L_PAREN).append(TLAConstants.CR).append(getStateConjunction(finalState));
	    tlaBuffer.append(TLAConstants.CR).append(TLAConstants.R_PAREN).append(CLOSING_SEP).append(TLAConstants.CR);
	}

	/**
	 * Adds the temporal property ~([]<>P /\ []<>Q), where P is the formula describing finalState and 
	 * Q the formula describing backToState. The formating in the tla file is as follows:
	 * 
	 * prop_21321312 ==
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
	public void addBackToStateProperty(final MCState finalState, final MCState backToState) {
	    final String id = SpecWriterUtilities.getValidIdentifier(TLAConstants.Schemes.PROP_SCHEME);
	    cfgBuffer.append(TLAConstants.COMMENT).append(TLAConstants.KeyWords.PROPERTY).append(" definition");
	    cfgBuffer.append(TLAConstants.CR).append(TLAConstants.KeyWords.PROPERTY).append(TLAConstants.CR);
	    cfgBuffer.append(id).append(TLAConstants.CR);
	
	    tlaBuffer.append(TLAConstants.COMMENT).append(TLAConstants.KeyWords.PROPERTY).append(" definition");
	    tlaBuffer.append(TLAConstants.CR).append(id).append(TLAConstants.DEFINES_CR);
	    tlaBuffer.append(TLAConstants.TLA_NOT).append(TLAConstants.L_PAREN).append(TLAConstants.L_PAREN);
	    tlaBuffer.append(TLAConstants.TLA_INF_OFTEN).append(TLAConstants.L_PAREN).append(TLAConstants.CR);
	    tlaBuffer.append(getStateConjunction(finalState)).append(TLAConstants.CR).append(TLAConstants.R_PAREN);
	    tlaBuffer.append(TLAConstants.R_PAREN).append(TLAConstants.TLA_AND).append(TLAConstants.L_PAREN);
	    tlaBuffer.append(TLAConstants.TLA_INF_OFTEN).append(TLAConstants.L_PAREN).append(TLAConstants.CR);
	    tlaBuffer.append(getStateConjunction(backToState)).append(TLAConstants.CR).append(TLAConstants.R_PAREN);
	    tlaBuffer.append(TLAConstants.R_PAREN).append(TLAConstants.R_PAREN).append(CLOSING_SEP).append(TLAConstants.CR);
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
	public String[] addInitNext(final List<MCState> trace, final TraceExpressionInformationHolder[] expressionData) {
		return addInitNextToBuffers(tlaBuffer, cfgBuffer, trace, expressionData);
	}

	/**
	 * @see #addInitNextToBuffers(StringBuilder, StringBuilder, List, TraceExpressionInformationHolder[], String, String, String)
	 */
	public void addInitNext(final List<MCState> trace, final TraceExpressionInformationHolder[] expressionData,
			final String initId, String nextId, final String actionConstraintId) {
		addInitNextToBuffers(tlaBuffer, cfgBuffer, trace, expressionData, initId, nextId, actionConstraintId);
	}

	public void addTraceFunction(final List<MCState> input) {
		addTraceFunctionToBuffers(tlaBuffer, cfgBuffer, input);
	}
	
    /**
     * Returns a string representing the formula describing the state.
     * If the state has var1=expr1, var2 = expr2, and var3=expr3, then this returns:
     * 
     * var1=(
     * expr1
     * )/\
     * var2=(
     * expr2
     * )/\
     * var3=(
     * expr3
     * )
     * 
     * 
     * The expressions expr1, expr2, and expr3 can take up multiple lines.
     * 
     * This will return null if the state is stuttering or back to state.
     * 
     * @param state
     * @return
     */
	private static String getStateConjunction(final MCState state) {
		if (state.isBackToState()) {
			return null;
		} else if (state.isStuttering()) {
			return null;
		} else {
            final StringBuilder formula = new StringBuilder();
            final MCVariable[] vars = state.getVariables();
			for (int i = 0; i < vars.length; i++) {
				final MCVariable var = vars[i];
				formula.append(var.getName()).append(TLAConstants.EQ).append(TLAConstants.L_PAREN).append(TLAConstants.CR);
				formula.append(var.getValueAsString()).append(TLAConstants.CR).append(TLAConstants.R_PAREN);

				// append /\ except for the last variable
				if (i != (vars.length - 1)) {
                    formula.append(TLAConstants.TLA_AND).append(TLAConstants.CR);
                }
            }

            return formula.toString();
        }
    }
}
