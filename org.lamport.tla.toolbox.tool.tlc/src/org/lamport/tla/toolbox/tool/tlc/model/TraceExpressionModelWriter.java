/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
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
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.tool.tlc.model;

import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.TraceExpressionInformationHolder;
import org.lamport.tla.toolbox.tool.tlc.traceexplorer.SimpleTLCState;
import org.lamport.tla.toolbox.tool.tlc.traceexplorer.SimpleTLCVariable;

public class TraceExpressionModelWriter extends ModelWriter {

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
	public TraceExpressionInformationHolder[] createAndAddVariablesAndDefinitions(List<Formula> expressions, String attributeName) {
	
	    TraceExpressionInformationHolder[] expressionData = new TraceExpressionInformationHolder[expressions.size()];
	    Iterator<Formula> it = expressions.iterator();
	    int position = 0;
	    while (it.hasNext())
	    {
	        String expression = it.next().getFormula();
	
	        if (expression != null && expression.length() > 0)
	        {
	            expressionData[position] = new TraceExpressionInformationHolder(expression,
	                    getValidIdentifier(TRACE_EXPR_DEF_SCHEME), getValidIdentifier(TRACE_EXPR_VAR_SCHEME));
	        }
	
	        position++;
	    }
	
	    addVariablesAndDefinitions(expressionData, attributeName, true);
	
	    return expressionData;
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
	public void addVariablesAndDefinitions(TraceExpressionInformationHolder[] traceExpressionData, String attributeName, boolean addDefinitions) {
	    if (traceExpressionData.length == 0)
	    {
	        return;
	    }
	
	    StringBuffer variableDecls = new StringBuffer();
	    StringBuffer definitions = new StringBuffer();
	
	    for (int i = 0; i < traceExpressionData.length; i++)
	    {
	        TraceExpressionInformationHolder expressionInfo = traceExpressionData[i];
	
	        variableDecls.append(expressionInfo.getVariableName());
	        // we add a comma after every variable except for the last
	        if (i != traceExpressionData.length - 1)
	        {
	            variableDecls.append(COMMA);
	        }
	
	        if (addDefinitions)
	        {
	            // define the identifier corresponding to this expression - looks like:
	            // \* comment line
	            // trace_def_213123123123 ==
	            // expression
	            // ----
	            definitions.append(COMMENT).append("TRACE EXPLORER identifier definition ").append(ATTRIBUTE).append(
	                    attributeName).append(CR);
	            definitions.append(expressionInfo.getIdentifier()).append(DEFINES_CR).append(
	                    expressionInfo.getExpression()).append(CR);
	            definitions.append(SEP).append(CR).append(CR);
	        }
	    }
	
	    // variable declaration
	    tlaBuffer.append(COMMENT).append("TRACE EXPLORER variable declaration ").append(ATTRIBUTE)
	            .append(attributeName).append(CR);
	    tlaBuffer.append("VARIABLES ").append(variableDecls.toString()).append(CR);
	
	    tlaBuffer.append(SEP).append(CR).append(CR);
	
	    if (addDefinitions)
	    {
	        // append the expression definitions
	        tlaBuffer.append(definitions.toString());
	    }
	}

	/**
	 * This will generate two identifiers equal to the initial and next state
	 * predicate for the trace. If expressionData is not null, it should contain information
	 * about trace explorer expressions. This information is used to appropriately put
	 * the variables representing trace explorer expressions in the trace. In the following example, trace
	 * explorer expressions are used, but if expressionData is null, those variables will not appear in the
	 * init and next definitions, but everything else will be the same.
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
	 * @param trace
	 * @param expressionData data on trace explorer expressions, can be null
	 * @return String[], first element is the identifier for the initial state predicate,
	 * second element is the identifier for the next-state action
	 */
	public String[] addInitNext(List<SimpleTLCState> trace, TraceExpressionInformationHolder[] expressionData) {
	    String initId = getValidIdentifier(INIT_SCHEME);
	    String nextId = getValidIdentifier(NEXT_SCHEME);
	
	    addInitNext(trace, expressionData, initId, nextId);
	
	    return new String[] { initId, nextId };
	}

	/**
	 * This will set initId equal to the initial state predicate and nextId equal to the next state
	 * action for the trace. If expressionData is not null, it should contain information
	 * about trace explorer expressions. This information is used to appropriately put
	 * the variables representing trace explorer expressions in the trace. In the following example, trace
	 * explorer expressions are used, but if expressionData is null, those variables will not appear in the
	 * init and next definitions, but everything else will be the same.
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
	 * @param trace
	 * @param expressionData data on trace explorer expressions, can be null
	 * @param initId the identifier to be used for the initial state predicate, cannot be null
	 * @param nextId the identifier to be used for the next-state action, cannot be null
	 */
	public void addInitNext(List<SimpleTLCState> trace, TraceExpressionInformationHolder[] expressionData, String initId, String nextId) {
	
	    if (trace.size() > 0)
	    {
	        Iterator<SimpleTLCState> it = trace.iterator();
	        SimpleTLCState currentState = it.next();
	
	        /*******************************************************
	         * Add the init definition.                            *
	         *******************************************************/
	        cfgBuffer.append(COMMENT).append("INIT definition").append(CR);
	        cfgBuffer.append("INIT").append(CR);
	        cfgBuffer.append(initId).append(CR);
	
	        tlaBuffer.append(COMMENT).append("TRACE INIT definition").append(
	                IModelConfigurationConstants.TRACE_EXPLORE_INIT).append(CR);
	        tlaBuffer.append(initId).append(DEFINES_CR);
	        SimpleTLCVariable[] vars = currentState.getVars();
	
	        // variables from spec
	        for (int i = 0; i < vars.length; i++)
	        {
	            SimpleTLCVariable var = vars[i];
	            /*
	             * var=(
	             * expr
	             * )
	             */
	            tlaBuffer.append(var.getVarName()).append(EQ).append(L_PAREN).append(CR).append(var.getValueAsString())
	                    .append(CR).append(R_PAREN);
	            /*
	             * Add /\ after right parenthesis except for the last variable
	             * 
	             * var=(
	             * expr
	             * )/\
	             */
	            if (i != vars.length - 1)
	            {
	                tlaBuffer.append(TLA_AND).append(CR);
	            }
	        }
	
	        // variables representing trace explorer expressions
	        if (expressionData != null)
	        {
	            for (int i = 0; i < expressionData.length; i++)
	            {
	                TraceExpressionInformationHolder expressionInfo = expressionData[i];
	                tlaBuffer.append(TLA_AND).append(CR).append(expressionInfo.getVariableName()).append(EQ).append(
	                        L_PAREN).append(CR);
	
	                if (expressionInfo.getLevel() == 2)
	                {
	                    // add "--" if the expression is temporal level
	                    tlaBuffer.append(TRACE_NA);
	                } else
	                {
	                    // add the actual expression if it is not temporal level
	                    tlaBuffer.append(expressionInfo.getExpression());
	                }
	
	                tlaBuffer.append(CR).append(R_PAREN);
	            }
	        }
	
	        tlaBuffer.append(CR).append(SEP).append(CR).append(CR);
	
	        /**********************************************************
	         *  Now add the next state actions definition             *
	         **********************************************************/
	        cfgBuffer.append(COMMENT).append("NEXT definition").append(CR);
	        cfgBuffer.append("NEXT").append(CR);
	        cfgBuffer.append(nextId).append(CR);
	
	        tlaBuffer.append(COMMENT).append("TRACE NEXT definition").append(
	                IModelConfigurationConstants.TRACE_EXPLORE_NEXT).append(CR);
	        tlaBuffer.append(nextId).append(DEFINES_CR);
	
	        SimpleTLCState nextState = null;
	        boolean isSingleState;
	        if (it.hasNext())
	        {
	            nextState = (SimpleTLCState) it.next();
	            isSingleState = false;
	        } else
	        {
	            nextState = currentState;
	            isSingleState = true;
	        }
	
	        while (nextState != null)
	        {
	            /*
	             * Handle Back to state and stuttering.
	             * 
	             * nextState is assigned to the state which the "Back to state"
	             * or "Stuttering" state represents. If nextState is "Back to state i",
	             * then it is assigned to state i. If nextState is "Stuttering", then
	             * it is assigned to the current state.
	             */
	            if (nextState.isBackToState())
	            {
	                nextState = (SimpleTLCState) trace.get(nextState.getStateNumber() - 1);
	            } else if (nextState.isStuttering())
	            {
	                nextState = currentState;
	            }
	
	            /*
	             * Write the action:
	             * 
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
	             * ))
	             */
	            tlaBuffer.append(L_PAREN);
	
	            SimpleTLCVariable[] currentStateVars = currentState.getVars();
	            SimpleTLCVariable[] nextStateVars = nextState.getVars();
	
	            /*
	             * Iterate through current state variables. This adds:
	             * 
	             * var1=(
	             * expr1
	             * )/\
	             * var2=(
	             * expr2
	             * )/\
	             * 
	             */
	            for (int i = 0; i < currentStateVars.length; i++)
	            {
	                SimpleTLCVariable currentStateVar = currentStateVars[i];
	                tlaBuffer.append(currentStateVar.getVarName()).append(EQ).append(L_PAREN).append(CR).append(
	                        currentStateVar.getValueAsString()).append(CR).append(R_PAREN).append(TLA_AND).append(CR);
	            }
	
	            /*
	             * If the trace is a single state, make the next state
	             * action never enabled. The model will deadlock in the initial state.
	             * This adds:
	             * 
	             * FALSE
	             * /\
	             */
	            if (isSingleState)
	            {
	                tlaBuffer.append("FALSE").append(CR).append(TLA_AND).append(CR);
	            }
	
	            /*
	             * Iterate through next state variables. This adds:
	             * 
	             * var1'=(
	             * expr3
	             * )/\
	             * var2'=(
	             * expr4
	             * )
	             */
	            for (int i = 0; i < currentStateVars.length; i++)
	            {
	                SimpleTLCVariable nextStateVar = nextStateVars[i];
	                tlaBuffer.append(nextStateVar.getVarName()).append(PRIME).append(EQ).append(L_PAREN).append(CR)
	                        .append(nextStateVar.getValueAsString()).append(CR).append(R_PAREN);
	                // add /\ for each variable except the last one
	                if (i != currentStateVars.length - 1)
	                {
	                    tlaBuffer.append(TLA_AND).append(CR);
	                }
	            }
	
	            /*
	             * Iterate through the trace explorer expressions if there are any. This adds:
	             * 
	             *  /\
	             * var3'=(
	             * texpr1
	             * )/\
	             * var4'=(
	             * texpr2
	             * )'
	             * 
	             */
	            if (expressionData != null)
	            {
	                for (int i = 0; i < expressionData.length; i++)
	                {
	                    TraceExpressionInformationHolder expressionInfo = expressionData[i];
	                    tlaBuffer.append(TLA_AND).append(CR).append(expressionInfo.getVariableName()).append(PRIME)
	                            .append(EQ).append(L_PAREN).append(CR).append(expressionInfo.getExpression())
	                            .append(CR).append(R_PAREN);
	
	                    if (expressionInfo.getLevel() < 2)
	                    {
	                        tlaBuffer.append(PRIME);
	                    }
	                }
	            }
	
	            tlaBuffer.append(R_PAREN);
	
	            if (it.hasNext())
	            {
	                tlaBuffer.append(CR).append(TLA_OR).append(CR);
	            }
	
	            currentState = nextState;
	
	            if (it.hasNext())
	            {
	                nextState = (SimpleTLCState) it.next();
	            } else
	            {
	                nextState = null;
	            }
	        }
	
	        tlaBuffer.append(CR).append(SEP).append(CR).append(CR);
	
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
	public void addInvariant(SimpleTLCState finalState) {
	    String id = getValidIdentifier(INVARIANT_SCHEME);
	    cfgBuffer.append(COMMENT).append("INVARIANT definition").append(CR);
	    cfgBuffer.append("INVARIANT").append(CR);
	    cfgBuffer.append(id).append(CR);
	
	    tlaBuffer.append(COMMENT).append("INVARIANT definition").append(CR);
	    tlaBuffer.append(id).append(DEFINES_CR);
	    tlaBuffer.append(TLA_NOT).append(L_PAREN).append(CR).append(getStateConjunction(finalState)).append(CR).append(
	            R_PAREN).append(CR);
	
	    tlaBuffer.append(SEP).append(CR).append(CR);
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
	public void addStutteringProperty(SimpleTLCState finalState) {
	    String id = getValidIdentifier(PROP_SCHEME);
	    cfgBuffer.append(COMMENT).append("PROPERTY definition").append(CR);
	    cfgBuffer.append("PROPERTY").append(CR);
	    cfgBuffer.append(id).append(CR);
	
	    tlaBuffer.append(COMMENT).append("PROPERTY definition").append(CR);
	    tlaBuffer.append(id).append(DEFINES_CR);
	    tlaBuffer.append(TLA_NOT).append(TLA_EVENTUALLY_ALWAYS).append(L_PAREN).append(CR).append(
	            getStateConjunction(finalState)).append(CR).append(R_PAREN).append(CR);
	
	    tlaBuffer.append(SEP).append(CR).append(CR);
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
	public void addBackToStateProperty(SimpleTLCState finalState, SimpleTLCState backToState) {
	    String id = getValidIdentifier(PROP_SCHEME);
	    cfgBuffer.append(COMMENT).append("PROPERTY definition").append(CR);
	    cfgBuffer.append("PROPERTY").append(CR);
	    cfgBuffer.append(id).append(CR);
	
	    tlaBuffer.append(COMMENT).append("PROPERTY definition").append(CR);
	    tlaBuffer.append(id).append(DEFINES_CR);
	    tlaBuffer.append(TLA_NOT).append(L_PAREN).append(L_PAREN).append(TLA_INF_OFTEN).append(L_PAREN).append(CR)
	            .append(getStateConjunction(finalState)).append(CR).append(R_PAREN).append(R_PAREN).append(TLA_AND)
	            .append(L_PAREN).append(TLA_INF_OFTEN).append(L_PAREN).append(CR).append(
	                    getStateConjunction(backToState)).append(CR).append(R_PAREN).append(R_PAREN).append(R_PAREN)
	            .append(CR);
	
	    tlaBuffer.append(SEP).append(CR).append(CR);
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
	public void addInfoComments(TraceExpressionInformationHolder[] traceExpressionData) {
	    for (int i = 0; i < traceExpressionData.length; i++)
	    {
	        TraceExpressionInformationHolder expressionData = traceExpressionData[i];
	        tlaBuffer.append(COMMENT).append(INDEX).append(expressionData.getLevel()).append(INDEX).append(
	                expressionData.getVariableName()).append(INDEX).append(expressionData.getExpression()).append(
	                CONSTANT_EXPRESSION_EVAL_IDENTIFIER).append(CR);
	    }
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
    private static String getStateConjunction(SimpleTLCState state)
    {
        if (state.isBackToState())
        {
            return null;
        } else if (state.isStuttering())
        {
            return null;
        } else
        {
            StringBuffer formula = new StringBuffer();
            SimpleTLCVariable[] vars = state.getVars();
            for (int i = 0; i < vars.length; i++)
            {
                SimpleTLCVariable var = vars[i];
                formula.append(var.getVarName()).append(EQ).append(L_PAREN).append(CR).append(var.getValueAsString())
                        .append(CR).append(R_PAREN);

                // append /\ except for the last variable
                if (i != vars.length - 1)
                {
                    formula.append(TLA_AND).append(CR);
                }
            }

            return formula.toString();
        }
    }

    /**
    * This adds the trace explorer variables to initWithoutTraceVars.
    * The method returns a list with one element, a
    * String[]. The first element of the array is put in TE.cfg, and the
    * second element is put in TE.tla. The intention is to use
    * the return value as the first argument of {@link ModelWriter#addFormulaList(List, String, String)}.
    * 
    * This can be best explained with an example.
    * 
    * The trace is the following:
    
    STATE 1: <Initial predicate>
    /\ x = 0
    /\ y = 0

    STATE 2: <Action line 8, col 3 to line 9, col 15 of module Test>
    /\ x = 1
    /\ y = 0

    STATE 3: <Action line 8, col 3 to line 9, col 15 of module Test>
    /\ x = 2
    /\ y = 1

    STATE 4: <Action line 8, col 3 to line 9, col 15 of module Test>
    /\ x = 3
    /\ y = 3

    The user wants to evaluate two expressions:

    x + y
    x' > y

    The file TE.tla will define two new variables:

    VARIABLES sum, big

    The variables are named "sum" and "big" for the simplicity of this example. In
    reality they will be something like "trace_2348902347238", unless the user is
    responsible to assigning labels to the expressions. The file will also define
    two new identifiers:

    sum_def == x + y
    big_def == x' >y

    We define the initial predicate and next-state relation as follows:

    TInit ==
    /\ x = 0 
    /\ y = 0
    /\ sum = sum_def
    /\ big = "--"

    TNext ==
    \/ /\ x = 0
    /\ y = 0
    /\ x' = 1
    /\ y' = 0
    /\ sum' = sum_def'
    /\ big' = big_def

    \/ /\ x = 1
    /\ y = 0
    /\ x' = 2
    /\ y' = 1
    /\ sum' = sum_def'
    /\ big' = big_def

    \/ /\ x = 2
    /\ y = 1
    /\ x' = 3
    /\ y' = 3
    /\ sum' = sum_def'
    /\ big' = big_def

    The expression defined by big_def has primed variables so the variable big
    takes the value "--" in the initial state predicate. The expression defined by
    sum_def does not contain primed variables. This will produce an error trace by
    defining the invariant:

    ~(x=3/\y=3)
    
    * 
    * @param traceInit
    * @param nextWithoutTraceVars
    * @param traceExpressionData
    * @return
    */
    public static List<String[]> createInitContent(String traceInit, TraceExpressionInformationHolder[] traceExpressionData)
    {
        String id = getValidIdentifier(INIT_SCHEME);
        StringBuffer initPredicate = new StringBuffer();
        initPredicate.append(id).append(DEFINES_CR);
        initPredicate.append(traceInit);
        for (int i = 0; i < traceExpressionData.length; i++)
        {
            TraceExpressionInformationHolder expressionInfo = traceExpressionData[i];
            initPredicate.append(TLA_AND).append(expressionInfo.getVariableName()).append(EQ);
            if (expressionInfo.getLevel() < 2)
            {
                initPredicate.append(L_PAREN).append(expressionInfo.getExpression()).append(R_PAREN);
            } else
            {
                initPredicate.append(TRACE_NA);
            }
        }
        Vector<String[]> toReturn = new Vector<String[]>();
        toReturn.add(new String[] { id, initPredicate.toString() });
        return toReturn;
    }

    public static List<String[]> createNextContent(List<String> traceNextActions,
            TraceExpressionInformationHolder[] traceExpressionData)
    {
        String id = getValidIdentifier(NEXT_SCHEME);
        StringBuffer nextActionDisj = new StringBuffer();
        nextActionDisj.append(id).append(DEFINES_CR);
        Iterator<String> it = traceNextActions.iterator();
        while (it.hasNext())
        {
            String actionConj = it.next();
            nextActionDisj.append(TLA_OR).append(L_PAREN).append(actionConj);
            for (int i = 0; i < traceExpressionData.length; i++)
            {
                TraceExpressionInformationHolder expressionInfo = traceExpressionData[i];
                nextActionDisj.append(TLA_AND).append(expressionInfo.getVariableName()).append(PRIME).append(EQ);
                if (expressionInfo.getLevel() < 2)
                {
                    nextActionDisj.append(L_PAREN).append(expressionInfo.getExpression()).append(R_PAREN).append(PRIME);
                } else
                {
                    nextActionDisj.append(L_PAREN).append(expressionInfo.getExpression()).append(R_PAREN);
                }
            }
            nextActionDisj.append(R_PAREN).append(CR);
        }

        Vector<String[]> toReturn = new Vector<String[]>();
        toReturn.add(new String[] { id, nextActionDisj.toString() });
        return toReturn;
    }

}
