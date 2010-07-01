package org.lamport.tla.toolbox.tool.tlc.util;

import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.Region;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.TraceExpressionInformationHolder;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;
import org.lamport.tla.toolbox.tool.tlc.model.Formula;
import org.lamport.tla.toolbox.tool.tlc.model.TypedSet;
import org.lamport.tla.toolbox.tool.tlc.traceexplorer.SimpleTLCState;
import org.lamport.tla.toolbox.tool.tlc.traceexplorer.SimpleTLCVariable;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.OpDefNode;

/**
 * Encapsulates two buffers and provides semantic methods to add content to the _MC file and the CFG file of the model 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ModelWriter
{
    /**
     * Counter to be able to generate unique identifiers
     */
    private static long globalCounter = 1;

    public static final String SPEC_SCHEME = "spec";
    public static final String INIT_SCHEME = "init";
    public static final String NEXT_SCHEME = "next";
    public static final String CONSTANT_SCHEME = "const";
    public static final String SYMMETRY_SCHEME = "symm";
    public static final String DEFOV_SCHEME = "def_ov";
    public static final String CONSTRAINT_SCHEME = "constr";
    public static final String ACTIONCONSTRAINT_SCHEME = "action_constr";
    public static final String INVARIANT_SCHEME = "inv";
    public static final String PROP_SCHEME = "prop";
    public static final String VIEW_SCHEME = "view";
    public static final String CONSTANTEXPR_SCHEME = "const_expr";
    public static final String TRACE_EXPR_VAR_SCHEME = "__trace_var";
    public static final String TRACE_EXPR_DEF_SCHEME = "trace_def";

    public static final String SPACE = " ";
    public static final String CR = "\n";
    public static final String SEP = "----";
    public static final String EQ = " = ";
    public static final String ARROW = " <- ";
    public static final String DEFINES = " == ";
    public static final String DEFINES_CR = " ==\n";
    public static final String COMMENT = "\\* ";
    public static final String ATTRIBUTE = "@";
    public static final String INDEX = ":";
    public static final String EMPTY_STRING = "";
    public static final String CONSTANT_EXPRESSION_EVAL_IDENTIFIER = "\"$!@$!@$!@$!@$!\"";
    public static final String COMMA = ",";
    public static final String BEGIN_TUPLE = "<<";
    public static final String END_TUPLE = ">>";
    public static final String PRIME = "'";
    public static final String VARIABLES = "VARIABLES ";
    public static final String TLA_AND = "/\\";
    public static final String TLA_OR = "\\/";
    public static final String TLA_NOT = "~";
    public static final String TLA_EVENTUALLY_ALWAYS = "<>[]";
    public static final String TLA_INF_OFTEN = "[]<>";
    public static final String TRACE_NA = "\"--\"";
    public static final String L_PAREN = "(";
    public static final String R_PAREN = ")";

    private StringBuffer tlaBuffer;
    private StringBuffer cfgBuffer;

    /**
     * Constructs new model writer
     */
    public ModelWriter()
    {
        this.tlaBuffer = new StringBuffer(1024);
        this.cfgBuffer = new StringBuffer(1024);
    }

    /**
     * Write the content to files
     * @param tlaFile
     * @param cfgFile
     * @param monitor
     * @throws CoreException
     */
    public void writeFiles(IFile tlaFile, IFile cfgFile, IProgressMonitor monitor) throws CoreException
    {
        tlaBuffer.append(ResourceHelper.getModuleClosingTag());
        cfgBuffer.append(ResourceHelper.getConfigClosingTag());
        ResourceHelper.replaceContent(tlaFile, tlaBuffer, monitor);
        ResourceHelper.replaceContent(cfgFile, cfgBuffer, monitor);
    }

    /**
     * Add file header
     * @param moduleFilename
     * @param extendedModuleName
     */
    public void addPrimer(String moduleFilename, String extendedModuleName)
    {
        tlaBuffer.append(ResourceHelper.getExtendingModuleContent(moduleFilename, extendedModuleName));
    }

    /**
     * Add spec definition
     * @param specDefinition
     */
    public void addSpecDefinition(String[] specDefinition, String attributeName)
    {
        cfgBuffer.append("SPECIFICATION").append(SPACE);
        cfgBuffer.append(specDefinition[0]).append(CR);

        tlaBuffer.append(COMMENT).append("Specification ").append(ATTRIBUTE).append(attributeName).append(CR);
        tlaBuffer.append(specDefinition[1]).append(CR).append(SEP).append(CR);

    }

    /**
     * Add constants declarations
     * @param constants
     * @param modelValues
     */
    public void addConstants(List constants, TypedSet modelValues, String attributeConstants, String attributeMVs)
    {
        // add model value declarations
        addMVTypedSet(modelValues, "MV CONSTANT declarations ", attributeMVs);

        Assignment constant;
        Vector symmetrySets = new Vector();

        // first run for all the declarations
        for (int i = 0; i < constants.size(); i++)
        {
            constant = (Assignment) constants.get(i);
            if (constant.isModelValue())
            {
                if (constant.isSetOfModelValues())
                {
                    // set model values
                    TypedSet setOfMVs = TypedSet.parseSet(constant.getRight());
                    addMVTypedSet(setOfMVs, "MV CONSTANT declarations", attributeConstants);
                }
            }
        }

        // now all the definitions
        for (int i = 0; i < constants.size(); i++)
        {
            constant = (Assignment) constants.get(i);
            if (constant.isModelValue())
            {
                if (constant.isSetOfModelValues())
                {
                    // set model values
                    cfgBuffer.append(COMMENT).append("MV CONSTANT definitions").append(CR);
                    tlaBuffer.append(COMMENT).append("MV CONSTANT definitions " + constant.getLeft()).append(CR);

                    String id = addArrowAssignment(constant, CONSTANT_SCHEME);
                    if (constant.isSymmetricalSet())
                    {
                        symmetrySets.add(id);
                    }
                    tlaBuffer.append(SEP).append(CR).append(CR);
                } else
                {
                    cfgBuffer.append(COMMENT).append("CONSTANT declarations").append(CR);
                    // model value assignment
                    // to .cfg : foo = foo
                    // to _MC.tla : <nothing>, since the constant is already defined in one of the spec modules
                    cfgBuffer.append("CONSTANT").append(SPACE).append(constant.getLabel()).append(EQ).append(
                            constant.getRight()).append(CR);
                }
            } else
            {
                // simple constant value assignment
                cfgBuffer.append(COMMENT).append("CONSTANT definitions").append(CR);

                tlaBuffer.append(COMMENT).append("CONSTANT definitions ").append(ATTRIBUTE).append(attributeConstants)
                        .append(INDEX).append(i).append(constant.getLeft()).append(CR);
                addArrowAssignment(constant, CONSTANT_SCHEME);
                tlaBuffer.append(SEP).append(CR).append(CR);
            }
        }

        // symmetry
        if (!symmetrySets.isEmpty())
        {
            String label = ModelWriter.getValidIdentifier(SYMMETRY_SCHEME);

            tlaBuffer.append(COMMENT).append("SYMMETRY definition").append(CR);
            cfgBuffer.append(COMMENT).append("SYMMETRY definition").append(CR);

            tlaBuffer.append(label).append(DEFINES).append(CR);
            // symmetric model value sets added
            for (int i = 0; i < symmetrySets.size(); i++)
            {
                tlaBuffer.append("Permutations(").append((String) symmetrySets.get(i)).append(")");
                if (i != symmetrySets.size() - 1)
                {
                    tlaBuffer.append(" \\union ");
                }
            }

            tlaBuffer.append(CR).append(SEP).append(CR).append(CR);
            cfgBuffer.append("SYMMETRY").append(SPACE).append(label).append(CR);
        }

    }

    /**
     * Add the view definition
     * @param viewString the string that the user enters into the view field
     * @param attributeName the attribute name of the view field
     */
    public void addView(String viewString, String attributeName)
    {
        if (!(viewString.trim().length() == 0))
        {
            cfgBuffer.append(COMMENT).append("VIEW definition").append(CR);
            String id = ModelWriter.getValidIdentifier(VIEW_SCHEME);
            cfgBuffer.append("VIEW").append(CR).append(id).append(CR);
            tlaBuffer.append(COMMENT).append("VIEW definition ").append(ATTRIBUTE).append(attributeName).append(CR);
            tlaBuffer.append(id).append(DEFINES).append(CR).append(viewString).append(CR);
            tlaBuffer.append(SEP).append(CR).append(CR);
        }
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
    public TraceExpressionInformationHolder[] createAndAddTEVariablesAndDefinitions(List expressions,
            String attributeName)
    {

        TraceExpressionInformationHolder[] expressionData = new TraceExpressionInformationHolder[expressions.size()];
        Iterator it = expressions.iterator();
        int position = 0;
        while (it.hasNext())
        {
            Object next = it.next();
            Assert.isTrue(next instanceof Formula);
            String expression = ((Formula) next).getFormula();

            if (expression != null && expression.length() > 0)
            {
                expressionData[position] = new TraceExpressionInformationHolder(expression,
                        getValidIdentifier(TRACE_EXPR_DEF_SCHEME), getValidIdentifier(TRACE_EXPR_VAR_SCHEME));
            }

            position++;
        }

        addTEVariablesAndDefinitions(expressionData, attributeName, true);

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
    public void addTEVariablesAndDefinitions(TraceExpressionInformationHolder[] traceExpressionData,
            String attributeName, boolean addDefinitions)
    {
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
    public String[] addInitNextForTE(List trace, TraceExpressionInformationHolder[] expressionData)
    {
        String initId = getValidIdentifier(INIT_SCHEME);
        String nextId = getValidIdentifier(NEXT_SCHEME);

        addInitNextForTE(trace, expressionData, initId, nextId);

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
    public void addInitNextForTE(List trace, TraceExpressionInformationHolder[] expressionData, String initId,
            String nextId)
    {

        if (trace.size() > 0)
        {
            Iterator it = trace.iterator();
            SimpleTLCState currentState = (SimpleTLCState) it.next();

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
    public void addInvariantForTraceExplorer(SimpleTLCState finalState)
    {
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
    public void addStutteringPropertyForTraceExplorer(SimpleTLCState finalState)
    {
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
    public void addBackToStatePropertyForTraceExplorer(SimpleTLCState finalState, SimpleTLCState backToState)
    {
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
     * Adds the ASSUME PrintT statement and identifier for the constant expression
     * evaluation. The MC.tla file will contain:
     * 
     * const_expr_1232141234123 ==
     * expression
     * -----
     * ASSUME PrintT(<<"$!@$!@$!@$!@$!", const_expr_1232141234123>>)
     * 
     * See the comments in the method for an explanation of defining
     * an identifier.
     * 
     * @param expression
     * @param attributeName
     */
    public void addConstantExpressionEvaluation(String expression, String attributeName)
    {
        if (!((expression.trim().length()) == 0))
        {
            /*
             *  Identifier definition
             *  We define an identifier for more sensible error messages
             *  For example, if the user enters "1+" into the constant
             *  expression field and "1+" is placed as the second element
             *  of the tuple that is the argument for PrintT(), then the parse
             *  error would be something like "Encountered >>" which would be
             *  mysterious to the user. With an identifier defined, the message
             *  says "Encountered ----" which is the separator after each section in
             *  MC.tla. This error message is equally mysterious, but at least
             *  it is the same message that would appear were the same error present
             *  in another section in the model editor. We can potentially replace
             *  such messages with something more sensible in the future in the 
             *  appendError() method in TLCErrorView.
             */
            String id = ModelWriter.getValidIdentifier(CONSTANTEXPR_SCHEME);
            tlaBuffer.append(COMMENT).append("Constant expression definition ").append(ATTRIBUTE).append(attributeName)
                    .append(CR);
            tlaBuffer.append(id).append(DEFINES).append(CR).append(expression).append(CR);
            tlaBuffer.append(SEP).append(CR).append(CR);

            // ASSUME PrintT(<<"$!@$!@$!@$!@$!", const_expr_23423232>>) statement
            // The "$!@$!@$!@$!@$!" allows the toolbox to identify the
            // value of the constant expression in the TLC output
            tlaBuffer.append(COMMENT).append("Constant expression ASSUME statement ").append(ATTRIBUTE).append(
                    attributeName).append(CR);
            tlaBuffer.append("ASSUME PrintT(").append(BEGIN_TUPLE).append(CONSTANT_EXPRESSION_EVAL_IDENTIFIER).append(
                    COMMA).append(id).append(END_TUPLE).append(")").append(CR);
            tlaBuffer.append(SEP).append(CR).append(CR);
        }
    }

    /**
     * Assigns a right side to a label using an id generated from given schema
     * @param constant, constant containing the values
     * @param schema schema to generate the Id
     * @return generated id
     */
    public String addArrowAssignment(Assignment constant, String schema)
    {
        // constant instantiation
        // to .cfg : foo <- <id>
        // to _MC.tla : <id>(a, b, c)==
        // <expression>
        String id = ModelWriter.getValidIdentifier(schema);
        tlaBuffer.append(constant.getParametrizedLabel(id)).append(DEFINES).append(CR).append(constant.getRight())
                .append(CR);
        cfgBuffer.append("CONSTANT").append(CR);
        cfgBuffer.append(constant.getLabel()).append(ARROW).append(id).append(CR);
        return id;
    }

    /**
     * Creates a serial version of an MV set in both files
     * @param mvSet typed set containing the model values
     * @param comment a comment to put before the declarations, null and empty strings are OK
     */
    public void addMVTypedSet(TypedSet mvSet, String comment, String attributeName)
    {
        if (mvSet.getValueCount() != 0)
        {
            // create a declaration line
            // CONSTANTS
            // a, b, c
            if (comment != null && !(comment.length() == 0))
            {
                tlaBuffer.append(COMMENT).append(comment).append(ATTRIBUTE).append(attributeName).append(CR);
            }
            tlaBuffer.append("CONSTANTS").append(CR).append(mvSet.toStringWithoutBraces());
            tlaBuffer.append(CR).append(SEP).append(CR).append(CR);

            // create MV assignments
            // a = a
            // b = b
            // c = c
            if (comment != null && !(comment.length() == 0))
            {
                cfgBuffer.append(COMMENT).append(comment).append(CR);
            }
            cfgBuffer.append("CONSTANTS").append(CR);
            String mv;
            for (int i = 0; i < mvSet.getValueCount(); i++)
            {
                mv = mvSet.getValue(i);
                cfgBuffer.append(mv).append(EQ).append(mv).append(CR);
            }
        }
    }

    /**
     * Puts (String[])element[0] to CFG file and element[1] to TLA_MC file
     * 
     * @param elements a list of String[] elements
     * @param keyword the keyword to be used in the CFG file
     * @param attributeName the name of the attribute in the model file
     */
    public void addFormulaList(List elements, String keyword, String attributeName)
    {
        if (elements.isEmpty())
        {
            return;
        }
        cfgBuffer.append(COMMENT).append(keyword + " definition").append(CR);
        cfgBuffer.append(keyword).append(CR);

        for (int i = 0; i < elements.size(); i++)
        {
            String[] element = (String[]) elements.get(i);
            cfgBuffer.append(element[0]).append(CR);
            // when a definition in the root module is overriden as a model value
            // there is nothing to add to the MC.tla file so, we do not do the following
            if (!element[1].equals(EMPTY_STRING))
            {
                tlaBuffer.append(COMMENT).append(keyword + " definition ").append(ATTRIBUTE).append(attributeName)
                        .append(INDEX).append(i).append(CR);
                tlaBuffer.append(element[1]).append(CR).append(SEP).append(CR);
            }
        }
    }

    /**
     * New definitions are added to the _MC.tla file only
     * @param elements
     */
    public void addNewDefinitions(String definitions, String attributeName)
    {
        if (definitions.trim().length() == 0)
        {
            return;
        }
        tlaBuffer.append(COMMENT).append("New definitions ").append(ATTRIBUTE).append(attributeName).append(CR);
        tlaBuffer.append(definitions).append(CR).append(SEP).append(CR);
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
    public void addTraceExplorerExpressionInfoComments(TraceExpressionInformationHolder[] traceExpressionData)
    {
        for (int i = 0; i < traceExpressionData.length; i++)
        {
            TraceExpressionInformationHolder expressionData = traceExpressionData[i];
            tlaBuffer.append(COMMENT).append(INDEX).append(expressionData.getLevel()).append(INDEX).append(
                    expressionData.getVariableName()).append(INDEX).append(expressionData.getExpression()).append(
                    CONSTANT_EXPRESSION_EVAL_IDENTIFIER).append(CR);
        }
    }

    /**
     * Create the content for a single source element
     * @return a list with at most one String[] element
     * @throws CoreException 
     */
    public static List createSourceContent(String propertyName, String labelingScheme, ILaunchConfiguration config)
            throws CoreException
    {
        Vector result = new Vector();
        String value = config.getAttribute(propertyName, EMPTY_STRING);
        if (value.trim().length() == 0)
        {
            return result;
        }
        String identifier = getValidIdentifier(labelingScheme);
        StringBuffer buffer = new StringBuffer();

        // the identifier
        buffer.append(identifier).append(DEFINES_CR);
        buffer.append(value);

        result.add(new String[] { identifier, buffer.toString() });
        return result;
    }

    public static List createFalseInit(String var)
    {
        List list = new Vector();
        String identifier = getValidIdentifier(INIT_SCHEME);
        list.add(new String[] { identifier, identifier + DEFINES_CR + "FALSE/\\" + var + EQ + "0" });
        return list;
    }

    public static List createFalseNext(String var)
    {
        List list = new Vector();
        String identifier = getValidIdentifier(NEXT_SCHEME);
        list.add(new String[] { identifier, identifier + DEFINES_CR + "FALSE/\\" + var + PRIME + EQ + var });
        return list;
    }

    /**
     * Converts formula list to a string representation
     * @param serializedFormulaList, list of strings representing formulas (with enablement flag)
     * @param labelingScheme
     * @return
     */
    public static List createFormulaListContent(List serializedFormulaList, String labelingScheme)
    {
        List formulaList = ModelHelper.deserializeFormulaList(serializedFormulaList);
        return (createListContent(formulaList, labelingScheme));
    }

    /**
     * Create a list of overrides. If the override is not in the spec's root module, then
     * the config file will have     A <- [M] id . This means that A is defined in module M,
     * and its definition is being overriden in the spec root module which is dependent upon M.
     * The following is an example from Leslie Lamport that explains what occured before changing
     * the code and what occurs now.
     * Consider the root module

    ----------------- MODULE TestA --------------------
    M(a,b) == INSTANCE TestB WITH CB <- a, CD <- b
    ==================================================

    which imports the module

    ----------------- MODULE TestB --------------------
    CONSTANTS CB, CD

    Foo(x) == <<x, CB, CD>>
    ==================================================

    If you go to definition overrides, you'll find the option of
    overriding M!Foo.  Selecting it, the toolbox asks you to define an operator
    M!Foo of 3 arguments.  If you do it and run TLC, you get the error

    The configuration file substitutes for Foo with
    def_ov_12533499062845000 of different number of arguments.

    Here's what's going on.  The INSTANCE statement imports the operator
    M!Foo into module TestA.  As you may recall, you use that operator
    in an expression by writing something like

    M(42, "a")!F(-13)

    but in the semantic tree, it looks just as if M!F were any other
    operator with three arguments.  When TLC sees the override instruction

    Foo <- [TestB]def_ov_12533495599614000

    in the .cfg file, it tries to substitute an operator def_ov_...  with
    3 arguments for the operator Foo of module TestB that has only a
    single argument.  Hence, the error.

    ------

    Here's the fix.  Instead of giving the user the option of overriding
    M!Foo, in the menu, he should simply see Foo and, if he clicks once
    it, he should see that it's in module TestB. If he chooses to override
    Foo, he should be asked to define an operator of one argument.
    
     * @param overrides
     * @param string
     * @return
     * 
     * Was throwing null-pointer exception when called with spec unparsed.
     * Hacked a fix to handle this case.  LL 20 Sep 2009
     */
    public static List createOverridesContent(List overrides, String labelingScheme)
    {
        Vector resultContent = new Vector(overrides.size());
        String[] content;
        String id;
        Assignment formula;

        // getting the opdefnodes is necessary for retrieving the correct label
        // to appear in the cfg file as explained in the documentation for this method
        SpecObj specObj = ToolboxHandle.getCurrentSpec().getValidRootModule();
        if (specObj == null)
        {
            return resultContent;
        }
        OpDefNode[] opDefNodes = specObj.getExternalModuleTable().getRootModule().getOpDefs();
        Hashtable nodeTable = new Hashtable(opDefNodes.length);

        for (int j = 0; j < opDefNodes.length; j++)
        {
            String key = opDefNodes[j].getName().toString();
            nodeTable.put(key, opDefNodes[j]);
        }

        for (int i = 0; i < overrides.size(); i++)
        {
            id = getValidIdentifier(labelingScheme);
            // formulas
            // to .cfg : <id>
            // to _MC.tla : <id> == <expression>
            formula = ((Assignment) overrides.get(i));

            OpDefNode defNode = (OpDefNode) nodeTable.get(formula.getLabel());

            if (defNode == null)
            {
                // should raise an error
                content = null;
            } else
            {
                OpDefNode source = defNode.getSource();
                if (source == defNode)
                {
                    // user is overriding a definition in the root module
                    if (formula.isModelValue() && !formula.isSetOfModelValues())
                    {
                        // model value
                        content = new String[] { formula.getLabel() + EQ + formula.getLabel(), EMPTY_STRING };
                    } else
                    {
                        // not a model value
                        content = new String[] { formula.getLabel() + ARROW + id,
                                formula.getParametrizedLabel(id) + DEFINES_CR + formula.getRight() };
                    }
                } else if (source.getSource() == source)
                {
                    // user is overriding a definition that is not in the root module
                    if (formula.isModelValue() && !formula.isSetOfModelValues())
                    {
                        // model value
                        content = new String[] {
                                source.getName().toString() + ARROW + "["
                                        + source.getOriginallyDefinedInModuleNode().getName().toString() + "]" + id
                                        + " " + id + EQ + source.getName().toString(), "CONSTANT " + id };
                    } else
                    {
                        // not a model value
                        content = new String[] {
                                source.getName().toString() + ARROW + "["
                                        + source.getOriginallyDefinedInModuleNode().getName().toString() + "]" + id,
                                formula.getParametrizedLabel(id) + DEFINES_CR + formula.getRight() };
                    }
                } else
                {
                    // should raise an error window
                    content = null;
                }
            }

            resultContent.add(content);
        }
        return resultContent;
    }

    /**
     * Converts formula list to a string representation
     * @param formulaList list of assignments
     * @param labelingScheme 
     * @return
     */
    public static List createListContent(List formulaList, String labelingScheme)
    {
        Vector resultContent = new Vector(formulaList.size());
        String[] content;
        String label;
        for (int i = 0; i < formulaList.size(); i++)
        {
            label = getValidIdentifier(labelingScheme);
            // formulas
            // to .cfg : <id>
            // to _MC.tla : <id> == <expression>
            content = new String[] { label, label + DEFINES_CR + ((Formula) formulaList.get(i)).getFormula() };
            resultContent.add(content);
        }
        return resultContent;
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
    public static List createTraceInitContent(String traceInit, TraceExpressionInformationHolder[] traceExpressionData)
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
        Vector toReturn = new Vector();
        toReturn.add(new String[] { id, initPredicate.toString() });
        return toReturn;
    }

    public static List createTraceNextContent(List traceNextActions,
            TraceExpressionInformationHolder[] traceExpressionData)
    {
        String id = getValidIdentifier(NEXT_SCHEME);
        StringBuffer nextActionDisj = new StringBuffer();
        nextActionDisj.append(id).append(DEFINES_CR);
        Iterator it = traceNextActions.iterator();
        while (it.hasNext())
        {
            String actionConj = (String) it.next();
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

        Vector toReturn = new Vector();
        toReturn.add(new String[] { id, nextActionDisj.toString() });
        return toReturn;
    }

    /**
     * A pattern to match IDs generated by the {@link ModelWriter#getValidIdentifier(String)} method
     */
    public static final Pattern ID_MATCHER = Pattern.compile("(" + SPEC_SCHEME + "|" + INIT_SCHEME + "|" + NEXT_SCHEME
            + "|" + CONSTANT_SCHEME + "|" + SYMMETRY_SCHEME + "|" + DEFOV_SCHEME + "|" + CONSTRAINT_SCHEME + "|"
            + ACTIONCONSTRAINT_SCHEME + "|" + INVARIANT_SCHEME + "|" + PROP_SCHEME + ")_[0-9]{17,}");

    /**
     * Find the IDs in the given text and return the array of 
     * regions pointing to those or an empty array, if no IDs were found.
     * An ID is scheme_timestamp, created by {@link ModelWriter#getValidIdentifier(String)} e.G. next_125195338522638000
     * @param text text containing IDs (error text)
     * @return array of regions or empty array
     */
    static IRegion[] findIds(String text)
    {
        if (text == null || text.length() == 0)
        {
            return new IRegion[0];
        }

        Matcher matcher = ModelWriter.ID_MATCHER.matcher(text);
        Vector regions = new Vector();
        while (matcher.find())
        {
            regions.add(new Region(matcher.start(), matcher.end() - matcher.start()));
        }
        return (IRegion[]) regions.toArray(new IRegion[regions.size()]);
    }

    /**
     * Retrieves new valid (not used) identifier from given schema
     * @param schema a naming schema, one of the {@link ModelWriter} SCHEMA constants
     * @return a valid identifier
     */
    public static synchronized String getValidIdentifier(String schema)
    {
        try
        {
            Thread.sleep(10);
        } catch (InterruptedException e)
        {
        }
        return schema + "_" + System.currentTimeMillis() + 1000 * (++globalCounter);
    }

}
