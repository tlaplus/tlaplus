package org.lamport.tla.toolbox.tool.tlc.launch;

/**
 * @author Simon Zambrovski
 */
public interface IModelConfigurationConstants extends IConfigurationConstants {
    /**
     * Comments
     */
    public static final String MODEL_COMMENTS = "modelComments";
    /**
     * number showing if one closed formula is used
     */
    public static final String MODEL_BEHAVIOR_SPEC_TYPE = "modelBehaviorSpecType";
    /**
     * formula which points behavior specification
     */
    public static final String MODEL_BEHAVIOR_CLOSED_SPECIFICATION = "modelBehaviorSpec";
    /**
     * formula which points init part of the specification
     */
    public static final String MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT = "modelBehaviorInit";
    /**
     * formula which points next part of the specification
     */
    public static final String MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT = "modelBehaviorNext";
    /**
     * formula which points fairness part of the specification
     */
    public static final String MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_FAIRNESS = "modelBehaviorFairness";
    /**
     * no specification option
     */
    public static final String MODEL_BEHAVIOR_NO_SPEC = "modelBehaviorNoSpec";
    /**
     * Variables
     */
    public static final String MODEL_BEHAVIOR_VARS = "modelBehaviorVars";

    /**
     * flag for checking deadlock
     */
    public static final String MODEL_CORRECTNESS_CHECK_DEADLOCK = "modelCorrectnessCheckDeadlock";
    /**
     * invariants list
     */
    public static final String MODEL_CORRECTNESS_INVARIANTS = "modelCorrectnessInvariants";
    /**
     * property lists
     */
    public static final String MODEL_CORRECTNESS_PROPERTIES = "modelCorrectnessProperties";

    /**
     * This property is set only if, when creating the model, the Properties
     * part should be expanded when first opened.
     */
    public static final String MODEL_PROPERTIES_EXPAND = "modelPropertiesExpand";
    /**
     * action constraints list
     */
    public static final String MODEL_PARAMETER_ACTION_CONSTRAINT = "modelParameterActionConstraint";
    /**
     * constraint 
     */
    public static final String MODEL_PARAMETER_CONSTRAINT = "modelParameterContraint";
    /**
     * constant list 
     */
    public static final String MODEL_PARAMETER_CONSTANTS = "modelParameterConstants";
    /**
     * definitions list
     */
    public static final String MODEL_PARAMETER_DEFINITIONS = "modelParameterDefinitions";
    /**
     * new definitions list
     */
    public static final String MODEL_PARAMETER_NEW_DEFINITIONS = "modelParameterNewDefinitions";
    /**
     * advanced model values not used in constant definitions
     */
    public static final String MODEL_PARAMETER_MODEL_VALUES = "modelParameterModelValues";
    /**
     * view
     */
    public static final String MODEL_PARAMETER_VIEW = "modelParameterView";
    /**
     * constant expression to be evaluated
     */
    public static final String MODEL_EXPRESSION_EVAL = "modelExpressionEval";
    /**
     * Extra modules to extended by TE.tla.
     */
    public static final String TRACE_EXPLORE_EXTENDS = "traceExploreExtends";
    
    /**
     * a bitwise OR'd value representing which of the closeable tabs should be open on a model editor opening
     */
    public static final String EDITOR_OPEN_TABS = "modelEditorOpenTabs";
    
    /**
     * values to use with the {@link #EDITOR_OPEN_TABS} attribute
     */
	public static final int EDITOR_OPEN_TAB_NONE = 0;
	public static final int EDITOR_OPEN_TAB_ADVANCED_MODEL = 1 << 1;
	public static final int EDITOR_OPEN_TAB_ADVANCED_TLC = 1 << 2;
	public static final int EDITOR_OPEN_TAB_RESULTS = 1 << 3;
    
    /**
     * an integer representing the model version - we'll probably use YYYYMMDD
     */
    public static final String MODEL_VERSION = "modelVersion";
    
    /**
     * values to use with the {@link #MODEL_VERSION} attribute
     */
    public static final int VERSION_160 = 20190710;
    // this value needn't be cemented before release, as long as kept consistently increasing during development
    public static final int VERSION_161 = 20191005;
    
}
