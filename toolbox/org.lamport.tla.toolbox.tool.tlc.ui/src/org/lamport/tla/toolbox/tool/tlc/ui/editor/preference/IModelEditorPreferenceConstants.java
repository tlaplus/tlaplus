package org.lamport.tla.toolbox.tool.tlc.ui.editor.preference;

public interface IModelEditorPreferenceConstants {
	/**
	 * If set, the Evaluate Constant Expressions section of the Results page will be shown in its own model editor tab.
	 */
	public static final String I_MODEL_EDITOR_SHOW_ECE_AS_TAB = "showECEAsTab";

	/**
	 * The preference defining how the user would prefer to see overridden definitions displayed.
	 */
	public static final String I_OVERRIDDEN_DEFINITION_STYLE = "definitionOverrideStyle";
	/**
	 * The style of "Definition [Module Name]"
	 */
	public static final String I_OVERRIDDEN_DEFINITION_STYLE_MODULE_NAME = "byModuleName";
	/**
	 * The style of "InstanceVariableName!Definition" where there is a declaration in the code like:
	 * 		InstanceVariableName == INSTANCE ModuleName WITH ...
	 */
	public static final String I_OVERRIDDEN_DEFINITION_STYLE_INSTANCE_NAME = "byInstanceName";
}
