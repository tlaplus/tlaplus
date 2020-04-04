package org.lamport.tla.toolbox.tool.tlc.model;

/**
 * TLC's coverage implementation (see tlc2.tool.coverage.CostModelCreator) only
 * supports two modes: Off and On. However, we consider On too much information
 * for novice users who are (likely) only interested in identifying spec errors
 * that leave a subset of actions permanently disabled. The Toolbox therefore
 * adds a third mode "Action" which filters TLC's output for All. This obviously
 * means that the overhead of collecting coverage in Action and On mode is
 * identical. This shouldn't matter however as novice users don't create large
 * specs anyway and the Toolbox warns users when a large spec has been
 * configured with coverage. (see
 * org.lamport.tla.toolbox.tool.tlc.output.data.CoverageUINotification)
 * Alternatively, tlc2.tool.coverage.ActionWrapper.report() could be changed to
 * omit the report of its children (line 126) to effectively create the Action
 * mode at the TLC layer. I decided against it though, because I didn't want to
 * extend the -coverage TLC parameter.
 */
public enum ModelCoverage {
	/**
	 * This was an inner-enum to the {@link Model} class, but the Eclipse IDE's
	 * syntax colorer was breaking on code that refers to inner-enums (and
	 * inner-inner-enums that were refactored out of Model's state change listener
	 * related code.)
	 */
	
	OFF,
	ACTION,
	ON;
}
