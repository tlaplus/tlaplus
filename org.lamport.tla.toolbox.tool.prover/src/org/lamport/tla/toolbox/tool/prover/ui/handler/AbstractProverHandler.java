package org.lamport.tla.toolbox.tool.prover.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.IParseConstants;
import org.lamport.tla.toolbox.tool.prover.ui.util.TLAPMExecutableLocator;

/**
 * All of our prover handlers have the same {@link #setEnabled(Object)} logic, so we abstract it out here.
 */
public abstract class AbstractProverHandler extends AbstractHandler {
	/**
	 * The handler is enabled if there is a TLA editor with focus, a TLAPM executable exists, and the spec
	 * 	has been parsed successfully.
	 */
	public void setEnabled(Object context) {
		final TLAPMExecutableLocator locator = TLAPMExecutableLocator.INSTANCE;
		final Spec spec = Activator.getSpecManager().getSpecLoaded();

		setBaseEnabled((EditorUtil.getTLAEditorWithFocus() != null) && locator.tlapmDoesExist()
				&& (spec.getStatus() == IParseConstants.PARSED));
	}
}
