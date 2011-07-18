package org.lamport.tla.toolbox.tool;

import org.eclipse.core.runtime.Assert;
import org.lamport.tla.toolbox.spec.Spec;

public class SpecRenameEvent extends SpecEvent {

	private final String newName;

	public SpecRenameEvent(final Spec spec, final String aNewName) {
		super(spec, SpecEvent.TYPE_RENAME);
		Assert.isNotNull(aNewName);
		this.newName = aNewName;
	}

	/**
	 * @return the newName
	 */
	public String getNewName() {
		return newName;
	}
}
