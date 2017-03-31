package org.lamport.tla.toolbox.tool;

import org.eclipse.core.runtime.Assert;
import org.lamport.tla.toolbox.spec.Spec;

public class SpecRenameEvent extends SpecEvent {

	private final Spec newSpec;

	public SpecRenameEvent(final Spec spec, final Spec newSpec) {
		super(spec, SpecEvent.TYPE_RENAME);
		Assert.isNotNull(newSpec);
		this.newSpec = newSpec;
	}

	public Spec getNewSpec() {
		return newSpec;
	}
}
