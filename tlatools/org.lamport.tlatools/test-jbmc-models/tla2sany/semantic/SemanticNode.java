package tla2sany.semantic;

import org.cprover.OverlayClassImplementation;
import org.cprover.OverlayMethodImplementation;

/** Skip diagnostic source rendering; semantic-node operations stay production. */
@OverlayClassImplementation
public class SemanticNode {
	// Use a distinct signature so JBMC retains the production constructors.
	private SemanticNode(final OverlayClassImplementation unused) {
	}

	@Override
	@OverlayMethodImplementation
	public String toString() {
		return "<expression>";
	}
}
