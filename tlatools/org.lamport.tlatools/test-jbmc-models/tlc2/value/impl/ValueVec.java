package tlc2.value.impl;

import org.cprover.OverlayClassImplementation;
import org.cprover.OverlayMethodImplementation;

/** Skip diagnostic traversal; vector storage, indexing, and sorting stay production. */
@OverlayClassImplementation
public class ValueVec {
	// Use a distinct signature so JBMC retains the production constructors.
	private ValueVec(final OverlayClassImplementation unused) {
	}

	@Override
	@OverlayMethodImplementation
	public final String toString() {
		return "<value vector>";
	}
}
