package util;

import org.cprover.OverlayClassImplementation;
import org.cprover.OverlayMethodImplementation;

/** Skip recursive diagnostic rendering; set operations stay production. */
@OverlayClassImplementation
public class Set {
	// Use a distinct signature so JBMC retains the production constructors.
	private Set(final OverlayClassImplementation unused) {
	}

	@Override
	@OverlayMethodImplementation
	public synchronized String toString() {
		return "<set>";
	}
}
