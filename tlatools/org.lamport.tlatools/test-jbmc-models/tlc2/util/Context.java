package tlc2.util;

import org.cprover.OverlayClassImplementation;
import org.cprover.OverlayMethodImplementation;

/** Skip diagnostic traversal; context construction and lookup stay production. */
@OverlayClassImplementation
public class Context {
	// Use a distinct signature so JBMC retains the production constructors.
	private Context(final OverlayClassImplementation unused) {
	}

	@Override
	@OverlayMethodImplementation
	public final String toString() {
		return "<context>";
	}
}
