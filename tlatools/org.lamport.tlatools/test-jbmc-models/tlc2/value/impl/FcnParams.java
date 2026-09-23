package tlc2.value.impl;

import org.cprover.OverlayClassImplementation;
import org.cprover.OverlayMethodImplementation;

/**
 * Skip rendering parameter names and domains in function diagnostics.
 * Parameter cardinality, binding, and enumeration remain production code.
 */
@OverlayClassImplementation
public class FcnParams {
	// Use a distinct signature so JBMC retains the production constructors.
	private FcnParams(final OverlayClassImplementation unused) {
	}

	@Override
	@OverlayMethodImplementation
	public final String toString() {
		return "<function parameters>";
	}
}
