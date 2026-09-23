package tlc2.value.impl;

import org.cprover.OverlayClassImplementation;
import org.cprover.OverlayMethodImplementation;

/**
 * Bound diagnostic rendering before it dispatches to the value subclasses.
 * The harnesses exclude diagnostic text and rendering-induced normalization or
 * lambda evaluation. Semantic calls to those operations still use production
 * code, and callers retain their production checks and exception paths.
 */
@OverlayClassImplementation
public abstract class Value {
	// Use a distinct signature so JBMC retains the production constructors.
	private Value(final OverlayClassImplementation unused) {
	}

	@OverlayMethodImplementation
	private final String toStringImpl(final String delim, final boolean checked) {
		return "<value>";
	}
}
