package tlc2.output;

import org.cprover.OverlayClassImplementation;
import org.cprover.OverlayMethodImplementation;

/**
 * Replace message formatting with bounded diagnostic text. The production
 * entry points and exception constructors retain error codes and parameters;
 * checks, throwing exceptions, and message recording are not overlaid.
 */
@OverlayClassImplementation
public class MP {
	// Use a distinct signature so JBMC retains the production constructors.
	private MP(final OverlayClassImplementation unused) {
	}

	@OverlayMethodImplementation
	public synchronized static String getMessage(final int messageClass, final int messageCode,
			final String[] parameters, final boolean tool) {
		return "<diagnostic>";
	}
}
