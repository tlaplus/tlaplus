package tlc2.tool.impl;

import org.cprover.OverlayClassImplementation;
import org.cprover.OverlayMethodImplementation;

/**
 * Models the operator registry that {@link tlc2.module.TLC}'s static
 * initializer fills. JBMC 6.11's Hashtable model returns objects that fail the
 * cast to String, and the harnesses never look up registered names.
 */
@OverlayClassImplementation
public class TLARegistry {
	// Use a distinct signature so JBMC retains the production constructors.
	private TLARegistry(final OverlayClassImplementation unused) {
	}

	@OverlayMethodImplementation
	public static String put(final String tname, final String jname) {
		return null;
	}
}
