package tlc2.pprint;

import org.cprover.OverlayClassImplementation;
import org.cprover.OverlayMethodImplementation;

/**
 * Skip parsing and reformatting diagnostic text during verification. The harnesses
 * do not check message layout. This overlay only bypasses the formatter;
 * surrounding callers retain their checks and exception paths.
 */
@OverlayClassImplementation
public class PrettyPrint {
	// Use a distinct signature so JBMC retains the production constructors.
	private PrettyPrint(final OverlayClassImplementation unused) {
	}

	@OverlayMethodImplementation
	public static String mypp(final String value, final int width) {
		return value;
	}
}
