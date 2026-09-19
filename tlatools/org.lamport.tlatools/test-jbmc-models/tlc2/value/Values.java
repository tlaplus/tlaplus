package tlc2.value;

import org.cprover.OverlayClassImplementation;
import org.cprover.OverlayMethodImplementation;

/**
 * Error-message formatting is outside the scope of the value harnesses.
 */
@OverlayClassImplementation
public class Values {
	@OverlayMethodImplementation
	private Values() {
	}

	@OverlayMethodImplementation
	public static String ppr(final String value) {
		return value;
	}

	@OverlayMethodImplementation
	public static String ppr(final IValue value) {
		return "";
	}
}
