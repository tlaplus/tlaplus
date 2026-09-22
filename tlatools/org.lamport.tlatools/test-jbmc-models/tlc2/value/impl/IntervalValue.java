package tlc2.value.impl;

import org.cprover.OverlayClassImplementation;
import org.cprover.OverlayMethodImplementation;

/**
 * Models {@link IntervalValue#size()} without the exact-arithmetic methods for
 * which JBMC 6.11 has no operational models. Harness paths that call this
 * method are restricted to cardinalities representable by {@code int}.
 */
@OverlayClassImplementation
public class IntervalValue {
	public int low;
	public int high;

	@OverlayMethodImplementation
	public int size() {
		if (high < low) {
			return 0;
		}
		return (int) ((long) high - (long) low + 1L);
	}
}
