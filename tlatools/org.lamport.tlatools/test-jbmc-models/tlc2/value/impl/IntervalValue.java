package tlc2.value.impl;

import org.cprover.OverlayClassImplementation;
import org.cprover.OverlayMethodImplementation;

/**
 * Models {@link IntervalValue#size()} for singleton intervals. JBMC 6.11 has
 * no operational models for the exact-arithmetic methods used by the
 * production implementation. Every analyzed interval is {@code value..value},
 * so this replacement is exact on every reachable harness path.
 */
@OverlayClassImplementation
public class IntervalValue {
	@OverlayMethodImplementation
	public int size() {
		return 1;
	}
}
