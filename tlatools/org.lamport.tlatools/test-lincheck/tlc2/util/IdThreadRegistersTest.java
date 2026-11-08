package tlc2.util;

import java.util.List;

import org.jetbrains.kotlinx.lincheck.Actor;
import org.jetbrains.kotlinx.lincheck.execution.ExecutionScenario;
import org.jetbrains.lincheck.datastructures.ModelCheckingOptions;
import org.jetbrains.lincheck.datastructures.Operation;
import org.junit.Test;

import tlc2.value.IValue;
import tlc2.value.impl.IntValue;

/**
 * The registers of an IdThread, which start with four slots. TLCSet in
 * PERIODIC writes them from another thread (Simulator#setAllValues) while
 * the worker writes them too, and TLCGet("all") reads them. A write to a
 * register that the array already holds must not get lost when another
 * write grows the array at the same time.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1486
 */
public class IdThreadRegistersTest {

	private static final int LOW = 1;
	private static final int HIGH = 4;
	private static final int HIGHER = 9;

	private final IdThread thread = new IdThread(0);

	private int get(final int idx) {
		final IValue v = thread.getLocalValue(idx);
		return v == null ? -1 : ((IntValue) v).val;
	}

	@Operation
	public void setLow() {
		thread.setLocalValue(LOW, IntValue.gen(LOW));
	}

	// Grows the array to five slots.
	@Operation
	public void setHigh() {
		thread.setLocalValue(HIGH, IntValue.gen(HIGH));
	}

	// Grows the array to ten slots.
	@Operation
	public void setHigher() {
		thread.setLocalValue(HIGHER, IntValue.gen(HIGHER));
	}

	@Operation
	public int getLow() {
		return get(LOW);
	}

	@Operation
	public int getHigh() {
		return get(HIGH);
	}

	@Operation
	public int getHigher() {
		return get(HIGHER);
	}

	@Operation
	public int countAll() {
		int n = 0;
		for (final IValue v : thread.getLocalValues()) {
			if (v != null) {
				n++;
			}
		}
		return n;
	}

	@Test
	public void setLowWhileGrowing() {
		check(List.of(List.of(actor("setLow")), List.of(actor("setHigh"))));
	}

	@Test
	public void setLowWhileGrowingTwice() {
		check(List.of(List.of(actor("setLow")), List.of(actor("setHigh"), actor("setHigher"))));
	}

	@Test
	public void readWhileGrowing() {
		check(List.of(List.of(actor("setLow"), actor("setHigher")), List.of(actor("getLow"), actor("countAll"))));
	}

	/**
	 * Checks every interleaving of the given workers, after which reading each
	 * register must find every write.
	 */
	private void check(final List<List<Actor>> threads) {
		new ModelCheckingOptions()
			.addCustomScenario(new ExecutionScenario(List.of(), threads,
					List.of(actor("getLow"), actor("getHigh"), actor("getHigher"), actor("countAll")), null))
			.iterations(0)
			.invocationsPerIteration(10_000)
			.check(getClass());
	}

	private static Actor actor(final String operation) {
		try {
			return new Actor(IdThreadRegistersTest.class.getMethod(operation), List.of());
		} catch (NoSuchMethodException e) {
			throw new IllegalArgumentException(e);
		}
	}
}
