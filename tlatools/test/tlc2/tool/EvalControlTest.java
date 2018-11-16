package tlc2.tool;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

public class EvalControlTest {

	@Test
	public void test() {
		int control = EvalControl.Clear;

		assertFalse(EvalControl.isEnabled(control));
		assertFalse(EvalControl.isKeepLazy(control));
		assertFalse(EvalControl.isPrimed(control));

		control = EvalControl.setEnabled(control);
		assertTrue(EvalControl.isEnabled(control));
		assertFalse(EvalControl.isKeepLazy(control));
		assertFalse(EvalControl.isPrimed(control));
		
		control = EvalControl.setKeepLazy(control);
		assertTrue(EvalControl.isEnabled(control));
		assertTrue(EvalControl.isKeepLazy(control));
		assertFalse(EvalControl.isPrimed(control));

		control = EvalControl.setPrimed(control);
		assertTrue(EvalControl.isEnabled(control));
		assertTrue(EvalControl.isKeepLazy(control));
		assertTrue(EvalControl.isPrimed(control));
	}

	@Test
	public void testIfEnabled() {
		int control = EvalControl.Clear;
		
		assertFalse(EvalControl.isPrimed(EvalControl.setPrimedIfEnabled(control)));
		
		control = EvalControl.setEnabled(control);
		assertTrue(EvalControl.isEnabled(control));
		assertTrue(EvalControl.isPrimed(EvalControl.setPrimedIfEnabled(control)));
	}
}
