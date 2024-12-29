package tlc2.debug;

import org.eclipse.lsp4j.debug.SetBreakpointsArguments;
import org.eclipse.lsp4j.debug.SourceBreakpoint;
import org.junit.Test;
import org.junit.Assert;

import tlc2.output.EC;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.LazyValue;
import util.UniqueString;

public class ExpressionBreakpointTest extends TLCDebuggerTestCase {

	private static final String FOLDER = "debug";
	private static final String RM = "ExpressionBreakpointTest";

	public ExpressionBreakpointTest() {
		super(RM, FOLDER, new String[] { "-config", RM + ".tla" }, EC.ExitStatus.SUCCESS);
	}
	
	private static int getContextVal(TLCStackFrame frame, String var) {
		Object result = frame.getContext().lookup(s -> s.getName().equals(var));
		if (result instanceof IntValue) {
			return ((IntValue)result).val;
		} else if (result instanceof LazyValue) {
			// Evade cache guard by guessing value from small range.
			LazyValue lazy = (LazyValue)result;
			for (int i = 0; i < 20; i++) {
				if (lazy.equals(IntValue.gen(i))) {
					return i;
				}
			}
			throw new IllegalArgumentException();
		} else {
			throw new IllegalArgumentException();
		}
	}
	
	private static int getStateVal(TLCStackFrame frame, String var) {
		return ((IntValue)frame.getT().getVals().get(UniqueString.of(var))).val;
	}

	@Test
	public void testSpec() throws Exception {
		// Set breakpoint
		SourceBreakpoint bp = createBreakpointInfo(8, 5, 1, "(i + l + k) > j");
		SetBreakpointsArguments sba = createBreakpointArgument(RM, bp);
		debugger.setBreakpoints(sba);

		// Break at init
		debugger.continue_();
		
		// Break at bp
		TLCStackFrame current = (TLCStackFrame)debugger.continue_()[0];
		final int i = getStateVal(current, "i");
		final int j = 10;
		final int k = getContextVal(current, "k");
		final int l = getContextVal(current, "l");
		Assert.assertEquals(j + 1, i + l + k);
		
		// Remove all breakpoints and run the spec to completion.
		debugger.unsetBreakpoints();
		debugger.continue_();
	}
}