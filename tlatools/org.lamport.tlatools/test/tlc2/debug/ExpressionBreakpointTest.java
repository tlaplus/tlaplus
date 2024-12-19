package tlc2.debug;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.eclipse.lsp4j.debug.EvaluateResponse;
import org.eclipse.lsp4j.debug.SetBreakpointsArguments;
import org.eclipse.lsp4j.debug.SourceBreakpoint;
import org.eclipse.lsp4j.debug.StackFrame;
import org.eclipse.lsp4j.debug.Variable;
import org.junit.Test;

import tlc2.debug.TLCStateStackFrame.DebuggerValue;
import tlc2.output.EC;
import tlc2.util.Context;
import tlc2.value.impl.BoolValue;


public class ExpressionBreakpointTest extends TLCDebuggerTestCase {

	private static final String FOLDER = "debug";
	private static final String RM = "ExpressionBreakpointTest";

	public ExpressionBreakpointTest() {
		super(RM, FOLDER, new String[] { "-config", RM + ".tla" }, EC.ExitStatus.SUCCESS);
	}

	@Test
	public void testSpec() throws Exception {
		SourceBreakpoint bp1 = createBreakpointInfo(8, 7, 1, "(m + l) > (j - k)");
		SourceBreakpoint bp2 = createBreakpointInfo(9, 1, 1, "i >= 8");
		SetBreakpointsArguments sba = createBreakpointArgument(RM, bp1, bp2);
		debugger.setBreakpoints(sba);
		StackFrame[] stackFrames = debugger.continue_();
		
		// Remove all breakpoints and run the spec to completion.
		debugger.unsetBreakpoints();
		debugger.continue_();
	}
}