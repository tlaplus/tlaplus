package tlc2.output;

import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;

import org.junit.Assert;
import org.junit.Test;

public class CFGCopierTest {
	private static final String INIT_NEXT_CFG = "\\* INIT definition\n"
			+ "INIT\n"
			+ "init_15767838108312000\n"
			+ "\\* NEXT definition\n"
			+ "NEXT\n"
			+ "next_15767838108313000\n"
			+ "\\* Action Constraint definition\n"
			+ "ACTION_CONSTRAINT\n"
			+ "action_constr_15767838108314000\n";
	// Yes, this is an illegal CFG as it specifies both SPECIFICATION and INIT/NEXT
	private static final String ORIGINAL_CFG = "\\* CONSTANT definitions\n"
			+ "CONSTANT\n"
			+ "N <- const_157376354642853000\n"
			+ "\\* SPECIFICATION definition\n"
			+ "SPECIFICATION\n"
			+ "Spec\n"
			+ "\\* INIT definition\n"
			+ "INIT\n"
			+ "BigInit\n"
			+ "\\* NEXT definition\n"
			+ "NEXT\n"
			+ "SmallNext\n"
			+ "\\* INVARIANT definition\n"
			+ "INVARIANT\n"
			+ "TypeInvariant\n"
			+ "Invariant\n"
			+ "\\* PROPERTY definition\n"
			+ "PROPERTY\n"
			+ "Termination\n"
			+ "\\* Generated on Thu Nov 14 12:32:26 PST 2019\n";
	private static final String NEW_CFG = "\\* CONSTANT definitions\n"
			+ "CONSTANT\n"
			+ "N <- const_157376354642853000\n"
			+ "\\* INVARIANT definition\n"
			+ "INVARIANT\n"
			+ "TypeInvariant\n"
			+ "Invariant\n"
			+ "\\* PROPERTY definition\n"
			+ "PROPERTY\n"
			+ "Termination\n"
			+ "\\* Generated on Thu Nov 14 12:32:26 PST 2019\n"
			+ INIT_NEXT_CFG
			+ "\n";

	@Test
	public void testCopy() throws IOException {
		final CFGCopier copier = new CFGCopier("doesn't", "matter", null, INIT_NEXT_CFG);
		final StringReader sr = new StringReader(ORIGINAL_CFG);
		final StringWriter sw = new StringWriter();
		
		copier.copy(sr, sw);
		Assert.assertEquals(NEW_CFG, sw.getBuffer().toString());
	}
}
