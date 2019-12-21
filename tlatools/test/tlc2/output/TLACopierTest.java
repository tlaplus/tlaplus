package tlc2.output;

import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;

import org.junit.Assert;
import org.junit.Test;

public class TLACopierTest {
	private static final String INIT_NEXT_DEFINITIONS = "init_ldq ==\n"
			+ "	TRUE\n"
			+ "	\\/ FALSE\n"
			+ "	\n"
			+ "next_ldq ==\n"
			+ "	FALSE\n";
	private static final String ORIGINAL_SPEC = "---- MODULE MC ----\n"
			+ "EXTENDS Queens, TLC\n"
			+ "\n"
			+ "\\* CONSTANT definitions @modelParameterConstants:0N\n"
			+ "const_157376354642853000 == \n"
			+ "3\n"
			+ "----\n"
			+ "\n"
			+ "=============================================================================\n"
			+ "\\* Modification History\n"
			+ "\\* Created Thu Nov 14 12:32:26 PST 2019 by loki\n";
	private static final String NEW_SPEC_EXTENDED = "---- MODULE Spectacle ----\n"
			+ "EXTENDS Queens, TLC\n"
			+ "\n"
			+ "\\* CONSTANT definitions @modelParameterConstants:0N\n"
			+ "const_157376354642853000 == \n"
			+ "3\n"
			+ "----\n"
			+ "\n"
			+ INIT_NEXT_DEFINITIONS + "\n"
			+ "=============================================================================\n"
			+ "\\* Modification History\n"
			+ "\\* Created Thu Nov 14 12:32:26 PST 2019 by loki\n";
	private static final String NEW_SPEC_NONEXTENDED = "---- MODULE Spectacle ----\n"
			+ "EXTENDS Queens, TLC, TLC, Toolbox\n"
			+ "\n"
			+ "\\* CONSTANT definitions @modelParameterConstants:0N\n"
			+ "const_157376354642853000 == \n"
			+ "3\n"
			+ "----\n"
			+ "\n"
			+ INIT_NEXT_DEFINITIONS + "\n"
			+ "=============================================================================\n"
			+ "\\* Modification History\n"
			+ "\\* Created Thu Nov 14 12:32:26 PST 2019 by loki\n";
	
	@Test
	public void testNonExtending() throws IOException {
		final TLACopier copier = new TLACopier("MC", "Spectacle", null, INIT_NEXT_DEFINITIONS, false, false);
		final StringReader sr = new StringReader(ORIGINAL_SPEC);
		final StringWriter sw = new StringWriter();
		
		copier.copy(sr, sw);
		Assert.assertEquals(NEW_SPEC_NONEXTENDED, sw.getBuffer().toString());
	}
	
	@Test
	public void testExtending() throws IOException {
		final TLACopier copier = new TLACopier("MC", "Spectacle", null, INIT_NEXT_DEFINITIONS, true, true);
		final StringReader sr = new StringReader(ORIGINAL_SPEC);
		final StringWriter sw = new StringWriter();
		
		copier.copy(sr, sw);
		Assert.assertEquals(NEW_SPEC_EXTENDED, sw.getBuffer().toString());
	}
}
