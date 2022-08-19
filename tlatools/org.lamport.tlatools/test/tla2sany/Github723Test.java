// Copyright (c) 2022, Oracle and/or its affiliates.

package tla2sany;

import org.junit.Test;
import tla2sany.drivers.SANY;
import tlc2.tool.CommonTestCase;
import util.TestPrintStream;
import util.ToolIO;

import java.io.File;

public class Github723Test extends SANYTest {
	@Test
	public void test() {
		final TestPrintStream testPrintStream = new TestPrintStream();
		ToolIO.out = testPrintStream;

		SANY.SANYmain(new String[] { CommonTestCase.BASE_PATH + File.separator + "sany" + File.separator + "Github723.tla" });

		testPrintStream.assertSubstring("An operator must be substituted for symbol 'C', and it must have arity 1.");
	}
}
