package tla2sany.semantic;

import org.junit.Assert;
import org.junit.Test;

import tla2sany.drivers.InitException;
import tla2sany.drivers.SANY;
import tla2sany.drivers.SemanticException;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.parser.ParseException;
import tlc2.tool.CommonTestCase;
import util.ToolIO;

/**
 * This class contains tests to ensure symbol conflict errors in
 * {@link Context#mergeExtendContext(Context)} are captured appropriately;
 * comments in various places indicate these errors were being lost in the
 * past and special code was necessary to surface them.
 *
 * The reason the errors were getting lost is because the {@link Context}
 * class kept a {@link Errors} instance around and reported the errors there.
 * This was outside usual error reporting channels. It would be better to
 * report the error through ordinary semantic analysis error channels, so
 * this class is intended to isolate this error reporting behavior for the
 * purposes of changing it and ensuring it is captured in a different path.
 */
public class TestMergeContextError {
	
	private static final String MODULE_DIR = CommonTestCase.BASE_PATH + "/tla2sany/semantic/";
	
	/**
	 * Test warning logged when two different extended modules each contain
	 * a definition of the same name and same type (both operators).
	 */
	@Test
	public void testSymbolConflictWarning() throws InitException, ParseException, SemanticException {
		final String path = MODULE_DIR + "TestMergeContextWarning.tla";
		SpecObj spec = new SpecObj(path, null);
		SANY.frontEndInitialize(spec, ToolIO.out);
		SANY.frontEndParse(spec, ToolIO.out);
		SANY.frontEndSemanticAnalysis(spec, ToolIO.out, true);
		Context context = spec.getExternalModuleTable().getContextForRootModule();
		Errors contextErrors = context.getErrors();
		Assert.assertFalse(contextErrors.isFailure());
		Assert.assertEquals(1, contextErrors.getWarnings().length);
		Assert.assertEquals(contextErrors, spec.getGlobalContextErrors());
	}

	/**
	 * Test error logged when two different extended modules each contain
	 * a definition of the same name and different type (one operator, one
	 * constant).
	 */
	@Test
	public void testSymbolConflictError() throws InitException, ParseException, SemanticException {
		final String path = MODULE_DIR + "TestMergeContextError.tla";
		SpecObj spec = new SpecObj(path, null);
		SANY.frontEndInitialize(spec, ToolIO.out);
		SANY.frontEndParse(spec, ToolIO.out);
		SANY.frontEndSemanticAnalysis(spec, ToolIO.out, true);
		Context context = spec.getExternalModuleTable().getContextForRootModule();
		Errors contextErrors = context.getErrors();
		Assert.assertTrue(contextErrors.isFailure());
		Assert.assertEquals(1, contextErrors.getErrors().length);
		Assert.assertEquals(contextErrors, spec.getGlobalContextErrors());
	}
}