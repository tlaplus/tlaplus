package tla2sany.semantic;

import java.util.List;

import org.junit.Assert;
import org.junit.Test;

import tla2sany.drivers.SANY;
import tla2sany.drivers.SemanticException;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.parser.ParseException;
import tla2sany.semantic.Errors.ErrorDetails;
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
	
	private static final String MODULE_DIR = "test/tla2sany/semantic/error_corpus/";
	
	/**
	 * Test warning logged when two different extended modules each contain
	 * a definition of the same name and same type (both operators).
	 */
	@Test
	public void testSymbolConflictWarning() throws ParseException, SemanticException {
		final String path = MODULE_DIR + "TestMergeContextWarning.tla";
		SpecObj spec = new SpecObj(path, null);
		SANY.frontEndInitialize();
		SANY.frontEndParse(spec, ToolIO.out);
		SANY.frontEndSemanticAnalysis(spec, ToolIO.out, true);
		Errors contextErrors = spec.getSemanticErrors();
		Assert.assertFalse(contextErrors.isFailure());
		List<ErrorDetails> actual = contextErrors.getWarningDetails();
		Assert.assertEquals(1, actual.size());
		Assert.assertEquals(ErrorCode.EXTENDED_MODULES_SYMBOL_UNIFICATION_AMBIGUITY, actual.get(0).code);
	}

	/**
	 * Test error logged when two different extended modules each contain
	 * a definition of the same name and different type (one operator, one
	 * constant).
	 */
	@Test
	public void testSymbolConflictError() throws ParseException, SemanticException {
		final String path = MODULE_DIR + "TestMergeContextError.tla";
		SpecObj spec = new SpecObj(path, null);
		SANY.frontEndInitialize();
		SANY.frontEndParse(spec, ToolIO.out);
		SANY.frontEndSemanticAnalysis(spec, ToolIO.out, true);
		Errors contextErrors = spec.getSemanticErrors();
		Assert.assertTrue(contextErrors.isFailure());
		List<ErrorDetails> actual = contextErrors.getErrorDetails();
		Assert.assertEquals(1, actual.size());
		Assert.assertEquals(ErrorCode.EXTENDED_MODULES_SYMBOL_UNIFICATION_CONFLICT, actual.get(0).code);
	}
}