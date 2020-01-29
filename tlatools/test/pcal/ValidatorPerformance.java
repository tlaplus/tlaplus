package pcal;

import java.io.FileInputStream;
import java.io.IOException;

import org.junit.Assert;
import org.junit.Test;

import tlc2.tool.CommonTestCase;

public class ValidatorPerformance {
	private static final String SPEC_FILE = CommonTestCase.BASE_PATH + "PlusCalOptions.tla";
	
	@Test
	public void testTimings() throws IOException {
		final long trimmedStart = System.currentTimeMillis();
		for (int i = 0; i < 1000; i++) {
			try (final FileInputStream fis = new FileInputStream(SPEC_FILE)) {
				Validator.validate(fis);
			}
		}
		final long trimmedEnd = System.currentTimeMillis();

		Validator.PRE_TRIM_VALIDATION_CONTENT = false;
		final long untrimmedStart = System.currentTimeMillis();
		for (int i = 0; i < 1000; i++) {
			try (final FileInputStream fis = new FileInputStream(SPEC_FILE)) {
				Validator.validate(fis);
			}
		}
		final long untrimmedEnd = System.currentTimeMillis();

		final long trimmedDelta = trimmedEnd - trimmedStart;
		final long untrimmedDelta = untrimmedEnd - untrimmedStart;
		System.out.println("Trimmed run time was " + trimmedDelta + " and untrimmed was " + untrimmedDelta);
		Assert.assertTrue("Untrimmed processing time (" + untrimmedDelta +") ran faster than trimmed (" + trimmedDelta + ").",
						  (trimmedDelta < untrimmedDelta));
	}
}
