package tlc2.output;

import java.io.File;
import java.util.regex.Pattern;

import util.TLAConstants;

/**
 * The abstract superclass for classes which copy a TLA file.
 */
abstract class AbstractTLACopier extends AbstractCopier {
	protected static final String MODULE_REGEX_PREFIX = "^([-]+ " + TLAConstants.KeyWords.MODULE + ") ";

	private static final String CLOSING_BODY_REGEX = "^[=]+$";
	protected static final Pattern CLOSING_BODY_PATTERN = Pattern.compile(CLOSING_BODY_REGEX);
	

	protected final Pattern modulePattern;
	
	protected boolean inBody;
	
	AbstractTLACopier(final String originalName, final String newName, final File sourceLocation) {
		super(originalName, newName, sourceLocation);

		final String regex = MODULE_REGEX_PREFIX + originalModuleName;
		modulePattern = Pattern.compile(regex);
		
		inBody = false;
	}
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	protected String getFileExtension() {
		return TLAConstants.Files.TLA_EXTENSION;
	}
}
