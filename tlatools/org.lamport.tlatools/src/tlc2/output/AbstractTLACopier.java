package tlc2.output;

import java.io.File;
import java.util.regex.Pattern;

import util.TLAConstants;

/**
 * The abstract superclass for classes which copy a TLA file.
 */
abstract class AbstractTLACopier extends AbstractCopier {
	protected static final Pattern CLOSING_BODY_PATTERN = Pattern.compile(TLAConstants.MODULE_CLOSING_REGEX);
	

	protected final Pattern modulePattern;
	
	protected boolean inBody;
	
	AbstractTLACopier(final String originalName, final String newName, final File sourceLocation) {
		super(originalName, newName, sourceLocation);

		final String regex = TLAConstants.MODULE_OPENING_PREFIX_REGEX + originalModuleName;
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
