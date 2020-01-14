package tlc2.output;

import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import util.TLAConstants;

/**
 * This class which copies a CFG file, mutating it appropriately to become a SpecTE CFG file.
 */
public class CFGCopier extends AbstractCopier {
	private static final String SPECIFICATION_COMMENT_REGEX = "^\\\\\\* " + TLAConstants.KeyWords.SPECIFICATION + ".*$?";
	private static final Pattern SPECIFICATION_COMMENT_PATTERN = Pattern.compile(SPECIFICATION_COMMENT_REGEX);
	private static final String INIT_COMMENT_REGEX = "^\\\\\\* " + TLAConstants.KeyWords.INIT + ".*$?";
	private static final Pattern INIT_COMMENT_PATTERN = Pattern.compile(INIT_COMMENT_REGEX);
	private static final String NEXT_COMMENT_REGEX = "^\\\\\\* " + TLAConstants.KeyWords.NEXT + ".*$?";
	private static final Pattern NEXT_COMMENT_PATTERN = Pattern.compile(NEXT_COMMENT_REGEX);

	
	private boolean skipNextLine;
	
	private final String initNextConfiguration;
	
	public CFGCopier(final String originalName, final String newName, final File sourceLocation, final String initNextCFG) {
		super(originalName, newName, sourceLocation);

		skipNextLine = false;
		
		initNextConfiguration = initNextCFG;
	}
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	protected String getFileExtension() {
		return TLAConstants.Files.CONFIG_EXTENSION;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	protected void copyLine(final BufferedWriter writer, final String originalLine, final int lineNumber)
			throws IOException {
		if (skipNextLine) {
			skipNextLine = false;
			return;
		}
		
		final Matcher comment = SPECIFICATION_COMMENT_PATTERN.matcher(originalLine);
		if (!comment.matches()) {
			final Matcher init = INIT_COMMENT_PATTERN.matcher(originalLine);
			
			if (!init.matches()) {
				final Matcher next = NEXT_COMMENT_PATTERN.matcher(originalLine);
				
				if (!next.matches()) {
					final String trimmed = originalLine.trim();

					if (TLAConstants.KeyWords.SPECIFICATION.equals(trimmed)
							|| TLAConstants.KeyWords.INIT.equals(trimmed)
							|| TLAConstants.KeyWords.NEXT.equals(trimmed)) {
						skipNextLine = true;
					} else if (trimmed.startsWith(TLAConstants.KeyWords.SPECIFICATION)
								|| trimmed.startsWith(TLAConstants.KeyWords.INIT)
								|| trimmed.startsWith(TLAConstants.KeyWords.NEXT)) {
						// NO-OP - don't write since it starts with the keyword, but trimmed doesn't match
						//	the naming of the keyword-denoted-attribute is on this same line, e.g:
						//			SPECIFICATION MySpec
					} else if (!trimmed.startsWith(TLAConstants.GENERATION_TIMESTAMP_PREFIX)) {
						writer.write(originalLine + '\n');
					}
				}
			}
		}
	}
	
	@Override
	protected void allInputHasBeenConsumed(final BufferedWriter writer) throws IOException {
		writer.write(initNextConfiguration + '\n');
		writer.write(SpecWriterUtilities.getGeneratedTimeStampCommentLine().toString() + '\n');
	}
	
	
	public static void main(final String[] args) throws Exception {
		final String initNext = "INIT\ninit_abc_ldq\n\nNEXT\nnext_abc_ldq";
		final CFGCopier copier = new CFGCopier(TLAConstants.Files.MODEL_CHECK_FILE_BASENAME,
											   TLAConstants.TraceExplore.ERROR_STATES_MODULE_NAME,
											   new File(args[0]),
											   initNext);
		copier.copy();
	}
}
