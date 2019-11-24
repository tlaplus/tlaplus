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
	
	protected String getFileExtension() {
		return TLAConstants.Files.CONFIG_EXTENSION;
	}

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
					} else {
						writer.write(originalLine + '\n');
					}
				}
			}
		}
	}
	
	@Override
	protected void allInputHasBeenConsumed(final BufferedWriter writer) throws IOException {
		writer.write(initNextConfiguration + '\n');
	}
	
	
	public static void main(final String[] args) throws Exception {
		final String initNext = "INIT\ninit_abc_ldq\n\nNEXT\nnext_abc_ldq";
		final CFGCopier copier = new CFGCopier("MC", "SpecTE", new File(args[0]), initNext);
		copier.copy();
	}
}
