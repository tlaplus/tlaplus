package tlc2.output;

import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import util.TLAConstants;

/**
 * This class which copies a TLA file, mutating it appropriately to become a SpecTE TLA file.
 */
public class TLACopier extends AbstractCopier {
	private static final String MODULE_REGEX_PREFIX = "^([-]+ " + TLAConstants.KeyWords.MODULE + ") ";
	private static final String CLOSING_BODY_REGEX = "^[=]+$";
	private static final Pattern CLOSING_BODY_PATTERN = Pattern.compile(CLOSING_BODY_REGEX);
	

	private final Pattern modulePattern;
	
	private final String initNextDefinitions;
	
	private final boolean needExtendTLC;
	private final boolean needExtendToolbox;
	
	private boolean inBody;
	
	public TLACopier(final String originalName, final String newName, final File sourceLocation,
					 final String initNextDefinitionTLA, final boolean originalExtendsTLC,
					 final boolean originalExtendsToolbox) {
		super(originalName, newName, sourceLocation);

		final String regex = MODULE_REGEX_PREFIX + originalModuleName;
		modulePattern = Pattern.compile(regex);
		
		inBody = false;
		
		initNextDefinitions = initNextDefinitionTLA;
		
		needExtendTLC = !originalExtendsTLC;
		needExtendToolbox = !originalExtendsToolbox;
	}
	
	protected String getFileExtension() {
		return TLAConstants.Files.TLA_EXTENSION;
	}

	protected void copyLine(final BufferedWriter writer, final String originalLine, final int lineNumber)
			throws IOException {
		if (!inBody) {
			final Matcher m = modulePattern.matcher(originalLine);
			final String lineToWrite;

			if (m.find()) {
				lineToWrite = m.group(1) + ' ' + newModuleName + ' ' + TLAConstants.SEP;
				inBody = true;
			} else {
				lineToWrite = originalLine;
			}

			writer.write(lineToWrite + '\n');
		} else {
			if (originalLine.trim().startsWith(TLAConstants.KeyWords.EXTENDS)) {
				String line = originalLine;
				if (needExtendTLC) {
					line += ", " + TLAConstants.BuiltInModules.TLC;
				}
				if (needExtendToolbox) {
					line += ", " + TLAConstants.BuiltInModules.TRACE_EXPRESSIONS;
				}
				writer.write(line + '\n');
			} else {
				final Matcher m = CLOSING_BODY_PATTERN.matcher(originalLine);

				if (m.matches()) {
					writer.write(initNextDefinitions + '\n');
				}

				writer.write(originalLine + '\n');
			}
		}
	}
}
