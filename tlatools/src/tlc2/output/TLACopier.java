package tlc2.output;

import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.util.regex.Matcher;

import util.TLAConstants;

/**
 * This class which copies a TLA file, mutating it appropriately to become a SpecTE TLA file.
 */
public class TLACopier extends AbstractTLACopier {
	private final String initNextDefinitions;
	
	private final boolean needExtendTLC;
	private final boolean needExtendToolbox;
	
	public TLACopier(final String originalName, final String newName, final File sourceLocation,
					 final String initNextDefinitionTLA, final boolean originalExtendsTLC,
					 final boolean originalExtendsToolbox) {
		super(originalName, newName, sourceLocation);
		
		initNextDefinitions = initNextDefinitionTLA;
		
		needExtendTLC = !originalExtendsTLC;
		needExtendToolbox = !originalExtendsToolbox;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
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
