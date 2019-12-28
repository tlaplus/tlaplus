package tlc2.output;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Reader;
import java.io.Writer;

/**
 * This is the abstract copying class for the generation of SpecTE file assets.
 */
abstract class AbstractCopier {
	protected final String originalModuleName;
	protected final String newModuleName;

	protected final File sourceDirectory;
	
	protected File sourceFile;
	protected File destinationFile;
	
	AbstractCopier(final String originalName, final String newName, final File sourceLocation) {
		originalModuleName = originalName;
		newModuleName = newName;
		
		sourceDirectory = sourceLocation;
	}
	
	/**
	 * @return the extension including the prefixed '.'
	 */
	protected abstract String getFileExtension();

	/**
	 * @param writer
	 * @param originalLine
	 * @param lineNumber this is 1-based (e.g the first line of the file read will be lineNumber == 1)
	 * @throws IOException
	 */
	protected abstract void copyLine(final BufferedWriter writer, final String originalLine, final int lineNumber)
			throws IOException;
	
	/**
	 * Overriders will receive this notification after the final line of input has
	 * been consumed and {@link #copyLine(BufferedWriter, String, int)} has been
	 * invoked on that line.
	 */
	protected void allInputHasBeenConsumed(final BufferedWriter writer) throws IOException { }
	
	/**
	 * Overriders will receive this notification after the reader and writer
	 * instances employed in the copy haven been closed but before
	 * {@link #copy(Reader, Writer)} exits.
	 */
	protected void copyHasFinished() throws IOException { }

	/**
	 * @return null until {@link #copy()} has been invoked, thereafter the location of the destination file.
	 */
	public File getDestinationFile() {
		return destinationFile;
	}
	
	public final void copy() throws IOException {
		final String extension = getFileExtension();
		
		sourceFile = new File(sourceDirectory, (originalModuleName + extension));
		destinationFile = new File(sourceDirectory, (newModuleName + extension));
		
		copy(new FileReader(sourceFile), new FileWriter(destinationFile));
	}
	
	// This extra level of abstraction is done for unit tests
	protected void copy(final Reader reader, final Writer writer) throws IOException {
		try (final BufferedReader br = new BufferedReader(reader)) {
			try (final BufferedWriter bw = new BufferedWriter(writer)) {
				String line;
				int lineCount = 1;	// staying 1-based since Location is as well and our subclasses use Location instances
				while ((line = br.readLine()) != null) {
					copyLine(bw, line, lineCount);

					lineCount++;
				}
				
				allInputHasBeenConsumed(bw);
			}
		}
		
		copyHasFinished();
	}
}
