package tlc2.input;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import tlc2.output.MP;

abstract class AbstractMCOutputConsumer {
	private static final int MAX_READ_RETRIES = 25;
	private static final long SLEEP_BETWEEN_RETRIES = 500;
	
	// In the current world, the 'message class' (the second number run in the regex) is only a single digit, but i
	//		specify potentially two to give room for future expansion without needing to change this code.
	private static final String START_MESSAGE_REGEX
				= MP.DELIM + MP.STARTMSG + "([0-9]{4})" + MP.COLON + "([0-9]{1,2})" + MP.SPACE + MP.DELIM;
	private static final String END_MESSAGE_REGEX = MP.DELIM + MP.ENDMSG + "[0-9]{4}" + MP.SPACE + MP.DELIM;
	
	protected static final Pattern START_MESSAGE_PATTERN = Pattern.compile(START_MESSAGE_REGEX);
	protected static final Pattern END_MESSAGE_PATTERN = Pattern.compile(END_MESSAGE_REGEX);
	

	/**
	 * Subclasses may override this should they wish; via this method, they will be
	 * 	handed any line which is read and does not exist in a message block. This line
	 * 	will not be written to the output file (if a non-null writer has been supplied to
	 * 	the parseChunk(BufferedReader, BufferedWriter) method) until this method returns.
	 * 
	 * @param line
	 */
	protected void handleUnknownReadLine(final String line) throws IOException { }
	
	/**
	 * The reader is assumed to be parked at a line containing a start message; if
	 * not, lines will be consumed until one is found, and then the ensuing chunk
	 * is consumed.
	 * 
	 * @param reader
	 * @param writer if non-null, each line read will be written out through this instance
	 * @return a consumed message, or null if a new chunk could not be encountered
	 * @throws IOException on a read error, or, if in an attempt to consume the next
	 *                     chunk, we're unable to find the end of the chunk
	 */
	protected MCOutputMessage parseChunk(final BufferedReader reader, final BufferedWriter writer) throws IOException {
		MCOutputMessage message = null;
		String startLine = null;
		while (startLine == null) {
			final String line = blockingReadLine(reader, true);
			
			if (line == null) {
				return null;
			}
			
			final Matcher m = START_MESSAGE_PATTERN.matcher(line);
			if (m.find()) {
				message = new MCOutputMessage(Integer.parseInt(m.group(1)), Integer.parseInt(m.group(2)));
				startLine = line;
			} else {
				handleUnknownReadLine(line);
			}
			
			if (writer != null) {
				writer.write(line + '\n');
			}
		}
		
		boolean chunkEndEncountered = false;
		final StringBuilder sb = new StringBuilder();
		while (!chunkEndEncountered) {
			final String line = blockingReadLine(reader, false);
			final Matcher m = END_MESSAGE_PATTERN.matcher(line);
			if (m.find()) {
				message.setBody(sb);
				chunkEndEncountered = true;
			} else {
				if (sb.length() > 0) {
					sb.append(MP.CR);
				}
				sb.append(line);
			}
			
			if (writer != null) {
				writer.write(line + '\n');
			}
		}
		
		return message;
	}
	
	private String blockingReadLine(final BufferedReader reader, final boolean eofOK) throws IOException {
		int retry = 0;
		String line = reader.readLine();
		while (line == null) {
			retry++;
			
			if (retry == MAX_READ_RETRIES) {
				if (eofOK) {
					return null;
				} else {
					throw new IOException("We ran out of input unexpectedly.");
				}
			}
			
			try {
				Thread.sleep(SLEEP_BETWEEN_RETRIES);
			} catch (final Exception e) { }
			
			line = reader.readLine();
		}
		
		return line;
	}
}
