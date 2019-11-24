package tlc2.input;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import tlc2.model.MCError;
import tlc2.model.MCState;
import tlc2.output.MP;

/**
 * This class provides a parser to extract error & state from an MC.out file; it also provides a public static
 * 	method which does a pretty-print dump to a provided output stream of the collected states in order.
 */
public class MCOutputParser {
	// In the current world, the 'message class' (the second number run in the regex) is only a single digit, but i
	//		specify potentially two to give room for future expansion without needing to change this code.
	private static final String START_MESSAGE_REGEX
				= MP.DELIM + MP.STARTMSG + "([0-9]{4})" + MP.COLON + "([0-9]{1,2})" + MP.SPACE + MP.DELIM;
	private static final String END_MESSAGE_REGEX = MP.DELIM + MP.ENDMSG + "[0-9]{4}" + MP.SPACE + MP.DELIM;
	private static final Pattern START_MESSAGE_PATTERN = Pattern.compile(START_MESSAGE_REGEX);
	private static final Pattern END_MESSAGE_PATTERN = Pattern.compile(END_MESSAGE_REGEX);


	private final File mcOutFile;

	private MCError error;
	
	MCOutputParser(final File outFile) {
		mcOutFile = outFile;
	}
	
	MCError getError() {
		return error;
	}

	List<MCOutputMessage> parse(final boolean returnAllMessages) throws IOException {
		final ArrayList<MCOutputMessage> encounteredMessages = returnAllMessages ? new ArrayList<>() : null;
		
		try (final BufferedReader br = new BufferedReader(new FileReader(mcOutFile))) {
			MCOutputMessage message;
			MCError currentError = null;
			
			while ((message = parseChunk(br)) != null) {
				if (returnAllMessages) {
					encounteredMessages.add(message);
				}

				// TODO unclear how - if - nested errors can occur; there is support for them in TLCError
				//			which has [therefore] been mirrored in MCError
				if (message.getType() == MP.ERROR) {
					if (error == null) {
						error = new MCError(null, message.getBody());
						currentError = error;
					} else {
						currentError = new MCError((currentError != null) ? currentError : error, message.getBody());
					}
					
					message = parseChunk(br);
					if ((message == null) || (message.getType() != MP.ERROR)) {
						throw new IOException("Expected a useless error message like "
												+ "'The behavior up to this point is...' but didn't find one after"
												+ "[" + currentError.getMessage() + "]");
					}
					
					boolean inStateTrace = true;
					while (inStateTrace) {
						message = parseChunk(br);
						if (message == null) {
							throw new IOException("Unexpected end of the log during state consumption for "
													+ "[" + currentError.getMessage() + "]");
						}
						
						if (message.getType() == MP.STATE) {
							currentError.addState(MCState.parseState(message.getBody()));
						} else {
							inStateTrace = false;
							// TODO do we want to process this message?
						}
					}
				}
			}
		}

		return encounteredMessages;
	}

	/**
	 * The reader is assumed to be parked at a line containing a start message; if
	 * not, lines will be consumed until one is found, and then the ensuing chunk
	 * is consumed.
	 * 
	 * @param reader
	 * @return a consumed message, or null if a new chunk could not be encountered
	 * @throws IOException on a read error, or, if in an attempt to consume the next
	 *                     chunk, we're unable to find the end of the chunk
	 */
	private MCOutputMessage parseChunk(final BufferedReader reader) throws IOException {
		MCOutputMessage message = null;
		String startLine = null;
		while (startLine == null) {
			final String line = reader.readLine();
			
			if (line == null) {
				return null;
			}
			
			final Matcher m = START_MESSAGE_PATTERN.matcher(line);
			if (m.find()) {
				message = new MCOutputMessage(Integer.parseInt(m.group(1)), Integer.parseInt(m.group(2)));
				startLine = line;
			}
		}
		
		boolean chunkEndEncountered = false;
		final StringBuilder sb = new StringBuilder();
		while (!chunkEndEncountered) {
			final String line = reader.readLine();
			
			if (line == null) {
				throw new IOException(
						"Could not find the end of the message chunk which began with [" + startLine.trim() + "]");
			}
			
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
		}
		
		return message;
	}
	
	
	private static String getPrettyPrintForState(final MCState state) {
		if (state.isStuttering()) {
			return "<Stuttering>";
		} else if (state.isBackToState()) {
			return "<Back to state " + state.getStateNumber() + ">";
		}
		return state.getLabel();
	}
	
	/**
	 * @param os an output stream to send the 'pretty printed' trace to, or a
	 *              notification if the output file contains no error-state
	 *              messages.
	 * @param mcOut
	 * @throws IOException
	 */
	public static void prettyPrintToStream(final OutputStream os, final File mcOut) throws IOException {
		final MCOutputParser parser = new MCOutputParser(mcOut);
		parser.parse(false);
		
		final PrintStream ps;
		if (os instanceof PrintStream) {
			ps = (PrintStream)os;
		} else {
			ps = new PrintStream(os);
		}
		
		final MCError error = parser.getError();
		if (error == null) {
			ps.println("The file at " + mcOut.getAbsolutePath() + " contained no error-state messages.");
		} else {
			for (final MCState state : error.getStates()) {
				ps.println(getPrettyPrintForState(state));
				ps.println(state.getConjunctiveDescription(true, "\t"));
			}
		}
	}
}
