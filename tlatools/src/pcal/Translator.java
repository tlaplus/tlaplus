/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Simon Zambrowski - initial API and implementation
 *   Markus Alexander Kuppe - Refactoring
 ******************************************************************************/
package pcal;

import java.util.List;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import util.ToolIO;

/**
 * Launcher for the PCal Translator for running out-of-the-tool
 * @author Simon Zambrovski
 */
public class Translator
{
    private String output;

    private final String input;
    
    public Translator(final String anInput, final String[] args) {
		this.input = anInput;
		ToolIO.reset();
		ToolIO.setMode(ToolIO.TOOL);
		PcalParams.resetParams();
		PcalParams.tlaPcalMapping = new TLAtoPCalMapping();
		trans.parseAndProcessArguments(args);
    }
    
    public Translator(final String anInput, final List<String> args) {
    	this(anInput, args.toArray(new String[args.size()]));
    }

    /**
     * delegates the call to the {@link trans#main()}
     * @param args
     * @return 
     */
	public boolean translate() {
		final Vector<String> in = new Vector<String>();
		// The input .tla file might have unix or windows line ending. If we fail to
		// properly split the input (a line per array cell), the pcal translator will
		// silently fail as well.
		final String[] lines = input.split("\\r?\\n");
		for (String line : lines) {
			in.add(line);
		}
		
		final Vector<String> out = trans.runMe(in);
		if (out != null) {
			final StringBuffer buf = new StringBuffer(out.size());
			for (String line : out) {
				buf.append(line);
				// The output .tla file will use the OS's line ending which is in line with the
				// the translator's legacy behavior.
				buf.append(System.getProperty("line.separator"));
			}
			output = buf.toString();
		}
		
		return output != null && PcalParams.tlaPcalMapping != null;
	}
	
	public String getOutput() {
		return output;
	}
	
	public boolean hasChanged() {
		return !input.equals(output);
	}
	
	public TLAtoPCalMapping getMapping() {
		return PcalParams.tlaPcalMapping;
	}

    /**
     * Retrieves the errors recorded during the execution
     * @return
     */
	public List<Error> getErrors() {
		final String[] messages = ToolIO.getAllMessages();
		final Vector<Error> errorMessages = new Vector<Error>();
		for (int i = 0; i < messages.length; i++) {
			int position = messages[i].indexOf(PcalDebug.UNRECOVERABLE_ERROR);
			if (position != -1) {
				errorMessages.add(new Error(messages[i].substring(position,
						messages[i].length() - PcalDebug.ERROR_POSTFIX.length())));
			}
		}
		return errorMessages;
	}
	
	public static class Error {

		private static final String LINE = "line ";
		private static final String COLUMN = ", column ";
		
		private final String error;

		public Error(String anError) {
			this.error = anError;
		}
		
		/* (non-Javadoc)
		 * @see java.lang.Object#toString()
		 */
		public String toString() {
			return error;
		}
		
		public int[] getLocation() {
			final int lineStarts = error.indexOf(LINE);
			final int lineEnds = error.indexOf(COLUMN);
			if (lineStarts != -1 && lineEnds != -1) {
				final String line = error.substring(lineStarts + LINE.length(), lineEnds);
				/*
				 * afterColumnString is the substring of message that comes after the first
				 * occurance of ", column" in message.
				 */
				final String afterColumnString = error.substring(lineEnds + COLUMN.length());
				// match any number of white spaces followed by the first string of digits.
				final Matcher matcher = Pattern.compile("\\s*\\d+").matcher(afterColumnString);
				matcher.find();
				// the column string that should be a parsable int
				final String column = matcher.group().trim();
				
				int lineNumber = -1;
				int columnNumber = -1;
				try {
					lineNumber = Integer.parseInt(line);
				} catch (final NumberFormatException e) {
				}
				try {
					columnNumber = Integer.parseInt(column);
				} catch (final NumberFormatException e) {
				}
				return new int[] { lineNumber, columnNumber, lineNumber, columnNumber + 1 };
			}
			return new int[] { -1, -1, -1, -1 };
		}
	}
}
