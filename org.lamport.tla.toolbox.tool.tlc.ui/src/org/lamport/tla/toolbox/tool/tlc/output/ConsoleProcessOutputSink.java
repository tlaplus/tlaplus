package org.lamport.tla.toolbox.tool.tlc.output;

import java.io.IOException;

import org.eclipse.ui.console.IOConsoleOutputStream;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.console.ConsoleFactory;

import tlc2.output.MP;

/**
 * A sink writing to a console. In plain English, this causes the Toolbox's
 * console to show TLC's output (stdout/stderr).
 * 
 * @author Simon Zambrovski
 */
public class ConsoleProcessOutputSink implements IProcessOutputSink {

	private final IOConsoleOutputStream outputStream;

	public ConsoleProcessOutputSink() {
		this.outputStream = ConsoleFactory.getTLCConsole().newOutputStream();
	}

	@Override
	public synchronized void appendText(final String text) {
		try {
			// Remove TLC's "-tool" markers for better readability by a human.
			if (Boolean.getBoolean(ConsoleProcessOutputSink.class.getName() + ".tool")) {
				this.outputStream.write(text.getBytes());
			} else {
				final String[] lines = text.split(MP.CR);
				for (String line : lines) {
					if (!line.startsWith(MP.DELIM) && !line.trim().isEmpty()) {
						line += MP.CR;
						this.outputStream.write(line.getBytes());
					}
				}
			}
		} catch (IOException e) {
			TLCUIActivator.getDefault().logError("Error printing a console message: >" + text + "<", e);
		}
	}

	@Override
	public void initializeSink(Model model, int sinkType) {
		// No-op (The why has been lost in time).
	}

	@Override
	public void processFinished() {
		// No-op (The why has been lost in time).
	}
}
