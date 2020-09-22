/*******************************************************************************
 * Copyright (c) 2020 Microsoft Research. All rights reserved. 
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
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package util;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.nio.charset.Charset;

public class MonolithSpecExtractor {

	public static String getConfig(final String configFile) {
		if (configFile.endsWith(TLAConstants.Files.TLA_EXTENSION)) {
			return configFile;
		}
		return configFile + TLAConstants.Files.CONFIG_EXTENSION;
	}
	
	// config and module are almost identical except for what they return.
	// The config is a plain (Java) InputStream, but the module has to be a
	// TLA+ *NamedInputStream*, which is a wrapper and not a subclass of
	// InputStream. Method config also filters out the config start and end markers
	// while module keeps them. Other than that, they both loop over the input line
	// by line and extract the lines in between the start and end marker.
	
	public static InputStream config(final InputStream in, final String configName) throws IOException {
		try (BufferedReader reader = new BufferedReader(new InputStreamReader(in))) {
			String config = "";

			String line = "";
			while ((line = reader.readLine()) != null) {
				if (!config.isEmpty() && line.matches("====.*")) {
					break;
				}
				if (config.isEmpty() && line.matches("-----*\\s*CONFIG\\s+" + configName + "\\s*-----*")) {
					config += " "; // activate.
					continue; // skip to next line/don't include marker.
				}
				if (!config.isEmpty()) {
					config += line + "\n";
				}
			}
			return new ByteArrayInputStream(config.trim().getBytes(Charset.forName("UTF-8")));
		}
	}
	
	public static NamedInputStream module(final File in, final String moduleName)
			throws IOException {
		final File out = FileUtil.createTempFile(moduleName + TLAConstants.Files.TLA_EXTENSION);
		final PrintWriter pw = new PrintWriter(new FileWriter(out));
		try (BufferedReader reader = new BufferedReader(new FileReader(in))) {
			boolean active = false;

			String line = "";
			while ((line = reader.readLine()) != null) {
				if (active && line.matches("====.*")) {
					pw.println(line); // include end marker.
					break;
				}
				if (!active && line.matches("-----*\\s*MODULE\\s+" + moduleName + "\\s*----*")) {
					active = true;
					pw.println(line); // include start marker.
					continue;
				}
				if (active) {
					pw.println(line);
				}
			}
			pw.close();
			if (!active) {
				// Not found in uber-spec.
				return null;
			}
			return new NamedInputStream(out.getName(), moduleName, out);
		}
	}
}
