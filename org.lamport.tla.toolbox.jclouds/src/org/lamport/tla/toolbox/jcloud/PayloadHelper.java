/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
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

package org.lamport.tla.toolbox.jcloud;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.net.URI;
import java.net.URL;
import java.nio.file.DirectoryStream;
import java.nio.file.FileSystem;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;
import java.util.jar.Attributes;
import java.util.jar.Manifest;

import org.apache.commons.io.IOUtils;
import org.eclipse.core.runtime.IProgressMonitor;
import org.jclouds.io.Payload;
import org.jclouds.io.Payloads;
import org.osgi.framework.Bundle;
import org.osgi.framework.FrameworkUtil;

public class PayloadHelper {

	public static Payload appendModel2Jar(final Path modelPath, String mainClass, Properties properties, IProgressMonitor monitor) throws IOException {
		monitor.subTask("Tweaking tla2tools.jar to contain the spec & model");
		
		/*
		 * Get the standard tla2tools.jar from the classpath as a blueprint.
		 * It's located in the org.lamport.tla.toolbox.jclouds bundle in the
		 * files/ directory. It uses OSGi functionality to read files/tla2tools.jar
		 * from the .jclouds bundle.
		 * The copy of the blueprint will contain the spec & model and 
		 * additional metadata (properties, amended manifest).
		 */
		final Bundle bundle = FrameworkUtil.getBundle(PayloadHelper.class);
		final URL toolsURL = bundle.getEntry("files/tla2tools.jar");
		if (toolsURL == null) {
			throw new RuntimeException("No tlatools.jar and/or spec to deploy");
		}

		/* 
		 * Copy the tla2tools.jar blueprint to a temporary location on
		 * disk to append model files below.
		 */
		final File tempFile = File.createTempFile("tla2tools", ".jar");
		tempFile.deleteOnExit();
		try (FileOutputStream out = new FileOutputStream(tempFile)) {
            IOUtils.copy(toolsURL.openStream(), out);
        }
		
		/*
		 * Create a virtual filesystem in jar format.
		 */
		final Map<String, String> env = new HashMap<>(); 
		env.put("create", "true");
		final URI uri = URI.create("jar:" + tempFile.toURI());
		
		try (FileSystem fs = FileSystems.newFileSystem(uri, env)) {
			/*
			 * Copy the spec and model into the jar's model/ folder.
			 */
			try (DirectoryStream<Path> modelDirectoryStream = Files.newDirectoryStream(modelPath, "*.{cfg,tla}")) {
				for (final Path file: modelDirectoryStream) {
		        	final Path to = fs.getPath("/model/" + file.getFileName());
		        	Files.copy(file, to, StandardCopyOption.REPLACE_EXISTING);
				}
			}
			
			/*
			 * Add given class as Main-Class statement to jar's manifest. This
			 * causes Java to launch this class when no other Main class is 
			 * given on the command line. Thus, it shortens the command line
			 * for us.
			 */
			final Path manifestPath = fs.getPath("/META-INF/", "MANIFEST.MF");
			final Manifest manifest = new Manifest(Files.newInputStream(manifestPath));
			manifest.getMainAttributes().put(Attributes.Name.MAIN_CLASS, mainClass);
			final PipedOutputStream ps = new PipedOutputStream();
	        final PipedInputStream is = new PipedInputStream(ps);
			manifest.write(ps);
			ps.close();
			Files.copy(is, manifestPath, StandardCopyOption.REPLACE_EXISTING);
			
			/*
			 * Add properties file to archive. The property file contains the
			 * result email address... from where TLC eventually reads it.
			 */

			// On Windows 7 and above the file has to be created in the system's
			// temp folder. Otherwise except file creation to fail with a
			// AccessDeniedException
			final File f = File.createTempFile("generated", "properties");
            OutputStream out = new FileOutputStream(f);
            // Append all entries in "properties" to the temp file f
            properties.store(out, "This is an optional header comment string");
            // Copy the temp file f into the jar with path /model/generated.properties.
        	final Path to = fs.getPath("/model/generated.properties");
        	Files.copy(f.toPath(), to, StandardCopyOption.REPLACE_EXISTING);
		} catch (final IOException e1) {
			throw new RuntimeException("No model directory found to deploy");
		}
		
		/*
		 * Convert the customized tla2tools.jar into a jClouds payload object. This
		 * is the format it will be transfered on the wire. This is handled by 
		 * jClouds though.
		 */
		Payload jarPayLoad = null;
		try {
			final InputStream openStream = new FileInputStream(tempFile);
			jarPayLoad = Payloads.newInputStreamPayload(openStream);
			// manually set length of content to prevent a NPE bug
			jarPayLoad.getContentMetadata().setContentLength(Long.valueOf(openStream.available()));
		} catch (final IOException e1) {
			throw new RuntimeException("No tlatools.jar to deploy");
		} finally {
			monitor.worked(5);
		}

		return jarPayLoad;
	}
}
