package org.lamport.tla.toolbox.jcloud;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.io.Writer;
import java.net.URI;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.nio.file.DirectoryStream;
import java.nio.file.FileSystem;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.nio.file.StandardOpenOption;
import java.util.HashMap;
import java.util.Map;
import java.util.jar.Attributes;
import java.util.jar.Manifest;

import org.apache.commons.io.IOUtils;
import org.eclipse.core.runtime.IProgressMonitor;
import org.jclouds.io.Payload;
import org.jclouds.io.Payloads;
import org.osgi.framework.Bundle;
import org.osgi.framework.FrameworkUtil;

public class PayloadHelper {

	public static Payload appendModel2Jar(final Path modelPath, String mainClass, IProgressMonitor monitor) throws IOException {
		final Bundle bundle = FrameworkUtil.getBundle(PayloadHelper.class);
		final URL toolsURL = bundle.getEntry("files/tla2tools.jar");
		if (toolsURL == null) {
			throw new RuntimeException("No tlatools.jar and/or spec to deploy");
		}

		// Copy the tla2tools.jar to a temporary location on disk to append model files to it later
		final File tempFile = File.createTempFile("tla2tools", ".jar");
		tempFile.deleteOnExit();
		try (FileOutputStream out = new FileOutputStream(tempFile)) {
            IOUtils.copy(toolsURL.openStream(), out);
        }
		
		final Map<String, String> env = new HashMap<>(); 
		env.put("create", "true");
		final URI uri = URI.create("jar:" + tempFile.toURI());
		
		try (FileSystem fs = FileSystems.newFileSystem(uri, env)) {
			try (DirectoryStream<Path> modelDirectoryStream = Files.newDirectoryStream(modelPath, "*.{cfg,tla}")) {
				for (final Path file: modelDirectoryStream) {
			        try (Writer writer = Files.newBufferedWriter(file.getFileName(),
			        		StandardCharsets.UTF_8, StandardOpenOption.CREATE)) {
			        	final Path to = fs.getPath("/model/" + file.getFileName());
			        	Files.copy(file, to, StandardCopyOption.REPLACE_EXISTING);
			        }
				}
			}
			
			// add given class as Main-Class statement to jar's manifest
			final Path manifestPath = fs.getPath("/META-INF/", "MANIFEST.MF");
			final Manifest manifest = new Manifest(Files.newInputStream(manifestPath));
			manifest.getMainAttributes().put(Attributes.Name.MAIN_CLASS, mainClass);
			final PipedOutputStream ps = new PipedOutputStream();
	        final PipedInputStream is = new PipedInputStream(ps);
			manifest.write(ps);
			ps.close();
			Files.copy(is, manifestPath, StandardCopyOption.REPLACE_EXISTING);
		} catch (final IOException e1) {
			throw new RuntimeException("No model directory found to deploy");
		}
		
		// tla2tools.jar payload (it uses the tla2tools.jar part of this toolbox to make sure its compatible)
		Payload jarPayLoad = null;
		try {
			final InputStream openStream = new FileInputStream(tempFile);
			jarPayLoad = Payloads.newInputStreamPayload(openStream);
			// manually set length of content to prevent a NPE bug
			jarPayLoad.getContentMetadata().setContentLength(Long.valueOf(openStream.available()));
		} catch (final IOException e1) {
			throw new RuntimeException("No tlatools.jar to deploy");
		}

		return jarPayLoad;
	}
}
