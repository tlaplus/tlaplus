/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
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
package org.lamport.tla.toolbox.util;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

public class ZipUtil {

	public static boolean isArchive(final String filePath) {
		final File file = new File(filePath);
		try {
			final String probeContentType = Files.probeContentType(file.toPath());
			if (probeContentType != null && probeContentType.equals("application/zip")) {
				return true;
			}
		} catch (final IOException intentionallyIgnored) {
		}
		return false;
	}

	public static File unzip(final File zipFilePath, File destDir, boolean unique) throws IOException {
		return unzip(new FileInputStream(zipFilePath), destDir, unique);
	}

	public static File unzip(final InputStream zip, File destDir, boolean unique) throws IOException {
		if (unique) {
			while (destDir.exists()) {
				// append suffix if another spec in the same directory already exists. This might append it multiple times.
				destDir = new File(destDir + "_" + System.currentTimeMillis());
			}
			destDir.mkdirs();
		}
		final ZipInputStream zipIn = new ZipInputStream(zip);

		ZipEntry entry = zipIn.getNextEntry();
		while (entry != null) {
			final String filePath = destDir + File.separator + entry.getName();
			final File file = new File(filePath);
			if (entry.isDirectory()) {
				file.mkdir();
			} else {
				if (file.getParentFile() != null && !file.getParentFile().exists()) {
					file.getParentFile().mkdirs();
				}
				// Better use Apache Commons IOUtils similar to PayloadHelper
				final BufferedOutputStream bos = new BufferedOutputStream(new FileOutputStream(file));
				final byte[] bytesIn = new byte[4096];
				int read = 0;
				while ((read = zipIn.read(bytesIn)) != -1) {
					bos.write(bytesIn, 0, read);
				}
				bos.close();
			}
			zipIn.closeEntry();
			entry = zipIn.getNextEntry();
		}
		
		zipIn.close();
		
		return destDir;
	}
}
