// Copyright (c) 2023, 2025, Oracle and/or its affiliates.

package util;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertEquals;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import org.junit.Test;
import tla2sany.semantic.StandardModules;
import tlc2.tool.impl.Tool;

public class SimpleFilenameToStreamTest {

	private void checkResolveStandardModule(FilenameToStream resolver, String path, boolean isModule) {
		File file = resolver.resolve(path, isModule);
		assertNotNull("resolve(" + path + ", " + isModule + ") should not be null", file);
		assertTrue("resolve(" + path + ", " + isModule + ") = " + file.getAbsolutePath() + " does not exist!", file.exists());
		assertTrue("resolve(" + path + ", " + isModule + ") = " + file + " should be a standard module but isn't!", resolver.isStandardModule(path));
	}

	/**
	 * Try various ways of resolving all the standard modules
	 */
	@Test
	public void testResolveStandardModules() {
		final SimpleFilenameToStream sfts = new SimpleFilenameToStream();
		for (String name : new String[] {
				"Bags", "FiniteSets", "Integers", "Json", "Naturals", "Randomization",
				"Reals", "RealTime", "Sequences", "TLC", "TLCExt", "Toolbox" }) {
			checkResolveStandardModule(sfts, name, true);
			checkResolveStandardModule(sfts, name + ".tla", true);
			checkResolveStandardModule(sfts, name + ".tla", false);

			// NOTE 2023/11/1: Ideally this next check would be valid, but it so happens that nothing in the current
			// implementation actually prevents the returned value from resolving to some arbitrary thing (like a
			// subdirectory of the current working directory).  The problem is worse on case-insensitive filesystems
			// like the MacOS default.  We should re-enable this check once the implementation is more robust.
			// assertFalse("Resolution with isModule=false should fail", sfts.resolve(name, false).exists());
		}
	}

	/**
	 * Try various ways of resolving a few of the community modules.
	 * For historical reasons these are considered standard modules as well.
	 */
	@Test
	public void testResolveCommunityModules() {
		final SimpleFilenameToStream sfts = new SimpleFilenameToStream();
		for (String name : new String[] { "Bitwise", "CSV", "IOUtils", "VectorClocks" }) {
			checkResolveStandardModule(sfts, name, true);
			checkResolveStandardModule(sfts, name + ".tla", true);
			checkResolveStandardModule(sfts, name + ".tla", false);

			// See NOTE 2023/11/1 above.
			// assertFalse("Resolution with isModule=false should fail", sfts.resolve(name, false).exists());
		}
	}

	/**
	 * Test if we can resolve files by absolute path
	 */
	@Test
	public void testResolveByAbsolutePath() throws IOException {
		Path tmpdir = null;
		try {
			tmpdir = Files.createTempDirectory(null);
			Path modulePath = tmpdir.resolve("MyModule.tla");
			Files.writeString(modulePath, "", StandardCharsets.US_ASCII);
			assertTrue("Resolver should be able to find modules by absolute path, even when it isn't a library path",
					new SimpleFilenameToStream().resolve(modulePath.toAbsolutePath().toString(), true).exists());
		} finally {
			if (tmpdir != null) {
				FileUtil.deleteDir(tmpdir.toFile(), true);
			}
		}
	}

	/**
	 * Test if we can resolve modules from {@link ToolIO#getUserDir()}
	 */
	@Test
	public void testResolveFromUserDir() throws IOException  {
		// Save the old value so we can restore it at the end of the test
		String oldUserDir = ToolIO.getUserDir();

		// We'll try to delete these at the end of the test
		Path d1 = null;
		Path d2 = null;

		try {
			d1 = Files.createTempDirectory(null);
			d2 = Files.createTempDirectory(null);

			ToolIO.setUserDir(d1.toString());
			File f1 = new SimpleFilenameToStream().resolve("MyModule", true);
			assertFalse("Resolver should not find nonexistent module MyModule", f1.exists());

			// Create MyModule.tla
			Files.writeString(d1.resolve("MyModule.tla"), "", StandardCharsets.US_ASCII);

			File f2 = new SimpleFilenameToStream().resolve("MyModule", true);
			assertTrue("Resolver should find MyModule even though it is empty", f2.exists());
			assertFalse("Module from userDir is not a standard module", new SimpleFilenameToStream().isStandardModule("MyModule"));

			ToolIO.setUserDir(d2.toString());
			File f3 = new SimpleFilenameToStream().resolve("MyModule", true);
			assertFalse("Resolver should not find MyModule in different directory", f3.exists());

			// Create subdir/MyModule.tla
			Path d2subdir = d2.resolve("subdir");
			Files.createDirectory(d2subdir);
			Files.writeString(d2subdir.resolve("MyModule.tla"), "", StandardCharsets.US_ASCII);

			File f4 = new SimpleFilenameToStream().resolve("MyModule", true);
			assertFalse("Resolver should not find MyModule in subdirectory", f4.exists());

			File f5 = new SimpleFilenameToStream().resolve("subdir/MyModule", true);
			assertTrue("Resolver should find MyModule in subdirectory", f5.exists());

			File f6 = new SimpleFilenameToStream().resolve("subdir/MyModule.tla", true);
			assertTrue("Resolver should find MyModule.tla in subdirectory", f6.exists());

			File f7 = new SimpleFilenameToStream().resolve("subdir/MyModule", false);
			assertFalse("Resolver should not find non-module MyModule in subdirectory", f7.exists());

			File f8 = new SimpleFilenameToStream().resolve("subdir/MyModule.tla", false);
			assertTrue("Resolver should find MyModule.tla in subdirectory", f8.exists());
		} finally {
			ToolIO.setUserDir(oldUserDir);
			try {
				if (d1 != null) {
					FileUtil.deleteDir(d1.toFile(), true);
				}
			} finally {
				if (d2 != null) {
					FileUtil.deleteDir(d2.toFile(), true);
				}
			}
		}
	}

	/**
	 * Test that the library path constructor argument behaves as expected
	 */
	@Test
	public void testResolveWithCustomLibraryPath() throws IOException  {
		// Save the old value so we can restore it at the end of the test
		String oldUserDir = ToolIO.getUserDir();

		// We'll try to delete these at the end of the test
		Path d1 = null;
		Path d2 = null;

		try {
			d1 = Files.createTempDirectory(null);
			d2 = Files.createTempDirectory(null);

			FilenameToStream resolver = new SimpleFilenameToStream(d1.toString());

			File f1 = resolver.resolve("Integers", true);
			assertTrue("Resolver should still find Integers when library path is empty", f1.exists());
			assertTrue("Integers is a standard module", resolver.isStandardModule("Integers"));

			Files.writeString(d1.resolve("MyModule.tla"), "", StandardCharsets.US_ASCII);
			Files.writeString(d2.resolve("MyModule.tla"), "", StandardCharsets.US_ASCII);

			File f2 = resolver.resolve("MyModule", true);
			assertTrue("Resolver should find modules in explicit library dir", f2.exists());
			assertFalse("Modules in explicit library dir are not library modules", resolver.isStandardModule("MyModule"));
			assertTrue("Integers is a standard module, even a custom library path", resolver.isStandardModule("Integers"));

			ToolIO.setUserDir(d2.toString());

			resolver = new SimpleFilenameToStream(d1.toString());
			File f3 = resolver.resolve("MyModule", true);
			assertTrue("Resolver should prefer userDir over library dir", f3.toString().startsWith(d2.toString()));
		} finally {
			ToolIO.setUserDir(oldUserDir);
			try {
				if (d1 != null) {
					FileUtil.deleteDir(d1.toFile(), true);
				}
			} finally {
				if (d2 != null) {
					FileUtil.deleteDir(d2.toFile(), true);
				}
			}
		}
	}

	/**
	 * Test that the resolver handles the TLA_LIBRARY system property as expected
	 */
	@Test
	public void testTLALibrarySystemProperty() throws IOException  {
		// Save the old value so we can restore it at the end of the test
		String oldTLALibrary = System.getProperty(SimpleFilenameToStream.TLA_LIBRARY);

		// We'll try to delete these at the end of the test
		Path d1 = null;
		Path d2 = null;

		try {
			d1 = Files.createTempDirectory(null);
			d2 = Files.createTempDirectory(null);

			FilenameToStream resolver = new SimpleFilenameToStream();

			System.setProperty(SimpleFilenameToStream.TLA_LIBRARY, d1.toString());
			File f1 = resolver.resolve("Integers", true);
			assertTrue("Resolver should still find Integers when library path is empty", f1.exists());
			assertTrue("Integers is a standard module, even with TLA_LIBRARY set", resolver.isStandardModule("Integers"));

			Files.writeString(d1.resolve("MyModule.tla"), "", StandardCharsets.US_ASCII);

			resolver = new SimpleFilenameToStream();
			File f2 = resolver.resolve("MyModule", true);
			assertTrue("Resolver should find modules in TLA_LIBRARY", f2.exists());
			assertFalse("Modules in TLA_LIBRARY are not library modules", resolver.isStandardModule("MyModule"));

			// TODO: is this next check actually desirable?  Because of this choice:
			//    - When TLC is invoked on a module like "MyModule.tla", it will also use the TLA_LIBRARY system
			//      property.
			//    - But, when TLC is invoked on a module like "some-dir/MyModule.tla", it will NOT use the TLA_LIBRARY
			//      system property.
			resolver = new SimpleFilenameToStream(d2.toString());
			File f3 = resolver.resolve("MyModule", true);
			assertFalse("Resolver should ignore TLA_LIBRARY system property if an explicit path was given", f3.exists());
		} finally {
			if (oldTLALibrary != null) {
				System.setProperty(SimpleFilenameToStream.TLA_LIBRARY, oldTLALibrary);
			} else {
				System.clearProperty(SimpleFilenameToStream.TLA_LIBRARY);
			}
			try {
				if (d1 != null) {
					FileUtil.deleteDir(d1.toFile(), true);
				}
			} finally {
				if (d2 != null) {
					FileUtil.deleteDir(d2.toFile(), true);
				}
			}
		}
	}

	/**
	 * Test whether the fix for #424 still works
	 */
	@Test
	public void testWindowsTLAFileCreation() {
		if (System.getProperty("os.name").toLowerCase().indexOf("win") > -1) {
			final String driveLetter = "X:";
			final String parentDirectory = driveLetter + "\\Develop\\myspecs\\DecentSpec\\";
			final String child = parentDirectory + "Fromage.tla";
			final FilenameToStream.TLAFile file = new FilenameToStream.TLAFile(parentDirectory, child, null);
			final int driveLetterCount = file.getAbsolutePath().split(driveLetter).length - 1;
			
			assertTrue("There should be 1 drive letter in the child's absolute path, but there are " + driveLetterCount,
					   (1 == driveLetterCount));
		}
	}

	/**
	 * Test whether the fix for <a href="https://github.com/tlaplus/tlaplus/issues/545">#545</a> still works
	 */
	@Test
	public void testBizarreWorkingDirectorySearchBehavior() throws IOException {
		String oldCWD = System.getProperty("user.dir");
		String oldUserDir = ToolIO.getUserDir();

		Path tmpdir = null;
		try {
			tmpdir = Files.createTempDirectory(null);

			// NOTE: Java does not have chdir() (https://bugs.openjdk.org/browse/JDK-4045688), but
			// we can fake it because SimpleFilenameToStream uses the user.dir system property.
			System.setProperty("user.dir", tmpdir.toString());

			Files.writeString(tmpdir.resolve("Test.tla"), "", StandardCharsets.US_ASCII);
			Files.writeString(tmpdir.resolve("Test.cfg"), "", StandardCharsets.US_ASCII);

			Path subdir = tmpdir.resolve("test");
			Files.createDirectory(subdir);
			Files.writeString(subdir.resolve("Test.tla"), "", StandardCharsets.US_ASCII);
			Files.writeString(subdir.resolve("Test.cfg"), "", StandardCharsets.US_ASCII);

			FilenameToStream resolver = new SimpleFilenameToStream();
			assertEquals("Resolver should not find modules in CWD ahead of named subdirectories",
					resolver.resolve("test" + File.separator + "Test.tla", true).getAbsolutePath(),
					tmpdir.resolve("test" + File.separator + "Test.tla").toAbsolutePath().toString());
		} finally {
			ToolIO.setUserDir(oldUserDir);
			if (oldCWD != null) {
				System.setProperty(SimpleFilenameToStream.TLA_LIBRARY, oldCWD);
			} else {
				System.clearProperty(SimpleFilenameToStream.TLA_LIBRARY);
			}
			if (tmpdir != null) {
				FileUtil.deleteDir(tmpdir.toFile(), true);
			}
		}
	}
	
}
