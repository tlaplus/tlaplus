package util;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.stream.Collectors;

import org.junit.Test;

public class MonolithSpecExtractorTest {

	private static final String MONOLITH_SPEC = "D:\\software\\TLA+\\Specs\\Scratch\\Scratch.tla\n" + "\n" + "\n"
			+ "---- MODULE Scratch ----\n" + "EXTENDS TLC\n" + "Spec == TRUE /\\ [][TRUE]_TRUE\n" + "======\n" + "\n"
			+ "---- CONFIG Scratch ----\n" + "SPECIFICATION Spec\n" + "=====\n";

	@Test
	public void testExtractConfig() throws IOException {
		final InputStream in = new ByteArrayInputStream(MONOLITH_SPEC.getBytes(StandardCharsets.UTF_8));
		final InputStream configStream = MonolithSpecExtractor.config(in, "Scratch");

		@SuppressWarnings("resource")
		final String config = new BufferedReader(new InputStreamReader(configStream, StandardCharsets.UTF_8)).lines()
				.collect(Collectors.joining("\n"));
		assertEquals("SPECIFICATION Spec", config);
	}

	@Test
	public void testExtractModule() throws IOException {
		final Path tmpFile = Files.createTempFile("MonolithSpecExtractorTest", ".tla");
		try {
			Files.writeString(tmpFile, MONOLITH_SPEC, StandardCharsets.UTF_8);

			final NamedInputStream nis = MonolithSpecExtractor.module(tmpFile.toFile(), "Scratch");
			assertNotNull("module() should find the MODULE Scratch section", nis);

			assertEquals("Scratch", nis.getModuleName());

			@SuppressWarnings("resource")
			final String module = new BufferedReader(new InputStreamReader(nis, StandardCharsets.UTF_8)).lines()
					.collect(Collectors.joining("\n"));
			assertEquals("---- MODULE Scratch ----\n" + "EXTENDS TLC\n" + "Spec == TRUE /\\ [][TRUE]_TRUE\n" + "======",
					module);
			nis.close();
		} finally {
			Files.deleteIfExists(tmpFile);
		}
	}

	@Test
	public void testConfigWithWindowsPathAsName() throws IOException {
		final String windowsPath = "d:\\software\\TLA+\\Specs\\Scratch\\Scratch";
		final InputStream in = new ByteArrayInputStream(MONOLITH_SPEC.getBytes(StandardCharsets.UTF_8));
		// Must not throw PatternSyntaxException due to unescaped regex
		// metacharacters (\, +) in the config name.
		final InputStream configStream = MonolithSpecExtractor.config(in, windowsPath);

		@SuppressWarnings("resource")
		final String config = new BufferedReader(new InputStreamReader(configStream, StandardCharsets.UTF_8)).lines()
				.collect(Collectors.joining("\n"));
		assertEquals("", config);
	}

	@Test
	public void testModuleWithWindowsPathAsName() throws IOException {
		final String windowsPath = "d:\\software\\TLA+\\Specs\\Scratch\\Scratch";
		final Path tmpFile = Files.createTempFile("MonolithSpecExtractorTest", ".tla");
		try {
			Files.writeString(tmpFile, MONOLITH_SPEC, StandardCharsets.UTF_8);
			// Must not throw PatternSyntaxException due to unescaped regex
			// metacharacters (\, +) in the module name.
			final NamedInputStream nis = MonolithSpecExtractor.module(tmpFile.toFile(), windowsPath);
			assertEquals(null, nis);
		} finally {
			Files.deleteIfExists(tmpFile);
		}
	}

	@Test
	public void testGetConfig() {
		assertEquals("Scratch.tla", MonolithSpecExtractor.getConfig("Scratch.tla"));
		assertEquals("Scratch.cfg", MonolithSpecExtractor.getConfig("Scratch"));
	}
}
