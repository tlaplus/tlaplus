/*******************************************************************************
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
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 ******************************************************************************/
package tla2sany.drivers;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.stream.Collectors;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import pcal.Translator;
import pcal.ValidationCallBack;
import tla2sany.SANYTest;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.output.LogLevel;
import tla2sany.output.RecordedSanyOutput;
import tla2sany.semantic.ErrorCode;
import tla2sany.semantic.Errors;
import tla2sany.semantic.Errors.ErrorDetails;
import util.SimpleFilenameToStream;

public class TLCAssertLintTest extends SANYTest {

	@Rule
	public final TemporaryFolder folder = new TemporaryFolder();

	private Path module(String name, String body) throws Exception {
		return Files.writeString(folder.getRoot().toPath().resolve(name + ".tla"),
				"---- MODULE " + name + " ----\n" + body + "\n====\n");
	}

	private SpecObj parse(Path path) throws Exception {
		final RecordedSanyOutput out = new RecordedSanyOutput(LogLevel.WARNING);
		final SpecObj spec = new SpecObj(path.toString(), new SimpleFilenameToStream(folder.getRoot().toString()));
		Assert.assertEquals(out.toString(), SanyExitCode.OK,
				SANY.parse(spec, path.toString(), out, SanySettings.defaultSettings()));
		return spec;
	}

	private List<ErrorDetails> warnings(SpecObj spec) {
		return spec.semanticErrors.getWarningDetails().stream()
				.filter(w -> w.getCode().getStandardValue() == 4806).collect(Collectors.toList());
	}

	@Test
	public void handwrittenApplications() throws Exception {
		final List<ErrorDetails> warnings = warnings(parse(module("Direct",
				"EXTENDS TLC\nA == Assert(TRUE, \"a\")\nB == Assert(FALSE, \"b\")")));
		Assert.assertEquals(2, warnings.size());
		Assert.assertEquals("Direct", warnings.get(0).getLocation().source());
		Assert.assertEquals(3, warnings.get(0).getLocation().beginLine());
		Assert.assertEquals(6, warnings.get(0).getLocation().beginColumn());
		Assert.assertEquals(4, warnings.get(1).getLocation().beginLine());
		for (ErrorDetails warning : warnings) {
			Assert.assertTrue(warning.getMessage().contains("evaluation order"));
			Assert.assertTrue(warning.getMessage().contains("invariant"));
			Assert.assertTrue(warning.getMessage().contains("action"));
			Assert.assertTrue(warning.getMessage().contains("temporal"));
			Assert.assertTrue(warning.getMessage().contains("debugger"));
		}
	}

	@Test
	public void resolvedApplicationsAndAuthoredBodies() throws Exception {
		module("Bridge", "T == INSTANCE TLC");
		module("Middle", "B == INSTANCE Bridge");
		module("Wrapper", "EXTENDS TLC\nCheck == Assert(TRUE, \"wrapper\")");
		final SpecObj spec = parse(module("Resolution", "EXTENDS TLC, Wrapper\n"
				+ "T == INSTANCE TLC\nM == INSTANCE Middle\nW == INSTANCE Wrapper\n"
				+ "Qualified == T!Assert(TRUE, \"qualified\")\n"
				+ "Transitive == M!B!T!Assert(TRUE, \"transitive\")\n"
				+ "Nested == IF TRUE THEN Assert(TRUE, \"nested\") ELSE TRUE\n"
				+ "Let == LET Local == Assert(TRUE, \"let\") IN Local\n"
				+ "ASSUME Assert(TRUE, \"assume\")\nTHEOREM Assert(TRUE, \"theorem\")\n"
				+ "Uses == Check /\\ W!Check /\\ Check\n"
				+ "---- MODULE Inner ----\nEXTENDS TLC\nI == Assert(TRUE, \"inner\")\n===="));
		final List<ErrorDetails> warnings = warnings(spec);
		Assert.assertEquals(8, warnings.size());
		Assert.assertEquals(1, warnings.stream().filter(w -> w.getLocation().source().equals("Wrapper")).count());
		Assert.assertFalse(warnings.stream().anyMatch(w -> w.getLocation().beginLine() == 12
				&& w.getLocation().source().equals("Resolution")));
	}

	@Test
	public void unrelatedOperatorsAndUnusedImports() throws Exception {
		module("User", "Assert(a, b) == a");
		Assert.assertTrue(warnings(parse(module("Unrelated", "Assert(a, b) == a\n"
				+ "U == INSTANCE User\nA == Assert(TRUE, \"local\")\nB == U!Assert(TRUE, \"user\")"))).isEmpty());
		Assert.assertTrue(warnings(parse(module("Unused", "EXTENDS TLC\nT == INSTANCE TLC"))).isEmpty());
		module("TLC", "Assert(a, b) == a");
		Assert.assertTrue(warnings(parse(module("Shadowed", "EXTENDS TLC\nT == INSTANCE TLC\n"
				+ "A == Assert(TRUE, \"shadow\")\nB == T!Assert(TRUE, \"instance\")"))).isEmpty());
	}

	@Test
	public void translatedAndHandwrittenApplications() throws Exception {
		final Path generated = module("Generated", "EXTENDS TLC\nBefore == Assert(TRUE, \"before\")\n"
				+ "(* --algorithm Check\nbegin\nL: assert TRUE;\nend algorithm; *)\n"
				+ "After == Assert(TRUE, \"after\")");
		final Translator translator = new Translator(Files.readString(generated), new String[] { "-nocfg", generated.toString() });
		final boolean translatedSuccessfully = translator.translate(new ValidationCallBack.Noop());
		Assert.assertTrue(translator.getErrors().toString(), translatedSuccessfully);
		Files.writeString(generated, translator.getOutput());
		Assert.assertEquals(2, warnings(parse(generated)).size());
		final String translated = Files.readString(generated);
		Assert.assertTrue(translated.contains("\\* BEGIN TRANSLATION ("));
		Assert.assertTrue(translated.substring(translated.indexOf("\\* BEGIN TRANSLATION"),
				translated.indexOf("\\* END TRANSLATION")).contains("Assert("));
		final Path importer = module("Importer", "EXTENDS Generated\nG == INSTANCE Generated\nUse == G!Next");
		Assert.assertEquals(2, warnings(parse(importer)).size());
		Files.writeString(generated, translated.replaceAll("(?m)^(\\\\\\* (?:BEGIN|END) TRANSLATION).*$", "$1"));
		Assert.assertEquals(2, warnings(parse(importer)).size());
	}

	@Test
	public void onlyBalancedCommentDelimitersExemptCalls() throws Exception {
		final List<ErrorDetails> warnings = warnings(parse(module("Boundaries", "EXTENDS TLC\n"
				+ "Text == \"\\\\* BEGIN TRANSLATION\"\nA == Assert(TRUE, \"string\")\n"
				+ "\\* END TRANSLATION\n"
				+ "(* outer (* nested *)\\* BEGIN TRANSLATION\n*)\n"
				+ "B == Assert(TRUE, \"block\")\n\\* END TRANSLATION\n"
				+ "\\* BEGIN TRANSLATION\nGenerated == Assert(TRUE, \"generated\")\n\\* END TRANSLATION\n"
				+ "C == Assert(TRUE, \"after\")\n\\* BEGIN TRANSLATION\nD == Assert(TRUE, \"unclosed\")")));
		Assert.assertEquals(4, warnings.size());
	}

	@Test
	public void existingErrorsDoNotSuppressAssertLint() throws Exception {
		final SpecObj spec = parse(module("ExistingError", "EXTENDS TLC\nA == Assert(TRUE, \"a\")"));
		spec.semanticErrors = new Errors();
		spec.semanticErrors.addMessage(ErrorCode.GENERAL, null, "Existing error");
		SANY.frontEndLinting(spec, new RecordedSanyOutput(LogLevel.WARNING));
		Assert.assertEquals(1, warnings(spec).size());
	}

	@Test
	public void parsedCommentLocationsWithTabsAndWindowsLineEndings() throws Exception {
		final Path path = module("CommentLocations", "EXTENDS TLC\n"
				+ "Head == TRUE\t\\* BEGIN TRANSLATION\n"
				+ "Generated == Assert(TRUE, \"generated\")\n\t\\* END TRANSLATION\n"
				+ "Authored == Assert(TRUE, \"authored\")");
		Files.writeString(path, Files.readString(path).replace("\n", "\r\n"));
		final List<ErrorDetails> warnings = warnings(parse(path));
		Assert.assertEquals(1, warnings.size());
		Assert.assertEquals(6, warnings.get(0).getLocation().beginLine());
	}

	@Test
	public void sourceReadFailureIsReportedAndLintingContinues() throws Exception {
		final Path path = module("Unreadable", "EXTENDS TLC\nA == Assert(TRUE, \"a\")");
		final SpecObj spec = parse(path);
		spec.semanticErrors = new Errors();
		Files.delete(path);
		final RecordedSanyOutput out = new RecordedSanyOutput(LogLevel.WARNING);
		SANY.frontEndLinting(spec, out);
		Assert.assertTrue(out.toString(), out.getMessages().stream().anyMatch(m ->
				m.getLevel() == LogLevel.ERROR && m.getText().contains("Cannot read source")
				&& m.getText().contains("Unreadable")));
		Assert.assertEquals(1, warnings(spec).size());
	}
}
