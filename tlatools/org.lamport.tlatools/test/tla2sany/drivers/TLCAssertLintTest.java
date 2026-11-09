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
import tla2sany.semantic.Errors.ErrorDetails;
import util.SimpleFilenameToStream;

public class TLCAssertLintTest extends SANYTest {

	@Rule
	public final TemporaryFolder folder = new TemporaryFolder();

	private Path module(String name, String body) throws Exception {
		return Files.writeString(folder.getRoot().toPath().resolve(name + ".tla"),
				"---- MODULE " + name + " ----\n" + body + "\n====\n");
	}

	@Test
	public void plusCalModuleSuppressesOnlyItsOwnAssertCalls() throws Exception {
		final Path plusCal = module("Algo", "EXTENDS TLC\nHandwritten == Assert(TRUE, \"algo\")\n"
				+ "(* --algorithm Algo\nbegin\nL: assert TRUE;\nend algorithm; *)");
		final Translator translator = new Translator(Files.readString(plusCal),
				new String[] { "-nocfg", plusCal.toString() });
		Assert.assertTrue(translator.getErrors().toString(), translator.translate(new ValidationCallBack.Noop()));
		Files.writeString(plusCal, translator.getOutput());

		module("Extender", "EXTENDS Algo, TLC\nE == Assert(TRUE, \"extender\")");
		final Path root = module("Instancer", "EXTENDS Extender, TLC\nA == INSTANCE Algo\n"
				+ "I == Assert(TRUE, \"instancer\") /\\ A!Next");

		final RecordedSanyOutput out = new RecordedSanyOutput(LogLevel.WARNING);
		final SpecObj spec = new SpecObj(root.toString(), new SimpleFilenameToStream(folder.getRoot().toString()));
		Assert.assertEquals(out.toString(), SanyExitCode.OK,
				SANY.parse(spec, root.toString(), out, SanySettings.defaultSettings()));
		final List<String> sources = spec.semanticErrors.getWarningDetails().stream()
				.filter(w -> w.getCode().getStandardValue() == 4806)
				.map(w -> w.getLocation().source()).sorted().collect(Collectors.toList());
		Assert.assertEquals(List.of("Extender", "Instancer"), sources);
	}
}
