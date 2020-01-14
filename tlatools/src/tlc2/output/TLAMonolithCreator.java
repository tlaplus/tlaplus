package tlc2.output;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.CopyOption;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import tla2sany.semantic.StandardModules;
import util.TLAConstants;

public class TLAMonolithCreator extends AbstractTLACopier {
	// these are modules which SANY logs that it has parsed
	private final List<File> extendedModules;
	// these are the modules which the root ModuleNode or one of its sub-ModuleNodes (or one or their sub-ModuleNodes
	//		and so on, turtles all the way down) has defined as EXTENDS-ing in their spec
	private final Set<String> modulesToSpecifyInExtends;
	
	public TLAMonolithCreator(final String specTEName, final File sourceLocation, final List<File> extendeds,
							  final Set<String> entireExtendsList) {
		super(specTEName, ("tmp_" + System.currentTimeMillis() + "_monolith"), sourceLocation);
		
		extendedModules = new ArrayList<File>();
		for (final File f : extendeds) {
			final String name = f.getName();
			final int index = name.toLowerCase().indexOf(TLAConstants.Files.TLA_EXTENSION);
			final boolean keep;
			if (index == -1) {
				// this should never be the case
				keep = true;
			} else {
				final String baseName = name.substring(0, index);

				keep = !StandardModules.isDefinedInStandardModule(baseName);
			}
			
			if (keep) {
				extendedModules.add(f);
			}
		}
		
		modulesToSpecifyInExtends = new HashSet<>(entireExtendsList);
		StandardModules.filterNonStandardModulesFromSet(modulesToSpecifyInExtends);
		// for _TE things
		modulesToSpecifyInExtends.add(TLAConstants.BuiltInModules.TRACE_EXPRESSIONS);
	}
	
	@Override
	protected void copyLine(final BufferedWriter writer, final String originalLine, final int lineNumber)
			throws IOException {
		if (!inBody) {
			final Matcher m = modulePattern.matcher(originalLine);

			inBody = m.find();

			writer.write(originalLine + '\n');
		} else {
			if (originalLine.trim().startsWith(TLAConstants.KeyWords.EXTENDS)) {
				writer.write(TLAConstants.KeyWords.EXTENDS + " " + String.join(", ", modulesToSpecifyInExtends) + "\n");

				for (final File f : extendedModules) {
					insertModuleIntoMonolith(f, writer);
				}
				
				final StringBuilder commentLine = new StringBuilder(TLAConstants.CR);
				commentLine.append(TLAConstants.COMMENT).append(TLAConstants.CR);
				commentLine.append(TLAConstants.COMMENT).append(' ');
				commentLine.append(TLAConstants.TraceExplore.ERROR_STATES_MODULE_NAME);
				commentLine.append(" follows\n");
				commentLine.append(TLAConstants.COMMENT).append(TLAConstants.CR).append(TLAConstants.CR);
				writer.write(commentLine.toString());
			} else {
				writer.write(originalLine + '\n');
			}
		}
	}
	
	@Override
	protected void copyHasFinished() throws IOException {
		final Path originalPath = sourceFile.toPath();
		Files.delete(originalPath);
		
		final Path monolithPath = destinationFile.toPath();
		Files.move(monolithPath, originalPath, new CopyOption[0]);
	}	
	
	private void insertModuleIntoMonolith(final File module, final BufferedWriter monolithWriter) throws IOException {
		final StringBuilder commentLine = new StringBuilder(TLAConstants.CR);
		commentLine.append(TLAConstants.COMMENT).append(TLAConstants.CR);
		commentLine.append(TLAConstants.COMMENT).append(' ').append(module.getName()).append(" follows\n");
		commentLine.append(TLAConstants.COMMENT).append(TLAConstants.CR).append(TLAConstants.CR);
		
		monolithWriter.write(commentLine.toString());
		
		final String moduleFilename = module.getName();
		final String moduleName
				= moduleFilename.substring(0, (moduleFilename.length() - TLAConstants.Files.TLA_EXTENSION.length()));
		final String regex = MODULE_REGEX_PREFIX + moduleName;
		final Pattern insertingModuleMatcher = Pattern.compile(regex);
		
		try (final BufferedReader br = new BufferedReader(new FileReader(module))) {
			String line;
			boolean inModuleBody = false;
			
			while ((line = br.readLine()) != null) {
				if (!inModuleBody) {
					final Matcher m = insertingModuleMatcher.matcher(line);

					inModuleBody = m.find();
				} else {
					if (!line.trim().startsWith(TLAConstants.KeyWords.EXTENDS)) {
						final Matcher m = CLOSING_BODY_PATTERN.matcher(line);

						if (m.matches()) {
							break;
						}

						monolithWriter.write(line + '\n');
					}
				}
			}
		}
	}
}
