package tlc2.output;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.CopyOption;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import tla2sany.semantic.StandardModules;
import tlc2.input.MCParser;
import tlc2.input.MCParserResults;
import util.TLAConstants;

public class TLAMonolithCreator extends AbstractTLACopier {
	// these are modules which SANY logs that it has parsed
	private final List<File> extendedModules;
	// these are the modules which the root ModuleNode or one of its sub-ModuleNodes (or one or their sub-ModuleNodes
	//		and so on, turtles all the way down) has defined as EXTENDS-ing in their spec
	private final Set<String> modulesToSpecifyInExtends;
	
	public TLAMonolithCreator(final String rootSpecName, final File sourceLocation, final List<File> extendeds,
							  final Set<String> entireExtendsList) {
		super(rootSpecName, ("tmp_" + System.currentTimeMillis() + "_monolith"), sourceLocation);
		
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
		// for TLC things
		modulesToSpecifyInExtends.add(TLAConstants.BuiltInModules.TLC);
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
				commentLine.append(originalModuleName);
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
		final String moduleFilename = module.getName();
		final int index = moduleFilename.indexOf(TLAConstants.Files.TLA_EXTENSION);
		final String moduleName;
		if (index != -1) {
			moduleName = moduleFilename.substring(0, index);
		} else {
			moduleName = moduleFilename;
		}
		commentLine.append(TLAConstants.COMMENT).append(TLAConstants.CR);
		commentLine.append(TLAConstants.COMMENT).append(' ').append(moduleName).append(" follows\n");
		commentLine.append(TLAConstants.COMMENT).append(TLAConstants.CR).append(TLAConstants.CR);
		
		monolithWriter.write(commentLine.toString());
		
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
	
	
	public static void main(final String[] args) {
		if (args.length == 0) {
			System.out.println("java tlc2.output.TLAMonolithCreator \\\n"
									+ "\t[-sourceDir=_directory_containing_spec_tla_] \\\n"
									+ "\t_specName_");
			
			System.exit(-2);
		}
		
		final File sourceDirectory;
		final String specName;
		if (args.length == 1) {
			sourceDirectory = new File(System.getProperty("user.dir"));
			specName = args[0];
		} else {
			sourceDirectory = new File(args[0]);
			specName = args[1];
		}
		final File originalTLA = new File(sourceDirectory, (specName + TLAConstants.Files.TLA_EXTENSION));
		if (!originalTLA.exists()) {
			System.out.println("Excepted to find the TLA file but could not: " + originalTLA.getAbsolutePath());
			
			System.exit(-3);
		}
		
		final MCParser parser = new MCParser(sourceDirectory, specName, true);
		final MCParserResults results = parser.parse();
		
		final File backupTLA = new File(sourceDirectory, (specName + "_orig" + TLAConstants.Files.TLA_EXTENSION));
		
		try {
			Files.copy(originalTLA.toPath(), backupTLA.toPath(), StandardCopyOption.COPY_ATTRIBUTES);
		} catch (final IOException ioe) {
			System.out.println("Exception encountered while making a backup of the original TLA file: "
									+ ioe.getMessage());
			
			System.exit(-1);
		}
		
		try {
			final ArrayList<File> extendeds = new ArrayList<>();
			for (final String extended : results.getOriginalExtendedModules()) {
				extendeds.add(new File(sourceDirectory, (extended + TLAConstants.Files.TLA_EXTENSION)));
			}
			
			final TLAMonolithCreator creator = new TLAMonolithCreator(specName, sourceDirectory, extendeds,
																	  results.getAllExtendedModules());
			creator.copy();
			
			System.out.println("The monolith file is now present at: " + originalTLA.getAbsolutePath());
		} catch (final IOException ioe) {
			System.out.println("Exception encountered while making creating the monolith: " + ioe.getMessage());
			
			System.exit(-4);
		} finally {
			System.out.println("The original TLA file was backed up to: " + backupTLA.getAbsolutePath());
		}
	}
}
