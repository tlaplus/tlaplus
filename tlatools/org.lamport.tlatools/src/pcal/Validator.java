package pcal;

import java.io.BufferedInputStream;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.zip.CRC32;

import pcal.exception.ParseAlgorithmException;
import pcal.exception.RemoveNameConflictsException;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.st.Location;
import util.TLAConstants;

/**
 * This class validates the recorded checksums generated from an input specification's PlusCal and translated PlusCal
 * blocks.
 */
public class Validator {

	public enum ValidationResult {
		/** No PlusCal algorithm exists in the specification */
		NO_PLUSCAL_EXISTS,
		
		/** No translation exists - BUT THERE IS PLUSCAL IN THE SPECIFICATION! */
		NO_TRANSLATION_EXISTS,
		
		NO_TLA_CHECKSUMS_EXIST,
		NO_PCAL_CHECKSUMS_EXIST,
		
		TLA_DIVERGENCE_EXISTS,
		PCAL_DIVERGENCE_EXISTS,
		
		/** A Java error was encountered while attempting to validate. */
		ERROR_ENCOUNTERED,
		
		/** Everything checks out. */
		NO_DIVERGENCE;
	}
	
	static final String PCAL_CHECKSUM = "pcalchecksum";
	static final String TLA_CHECKSUM = "tlachecksum";
	
	static final String FAIR = "fair";
	
	static final String CHECKSUM_TEMPLATE_IGNORE = "(chksum(pcal) \\in STRING /\\ chksum(tla) \\in STRING)";
	static final String CHECKSUM_TEMPLATE = "(chksum(pcal) = \"%s\" /\\ chksum(tla) = \"%s\")";
	
	static final Pattern CHECKSUM_PATTERN = Pattern
			.compile("\\\\\\* BEGIN TRANSLATION\\s+\\(\\s*((?i)ch(ec)?ksum\\(p(lus)?cal\\)(?-i))\\s*(=\\s*\\\"(?<"
					+ PCAL_CHECKSUM + ">[0-9A-Fa-f]*)\\\"|\\\\in\\s*"
					+ "STRING)\\s*\\/\\\\\\s*((?i)ch(ec)?ksum\\(tla\\+?\\)(?-i))\\s*(=\\s*\\\"(?<" + TLA_CHECKSUM
					+ ">[0-9A-Fa-f]*)\\\"|\\\\in\\s*STRING)\\s*\\)");

	private static final Pattern MODULE_CLOSING_PATTERN = Pattern.compile(TLAConstants.MODULE_CLOSING_REGEX);

	public static Set<ValidationResult> validate(ParseUnit parseUnit, InputStream inputStream)
			throws IOException {
		final BufferedReader reader = new BufferedReader(
				new InputStreamReader((inputStream instanceof BufferedInputStream) ? (BufferedInputStream) inputStream
						: new BufferedInputStream(inputStream)));
		return validate(parseUnit, reader);
	}
	
	public static Set<ValidationResult> validate(final ParseUnit parseUnit, final BufferedReader reader) throws IOException {
		// Instead of matching the module start and end markers, whe while loop use SANY's
		// parse tree that has the location of the start and end markers.
		final Location loc = parseUnit.getParseTree().getLocation();
		
		// Pre-allocate the number of lines we will read below.
		final List<String> lines = new ArrayList<>(loc.endLine() - loc.beginLine());
		
		// TODO It would be faster to let SANY look for a PlusCal algorithm when it
		// parses the TLA+ spec (although SANY probably doesn't parse comments, it
		// could look for the "--algorithm" or "--fair algorithm" tokens).
		boolean seenAlgo = false;
		int cnt = 1; // Location is 1-indexed.
		String line;
		while ((line = reader.readLine()) != null) {
			// Skip lines that are not within the range given by location.
			// This implies that this loop will miss "pluscal options" before
			// or after the module's start and end markers.  While it is legal to
			// put options there, I've decided we don't want to pay the price
			// of parsing the lines preceding or after a module.  Users can
			// put the options into a comment inside the module, which I
			// believe to be the choice for most users anyway.
			if (loc.beginLine() <= cnt && cnt <= loc.endLine()) {
				if (line.indexOf(PcalParams.BeginAlg.substring(2)) > 0) {
					seenAlgo = true;
				}
				lines.add(line);
			} else if (cnt >= loc.endLine()) {
				break;
			}
			cnt++;
		}
		
		if (!seenAlgo) {
			// No "algorithm" string in the input => No PlusCal algorithm.
			// The appearance of "algorithm", however, might be a false
			// positive of which validate will take care of (I don't have
			// time to move the logic up here).
			return setOf(ValidationResult.NO_PLUSCAL_EXISTS);
		}
		return validate(lines);
	}
	
	/**
	 * There is some redundancy between this and {@link trans#performTranslation(List)} - it would be nice to make a
	 * 	common method, extended by each.
	 * 
	 * @param specificationText the entire specification, line by line - for historical reasons.
	 * @return the result of the validation, as enumerated by the inner enum of this class.
	 */
	private static Set<ValidationResult>  validate(final List<String> specificationText) {
        final Vector<String> deTabbedSpecification = trans.removeTabs(specificationText);
		
        final IntPair searchLoc = new IntPair(0, 0);
        boolean notDone = true;
		while (notDone) {
			try {
				/*
				 * As mentioned in #413, this is a performance bottleneck point; unfortunately we need process the
				 *		options as it affects the production of the AST and we base the checksum on the AST.
				 * We have addressed a use case in which there is a long run of line prefacing the module specification
				 * 		in the {@link #validate(InputStream)} method, but that doesn't address a long spec.
				 * If we wanted to devote more time to this, we should examine the performance difference between
				 * 		the character-by-character marching done in the ParseAlgorithm code versus using a
				 * 		regex matcher to split apart lines.
				 */
                ParseAlgorithm.FindToken("PlusCal", deTabbedSpecification, searchLoc, "");
                final String line = ParseAlgorithm.GotoNextNonSpace(deTabbedSpecification, searchLoc);
                final String restOfLine = line.substring(searchLoc.two);
				if (restOfLine.startsWith("options")) {
                    // The first string after "PlusCal" not starting with a
                    // space character is "options"
					if (ParseAlgorithm.NextNonIdChar(restOfLine, 0) == 7) {
                        // The "options" should begin an options line
                        PcalParams.optionsInFile = true;
                        ParseAlgorithm.ProcessOptions(deTabbedSpecification, searchLoc);
                        notDone = false;
                    }
                }
			} catch (ParseAlgorithmException e) {
                // The token "PlusCal" not found.
                notDone = false;
            }
        }
        
        int algLine = 0;
        int algCol = -1;
        // Search for "--algorithm" or "--fair".
        // If found set algLine and algCol right after the last char,
        // set foundBegin true, and set foundFairBegin true iff it
        // was "--fair".  Otherwise, set foundBegin false.
        boolean foundBegin = false;
        boolean foundFairBegin = false;
		while ((algLine < deTabbedSpecification.size()) && !foundBegin) {
			final String line = deTabbedSpecification.elementAt(algLine);
			final Matcher m = MODULE_CLOSING_PATTERN.matcher(line);
			if (m.matches()) {
				break;
			}
			
			algCol = line.indexOf(PcalParams.BeginAlg);
			if (algCol != -1) {
				algCol = algCol + PcalParams.BeginAlg.length();
				foundBegin = true;
			} else {
            	algCol = line.indexOf(PcalParams.BeginFairAlg);
            	if (algCol != -1) {
            		// Found the "--fair".  The more structurally nice thing to
            		// do here would be to move past the following "algorithm".
            		// However, it's easier to pass a parameter to the ParseAlgorithm
            		// class's GetAlgorithm method that tells it to go past the
            		// "algorithm" token.
            		 algCol = algCol + PcalParams.BeginFairAlg.length();
                     foundBegin = true;
                     foundFairBegin = true;
            		
            	} else {
            		algLine = algLine + 1;
            	} 
            }
        }
	       
		final Set<ValidationResult> res = new HashSet<>();

		
		// TLA+ translation
		final int translationLine = trans.findTokenPair(deTabbedSpecification, 0,
														PcalParams.BeginXlation1, PcalParams.BeginXlation2);
		if (translationLine == -1) {
			res.add(ValidationResult.NO_TRANSLATION_EXISTS);
		}
		
		final int endTranslationLine = trans.findTokenPair(deTabbedSpecification, translationLine + 1,
				PcalParams.EndXlation1, PcalParams.EndXlation2);
		if (endTranslationLine == -1) {
			res.add(ValidationResult.NO_TRANSLATION_EXISTS);
		}
		if (translationLine == -1 && endTranslationLine == -1) {
			return res;
		}

		// PlusCal algorithm
		if (!foundBegin) {
			res.add(ValidationResult.NO_PLUSCAL_EXISTS);
		} else {

	    	// Get the PlusCal AST by parsing it.
			try {
				ParseAlgorithm.uncomment(deTabbedSpecification, algLine, algCol);
			} catch (ParseAlgorithmException e) {
	            PcalDebug.reportError(e);
	            return setOf(ValidationResult.ERROR_ENCOUNTERED);
	        }
			
	        final TLAtoPCalMapping mapping = new TLAtoPCalMapping() ;
	        mapping.algColumn = algCol;
	        mapping.algLine = algLine;
	        PcalParams.tlaPcalMapping = mapping;
			
			AST ast = new AST();
			try {
				final PcalCharReader reader = new PcalCharReader(deTabbedSpecification, algLine, algCol,
						specificationText.size(), 0);
				ast = ParseAlgorithm.getAlgorithm(reader, foundFairBegin);
				
				// The call translate mutates the ast in pcal.PcalTranslate.Explode(AST, PcalSymTab).
				// I'm ignoring the PcalParams.tlcTranslation() alternative in trans.java
				// because I doubt the "-spec" feature is used widely (if at all).
		        final PCalTLAGenerator pcalTLAGenerator = new PCalTLAGenerator(ast);
	            pcalTLAGenerator.removeNameConflicts();
                pcalTLAGenerator.translate();
			} catch (ParseAlgorithmException | RemoveNameConflictsException e) {
				PcalDebug.reportError(e);
				// The PlusCal algorithm doesn't parse because of a syntax error. This indicates
				// that the algorithm has been modified since it wouldn't have been possible to
				// calculate a checksum earlier. ast will be empty string and, thus, not match below.
			}
	        
			// Calculate the checksum value for the PlusCal's AST and compare unless no
			// checksum to compare it with is given (or it has been disabled).
			final Matcher m = Validator.CHECKSUM_PATTERN.matcher(deTabbedSpecification.get(translationLine));
	    	if (m.find()) {
	    		if (m.group(Validator.PCAL_CHECKSUM) != null) {

	    			final String chksumPCalAST = Validator.checksum(foundFairBegin ? FAIR : "" + ast.toString());
	    			if (!m.group(Validator.PCAL_CHECKSUM).equals(chksumPCalAST)) {
	    				// Mismatch between the PlusCal algorithm and its checksum.
	    				res.add(ValidationResult.PCAL_DIVERGENCE_EXISTS);
	    			}
	    		}
	    		if (m.group(Validator.TLA_CHECKSUM) != null) {
					final Vector<String> translation = new Vector<>(
							specificationText.subList((translationLine + 1), endTranslationLine));
					final String chksumTLATranslation = Validator.checksum(translation);
	    			
	    			if (!m.group(Validator.TLA_CHECKSUM).equals(chksumTLATranslation)) {
	    				// Mismatch between the TLA+ translation and its checksum.
	    				res.add(ValidationResult.TLA_DIVERGENCE_EXISTS);
	    			}
	    		}
	    	} else {
	    		res.add(ValidationResult.NO_PCAL_CHECKSUMS_EXIST);
	    	}
		}
		return res.isEmpty() ? setOf(ValidationResult.NO_DIVERGENCE) : res;
	}
    
    public static String checksum(final Vector<String> lines) {
    	final StringBuilder sb = new StringBuilder();
    	for (final String str : lines) {
    		sb.append(str);
    	}
    	
    	return checksum(sb.toString());
    }
    
    static String checksum(final String string) {
    	final CRC32 crc32 = new CRC32();
    	crc32.update(string.getBytes());
    	return Long.toHexString(crc32.getValue());
    }

    private static Set<ValidationResult> setOf(ValidationResult... res) {
    	return new HashSet<>(Arrays.asList(res));
    }
}
