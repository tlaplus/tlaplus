package pcal;

import java.io.BufferedInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Arrays;
import java.util.List;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import pcal.exception.ParseAlgorithmException;

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
		
		/** PlusCal and a translation block exist, but there are no checksums calculated. */
		NO_CHECKSUMS_EXIST,
		
		/** One or both Checksum in the spec do not match the checksums calculated for what was found in the spec. */
		DIVERGENCE_EXISTS,
		
		/** A Java error was encountered while attempting to validate. */
		ERROR_ENCOUNTERED,
		
		/** Everything checks out. */
		NO_DIVERGENCE;
	}
	
	
	static final Pattern PCAL_CHECKSUM_PATTERN = Pattern.compile(PcalParams.PCAL_CHECKSUM_KEYWORD + "[0-9a-f]+$");
	static final Pattern TRANSLATED_PCAL_CHECKSUM_PATTERN = Pattern
			.compile(PcalParams.TRANSLATED_PCAL_CHECKSUM_KEYWORD + "[0-9a-f]+$");

	/**
	 * This method is a convenience wrapped around {@link #validate(List)}.
	 * 
	 * @param inputStream an stream to the entire specification to be validated; this stream is not closed.
	 * @return the result of the validation, as enumerated by the inner enum of this class.
	 */
	public static ValidationResult validate(final InputStream inputStream)
			throws IOException {
        final String specContents;
    	final ByteArrayOutputStream baos = new ByteArrayOutputStream();
    	final byte[] buffer = new byte[4096];
    	final BufferedInputStream bis = (inputStream instanceof BufferedInputStream)
    											? (BufferedInputStream)inputStream
    											: new BufferedInputStream(inputStream);
    	
        int bytesRead;
        while ((bytesRead = bis.read(buffer)) != -1) {
        	baos.write(buffer, 0, bytesRead);
        }
        
    	specContents = new String(baos.toByteArray(), "UTF-8");

		final String[] lines = specContents.split("\\r?\\n");
		return validate(Arrays.asList(lines));
	}
	
	/**
	 * There is some redundancy between this and {@link trans#performTranslation(List)} - it would be nice to make a
	 * 	common method, extended by each.
	 * 
	 * @param specificationText the entire specification, line by line - for historical reasons.
	 * @return the result of the validation, as enumerated by the inner enum of this class.
	 */
	public static ValidationResult validate(final List<String> specificationText) {
        final Vector<String> deTabbedSpecification = trans.removeTabs(specificationText);
		
        final IntPair searchLoc = new IntPair(0, 0);
        boolean notDone = true;
		while (notDone) {
			try {
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
			String line = deTabbedSpecification.elementAt(algLine);
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
		if (!foundBegin) {
			return ValidationResult.NO_PLUSCAL_EXISTS;
		}

		final int translationLine = trans.findTokenPair(deTabbedSpecification, 0,
														PcalParams.BeginXlation1, PcalParams.BeginXlation2);
        final String pcalMD5;
        final String translatedMD5;
		if (translationLine == -1) {
            return ValidationResult.NO_TRANSLATION_EXISTS;
		} else {
			final int endTranslationLine = trans.findTokenPair(deTabbedSpecification, translationLine + 1,
															   PcalParams.EndXlation1, PcalParams.EndXlation2);
			if (endTranslationLine == -1) {
                return ValidationResult.NO_TRANSLATION_EXISTS;
            }

			final String beginLine = deTabbedSpecification.get(translationLine);
        	Matcher m = Validator.PCAL_CHECKSUM_PATTERN.matcher(beginLine);
        	if (m.find()) {
        		pcalMD5 = beginLine.substring(m.start() + PcalParams.PCAL_CHECKSUM_KEYWORD.length());
        	} else {
        		return ValidationResult.NO_CHECKSUMS_EXIST;
        	}
        	final String endLine = deTabbedSpecification.get(endTranslationLine);
        	m = Validator.TRANSLATED_PCAL_CHECKSUM_PATTERN.matcher(endLine);
        	if (m.find()) {
        		translatedMD5 = endLine.substring(m.start() + PcalParams.TRANSLATED_PCAL_CHECKSUM_KEYWORD.length());

            	final Vector<String> translation = new Vector<>(specificationText.subList((translationLine + 1),
            																			   endTranslationLine));
            	final String calculatedMD5 = calculateMD5(translation);
            	if (!translatedMD5.equals(calculatedMD5)) {
            		return ValidationResult.DIVERGENCE_EXISTS;
            	}
        	} else {
        		translatedMD5 = null;
        	}
        }
        
		try {
			ParseAlgorithm.uncomment(deTabbedSpecification, algLine, algCol);
		} catch (ParseAlgorithmException e) {
            PcalDebug.reportError(e);
            return ValidationResult.ERROR_ENCOUNTERED;
        }

		// This seems like crazy poor design - we're already passing around algLine and algCol, but if we don't make
		//	this arbitrary object, throw it into a global public static setting, and also assign values to it there,
		//	then the ParseAlgorithm won't pick up the values..
        final TLAtoPCalMapping mapping = new TLAtoPCalMapping() ;
        mapping.algColumn = algCol;
        mapping.algLine = algLine;
        PcalParams.tlaPcalMapping = mapping;
		
		final PcalCharReader reader = new PcalCharReader(deTabbedSpecification, algLine, algCol,
				specificationText.size(), 0);
		final AST ast;
		try {
			ast = ParseAlgorithm.getAlgorithm(reader, foundFairBegin);
		} catch (ParseAlgorithmException e) {
			PcalDebug.reportError(e);
			return ValidationResult.ERROR_ENCOUNTERED;
		}
        
        final String calculatedMD5 = Validator.calculateMD5(ast.toString());
    	if (!pcalMD5.equals(calculatedMD5)) {
    		return ValidationResult.DIVERGENCE_EXISTS;
    	}

		return ValidationResult.NO_DIVERGENCE;
	}
    
    static String calculateMD5(final Vector<String> lines) {
    	final StringBuilder sb = new StringBuilder();
    	for (final String str : lines) {
    		sb.append(str);
    	}
    	
    	return calculateMD5(sb.toString());
    }
    
    static String calculateMD5(final String string) {
    	try {
        	final MessageDigest digest = MessageDigest.getInstance("MD5");
        	final byte[] hash = digest.digest(string.getBytes(StandardCharsets.UTF_8));
        	final StringBuffer hexString = new StringBuffer();
			for (int i = 0; i < hash.length; i++) {
				final String hex = Integer.toHexString(0xff & hash[i]);
				if (hex.length() == 1) {
					hexString.append('0');
				}
				hexString.append(hex);
			}
            return hexString.toString();
    	} catch (final NoSuchAlgorithmException e) {
    		PcalDebug.reportError("Unable to calculate MD5: " + e.getMessage());
    		return null;
    	}
    }
}
