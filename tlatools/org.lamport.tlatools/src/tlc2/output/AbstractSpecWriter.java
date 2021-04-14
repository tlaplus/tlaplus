package tlc2.output;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.List;

import tlc2.model.Assignment;
import tlc2.model.TypedSet;
import util.TLAConstants;

/**
 * This is the abstract class of spec writers; there's no reason this need be abstract, it is more a semantic
 * 	denoting that within our code base, it acts as only a superclass to other employed classes.
 */
public abstract class AbstractSpecWriter {
    /**
     * Assigns a right side to a label using an id generated from given schema
	 * @param tlaBuffer the buffer into which the TLA code will be placed
	 * @param cfgBuffer if non-null, the buffer into which the CFG code will be placed
     * @param constant, constant containing the values
     * @param schema schema to generate the Id
     * @return generated id
     */
	public static String addArrowAssignmentToBuffers(final StringBuilder tlaBuffer, final StringBuilder cfgBuffer,
			final Assignment constant, final String schema) {
		final String identifier = SpecWriterUtilities.getValidIdentifier(schema);
		return addArrowAssignmentIdToBuffers(tlaBuffer, cfgBuffer, constant, identifier, identifier);
	}

	public static String addArrowAssignmentIdToBuffers(final StringBuilder tlaBuffer, final StringBuilder cfgBuffer,
			final Assignment constant, final String id, final String configId) {
		// constant instantiation
		// to .cfg : foo <- <id>
		// to _MC.tla : <id>(a, b, c)==
		// <expression>
		tlaBuffer.append(constant.getParametrizedLabel(id)).append(TLAConstants.DEFINES).append(TLAConstants.CR);
		tlaBuffer.append(constant.getRight()).append(TLAConstants.CR);
		
		if (cfgBuffer != null) {
			cfgBuffer.append(TLAConstants.CR).append(TLAConstants.KeyWords.CONSTANT).append(TLAConstants.CR);
			cfgBuffer.append(TLAConstants.INDENT).append(constant.getLabel()).append(TLAConstants.ARROW).append(configId).append(TLAConstants.CR);
		}
		return id;
	}
	
	/**
	 * Subclasses may implement this interface in order to invoke {@link #writeFiles(ContentWriter)} for cases
	 * in which the subclass is has file handles which are not suitable to being converted and used in
	 * {@link #writeStreamToFile(InputStream, boolean)}
	 */
    protected interface ContentWriter {
    	void writeStreamToFile(final InputStream inputStream, final boolean forTLAFile) throws IOException;
    }
    

    protected static final String CLOSING_SEP = TLAConstants.CR + TLAConstants.SEP + TLAConstants.CR;
	
	
    protected final StringBuilder tlaBuffer;
    protected final StringBuilder cfgBuffer;
    
    /**
	 * @param generateConfigurationContent if true, configuration file (.cfg)
	 *                                     accompanying the TLA module content will
	 *                                     be generated
	 */
    protected AbstractSpecWriter(final boolean generateConfigurationContent) {
    	tlaBuffer = new StringBuilder();
    	cfgBuffer = generateConfigurationContent ? new StringBuilder() : null;
    }

    /**
     * Subclasses may override this to set their own spin on a closing tag.
     * 
     * @return the String content of a module closing tag.
     */
    protected String getTLAModuleClosingTag() {
    	final StringBuilder sb = SpecWriterUtilities.getModuleClosingTag(77, false);
    	
    	return sb.toString();
    }
    
    /**
     * Provided for test code
     * @param tla if non-null the content will be appended to the tlaBuffer
     * @param cfg if non-null the content will be appended to the cfgBuffer
     */
    void appendContentToBuffers(final String tla, final String cfg) {
    	if (tla != null) {
    		tlaBuffer.append(tla);
    	}
    	
    	if (cfg != null) {
    		cfgBuffer.append(cfg);
    	}
    }
    
    /**
     * Writes the buffers to streams.
     * @param tlaStream TLA stream; if null, nothing is written.
     * @param cfgStream CFG stream; if null, nothing is written.
     * @throws IOException If there is an error writing to stream.
     */
    public void writeStreams(final OutputStream tlaStream, final OutputStream cfgStream) throws IOException {
    	final ContentWriter cw = (inputStream, forTlaFile) -> {
    		final OutputStream outputStream = forTlaFile ? tlaStream : cfgStream;
    		if (null != outputStream) {
    			// If we upgrade to Java 9 we can use InputStream.transferTo()
    			// For Java 8 compatibility we will copy the bytes manually
    			final byte[] buffer = new byte[8192];
    			int length;
    			while ((length = inputStream.read(buffer)) > 0) {
    				outputStream.write(buffer, 0, length);
    			}
    		}
    	};
    	
    	writeFiles(cw);
    }
    
    /**
     * Write the buffers to files.
     * 
     * @param tlaFile if null, nothing is written
     * @param cfgFile if null, nothing is written
     * @throws IOException
     */
	public void writeFiles(final File tlaFile, final File cfgFile) throws IOException {
		final ContentWriter cw = (inputStream, forTLAFile) -> {
			final File f = (forTLAFile ? tlaFile: cfgFile);
			
			if (f != null) {
		        Files.copy(inputStream, f.toPath(), StandardCopyOption.REPLACE_EXISTING);
			}
		};
		
		writeFiles(cw);
	}
	
	/**
	 * Subclasses may use to this to provide a content writer which deals with output other than using {@code java.io}
	 * directly.
	 * 
	 * @param contentWriter
	 * @throws IOException
	 */
	protected void writeFiles(final ContentWriter contentWriter) throws IOException {
        tlaBuffer.append(getTLAModuleClosingTag());
        final ByteArrayInputStream tlaBAIS = new ByteArrayInputStream(tlaBuffer.toString().getBytes());
        contentWriter.writeStreamToFile(tlaBAIS, true);
        
		if (cfgBuffer != null) {
			cfgBuffer.append(SpecWriterUtilities.getGeneratedTimeStampCommentLine());
	        final ByteArrayInputStream configurationBAIS = new ByteArrayInputStream(cfgBuffer.toString().getBytes());
	        contentWriter.writeStreamToFile(configurationBAIS, false);
		}
	}

	/**
	 * Add file header, which consists of the module-beginning ----- MODULE ... ----
	 * line and the EXTENDS statement.
	 * 
	 * @param moduleFilename
	 * @param extendedModuleName
	 */
	public void addPrimer(final String moduleFilename, final String extendedModuleName) {
		tlaBuffer.append(SpecWriterUtilities.getExtendingModuleContent(moduleFilename,
																	   new String[] { extendedModuleName, "TLC" }));
	}

	/**
	 * Add spec definition
	 * 
	 * @param specDefinition
	 * @param attributeName
	 */
	public void addSpecDefinition(final String[] specDefinition, final String attributeName) {
		if (cfgBuffer != null) {
			cfgBuffer.append(TLAConstants.KeyWords.SPECIFICATION).append(TLAConstants.SPACE);
			cfgBuffer.append(specDefinition[0]).append(TLAConstants.CR);
		}
		
		tlaBuffer.append(TLAConstants.COMMENT).append(TLAConstants.KeyWords.SPECIFICATION).append(TLAConstants.SPACE);
		tlaBuffer.append(TLAConstants.ATTRIBUTE).append(attributeName).append(TLAConstants.CR);
		tlaBuffer.append(specDefinition[1]).append(CLOSING_SEP);
	}
	
	/**
	 * Add an init-next pair of definitions.
	 * 
	 * @param initDefinition the 0th element is the init definition name, the 1rst is the entire definition
	 * @param nextDefinition the 0th element is the next definition name, the 1rst is the entire definition
	 * @param initAttributeName
	 * @param nextAttributeName
	 */
	public void addInitNextDefinitions(final String[] initDefinition, final String[] nextDefinition,
									   final String initAttributeName, final String nextAttributeName) {
		if (cfgBuffer != null) {
			cfgBuffer.append(TLAConstants.COMMENT).append(TLAConstants.KeyWords.INIT).append(" definition");
			cfgBuffer.append(TLAConstants.CR).append(TLAConstants.KeyWords.INIT).append(TLAConstants.CR);
			cfgBuffer.append(initDefinition[0]).append(TLAConstants.CR);
		}

		tlaBuffer.append(TLAConstants.COMMENT).append(TLAConstants.KeyWords.INIT).append(" definition ");
		tlaBuffer.append(TLAConstants.ATTRIBUTE).append(initAttributeName).append(TLAConstants.CR);
		tlaBuffer.append(initDefinition[1]).append(TLAConstants.CR);

		
		if (cfgBuffer != null) {
			cfgBuffer.append(TLAConstants.COMMENT).append(TLAConstants.KeyWords.NEXT).append(" definition");
			cfgBuffer.append(TLAConstants.CR).append(TLAConstants.KeyWords.NEXT).append(TLAConstants.CR);
			cfgBuffer.append(nextDefinition[0]).append(TLAConstants.CR);
		}

		tlaBuffer.append(TLAConstants.COMMENT).append(TLAConstants.KeyWords.NEXT).append(" definition ");
		tlaBuffer.append(TLAConstants.ATTRIBUTE).append(nextAttributeName).append(TLAConstants.CR);
		tlaBuffer.append(nextDefinition[1]).append(TLAConstants.CR);
	}

	public void addConstants(List<String> rawConstants) {
		if (rawConstants.isEmpty()) {
			return;
		}
		cfgBuffer.append(TLAConstants.KeyWords.CONSTANTS);
		cfgBuffer.append("\n");	
		for (String constant : rawConstants) {
			cfgBuffer.append(constant);	
			cfgBuffer.append("\n");	
		}
	}

    /**
     * Documentation by SZ: Add constants declarations. 
     * 
     * On 17 March 2012, LL split the original addConstants method
     * into the current one plus the addConstantsBis method.  As explained in Bugzilla Bug 280,
     * this was to allow the user definitions added on the Advanced Model page to appear between
     * the CONSTANT declarations for model values and the definitions of the expressions that 
     * instantiate CONSTANT parameters.  (This allows symbols defined in those user definitions to
     * appear in the expressions instantiated for CONSTANT parameters.)
     * 
     * See the use of these two methods in TLCModelLaunchDelegate.buildForLaunch for a description
     * of what these methods do.
     * 
     * @param constants
     * @param modelValues
     * @param attributeConstants
     * @param attributeMVs
     */
	public void addConstants(final List<Assignment> constants, final TypedSet modelValues, final String attributeConstants,
			final String attributeMVs) {
        // add declarations for model values introduced on Advanced Model page.
        addMVTypedSet(modelValues, "MV CONSTANT declarations ", attributeMVs);

        final ArrayList<String> symmetrySets = new ArrayList<>();

        Assignment constant;
        // first run for all the declarations
		for (int i = 0; i < constants.size(); i++) {
			constant = constants.get(i);
			if (constant.isModelValue()) {
				if (constant.isSetOfModelValues()) {
					// set model values
					addMVTypedSet(constant.getSetOfModelValues(), "MV CONSTANT declarations", attributeConstants);
				}
			}
		}

        // now all the definitions
		for (int i = 0; i < constants.size(); i++) {
			constant = constants.get(i);
			if (constant.isModelValue()) {
				if (constant.isSetOfModelValues()) {
                    // set model values
					if (cfgBuffer != null) {
						cfgBuffer.append(TLAConstants.COMMENT).append("MV CONSTANT definitions").append(TLAConstants.CR);
					}
                    tlaBuffer.append(TLAConstants.COMMENT).append("MV CONSTANT definitions " + constant.getLeft());
                    tlaBuffer.append(TLAConstants.CR);

                    final String id = addArrowAssignment(constant, TLAConstants.Schemes.CONSTANT_SCHEME);
					if (constant.isSymmetricalSet()) {
						symmetrySets.add(id);
					}
                    tlaBuffer.append(TLAConstants.SEP).append(TLAConstants.CR).append(TLAConstants.CR);
				} else if (cfgBuffer != null) {
					cfgBuffer.append(TLAConstants.COMMENT).append(TLAConstants.KeyWords.CONSTANT)
							 .append(" declarations").append(TLAConstants.CR);
					// model value assignment
					// to .cfg : foo = foo
					// to _MC.tla : <nothing>, since the constant is already defined in one of the
					// spec modules
					cfgBuffer.append(TLAConstants.KeyWords.CONSTANT).append(TLAConstants.SPACE).append(constant.getLabel());
					cfgBuffer.append(TLAConstants.EQ).append(constant.getRight()).append(TLAConstants.CR);
				}
			} else {
//                // simple constant value assignment
//                cfgBuffer.append(COMMENT).append("CONSTANT definitions").append(CR);
//
//                tlaBuffer.append(COMMENT).append("CONSTANT definitions ").append(ATTRIBUTE).append(attributeConstants)
//                        .append(INDEX).append(i).append(constant.getLeft()).append(CR);
//                addArrowAssignment(constant, CONSTANT_SCHEME);
//                tlaBuffer.append(SEP).append(CR).append(CR);
            }
        }

        // symmetry
		if (!symmetrySets.isEmpty()) {
			final String label = SpecWriterUtilities.getValidIdentifier(TLAConstants.Schemes.SYMMETRY_SCHEME);

			tlaBuffer.append(TLAConstants.COMMENT).append(TLAConstants.KeyWords.SYMMETRY)
					 .append(" definition").append(TLAConstants.CR);
			if (cfgBuffer != null) {
				cfgBuffer.append(TLAConstants.COMMENT).append(TLAConstants.KeyWords.SYMMETRY)
						 .append(" definition").append(TLAConstants.CR);
			}

			tlaBuffer.append(label).append(TLAConstants.DEFINES).append(TLAConstants.CR);
			// symmetric model value sets added
			for (int i = 0; i < symmetrySets.size(); i++) {
				tlaBuffer.append(TLAConstants.BuiltInOperators.PERMUTATIONS).append("(");
				tlaBuffer.append(symmetrySets.get(i)).append(")");
				if (i != symmetrySets.size() - 1) {
					tlaBuffer.append(' ').append(TLAConstants.KeyWords.UNION).append(' ');
				}
			}

			tlaBuffer.append(CLOSING_SEP).append(TLAConstants.CR);
			if (cfgBuffer != null) {
				cfgBuffer.append(TLAConstants.KeyWords.SYMMETRY).append(TLAConstants.SPACE)
						 .append(label).append(TLAConstants.CR);
			}
		}
    }

	public void addConstantsBis(final List<Assignment> constants, final String attributeConstants) {
		for (int i = 0; i < constants.size(); i++) {
			final Assignment constant = constants.get(i);
			if (! constant.isModelValue()) {
				if (cfgBuffer != null) {
					// simple constant value assignment
					cfgBuffer.append(TLAConstants.COMMENT).append(TLAConstants.KeyWords.CONSTANT).append(" definitions");
					cfgBuffer.append(TLAConstants.CR);
				}

                tlaBuffer.append(TLAConstants.COMMENT).append(TLAConstants.KeyWords.CONSTANT).append(" definitions ");
                tlaBuffer.append(TLAConstants.ATTRIBUTE).append(attributeConstants).append(TLAConstants.COLON);
                tlaBuffer.append(i).append(constant.getLeft()).append(TLAConstants.CR);
                
                addArrowAssignment(constant, TLAConstants.Schemes.CONSTANT_SCHEME);
                
                tlaBuffer.append(TLAConstants.SEP).append(TLAConstants.CR).append(TLAConstants.CR);
            }
        }
    }

    /**
     * Adds the ASSUME PrintT statement and identifier for the constant expression
     * evaluation. The MC.tla file will contain:
     * 
     * const_expr_1232141234123 ==
     * expression
     * -----
     * ASSUME PrintT(<<"$!@$!@$!@$!@$!", const_expr_1232141234123>>)
     * 
     * See the comments in the method for an explanation of defining
     * an identifier.
     * 
     * @param expression
     * @param attributeName
     */
	public void addConstantExpressionEvaluation(final String expression, final String attributeName) {
		if (expression.trim().length() != 0) {
			/*
			 * Identifier definition We define an identifier for more sensible error
			 * messages For example, if the user enters "1+" into the constant expression
			 * field and "1+" is placed as the second element of the tuple that is the
			 * argument for PrintT(), then the parse error would be something like
			 * "Encountered >>" which would be mysterious to the user. With an identifier
			 * defined, the message says "Encountered ----" which is the separator after
			 * each section in TLA buffer. This error message is equally mysterious, but at
			 * least it is the same message that would appear were the same error present in
			 * another section in the model editor. We can potentially replace such messages
			 * with something more sensible in the future in the appendError() method in
			 * TLCErrorView.
			 */
			final String id = SpecWriterUtilities.getValidIdentifier(TLAConstants.Schemes.CONSTANTEXPR_SCHEME);
			tlaBuffer.append(TLAConstants.COMMENT).append("Constant expression definition ");
			tlaBuffer.append(TLAConstants.ATTRIBUTE).append(attributeName).append(TLAConstants.CR);
			tlaBuffer.append(id).append(TLAConstants.DEFINES).append(TLAConstants.CR).append(expression);
			tlaBuffer.append(CLOSING_SEP).append(TLAConstants.CR);

			// ASSUME PrintT(<<"$!@$!@$!@$!@$!", const_expr_23423232>>) statement
			// The "$!@$!@$!@$!@$!" allows the toolbox to identify the
			// value of the constant expression in the TLC output
			tlaBuffer.append(TLAConstants.COMMENT).append("Constant expression ASSUME statement ");
			tlaBuffer.append(TLAConstants.ATTRIBUTE).append(attributeName).append(TLAConstants.CR);
			tlaBuffer.append("ASSUME PrintT(").append(TLAConstants.BEGIN_TUPLE);
			tlaBuffer.append(TLAConstants.CONSTANT_EXPRESSION_EVAL_IDENTIFIER).append(TLAConstants.COMMA).append(id);
			tlaBuffer.append(TLAConstants.END_TUPLE).append(")").append(CLOSING_SEP).append(TLAConstants.CR);
		}
	}

    /**
     * New definitions are added to the TLA buffer only
     * @param defnitions
     * @param attributeName
     */
	public void addNewDefinitions(final String definitions, final String attributeName) {
		if (definitions.trim().length() == 0) {
			return;
		}
		tlaBuffer.append(TLAConstants.COMMENT).append("New definitions ");
		tlaBuffer.append(TLAConstants.ATTRIBUTE).append(attributeName).append(TLAConstants.CR);
		tlaBuffer.append(definitions).append(CLOSING_SEP);
	}

	/**
	 * Convenience method to call {@link #addFormulaList(List, String, String)} wrapping the {@code element} parameter.
	 * 
	 * @param element
	 * @param keyword
	 * @param attributeName
	 */
    public void addFormulaList(final String element, final String keyword, final String attributeName) {
    	final List<String[]> elements = new ArrayList<>(1);
    	elements.add(new String[] {element, TLAConstants.EMPTY_STRING});
    	addFormulaList(elements, keyword, attributeName);
    }
    
    /**
	 * Puts (String[])element[0] to configuration buffer; if this instance was
	 * appropriately constructed, and element[1] to the TLA buffer; if element[2]
	 * present, uses it as index.
	 * 
	 * @param elements      a list of String[] elements
	 * @param keyword       the keyword to be used in the CFG buffer
	 * @param attributeName the name of the attribute in the TLA buffer
	 */
	public void addFormulaList(final List<String[]> elements, final String keyword, final String attributeName) {
		if (elements.isEmpty()) {
			return;
		}
		
		if (cfgBuffer != null) {
			cfgBuffer.append(TLAConstants.COMMENT).append(keyword + " definition").append(TLAConstants.CR);
			cfgBuffer.append(keyword).append(TLAConstants.CR);
		}

		for (int i = 0; i < elements.size(); i++) {
			final String[] element = elements.get(i);
			
			if (cfgBuffer != null) {
				cfgBuffer.append(element[0]).append(TLAConstants.CR);
			}
			
			// when a definition in the root module is overridden as a model value
			// there is nothing to add to the MC.tla file so, we do not do the following
			if (!element[1].equals(TLAConstants.EMPTY_STRING)) {
				tlaBuffer.append(TLAConstants.COMMENT).append(keyword + " definition ").append(TLAConstants.ATTRIBUTE);
				tlaBuffer.append(attributeName).append(TLAConstants.COLON).append(element.length > 2 ? element[2] : i);
				tlaBuffer.append(TLAConstants.CR).append(element[1]).append(CLOSING_SEP);
			}
		}
	}

    /**
     * Add the view definition
     * @param viewString the string that the user enters into the view field
     * @param attributeName the attribute name of the view field
     */
	public void addView(final String viewString, final String attributeName) {
		if (viewString.trim().length() != 0) {
			final String id = SpecWriterUtilities.getValidIdentifier(TLAConstants.Schemes.VIEW_SCHEME);
			
			if (cfgBuffer != null) {
				cfgBuffer.append(TLAConstants.COMMENT).append("VIEW definition").append(TLAConstants.CR);
				cfgBuffer.append("VIEW").append(TLAConstants.CR).append(id).append(TLAConstants.CR);
			}

			tlaBuffer.append(TLAConstants.COMMENT).append("VIEW definition ").append(TLAConstants.ATTRIBUTE);
			tlaBuffer.append(attributeName).append(TLAConstants.CR);
			tlaBuffer.append(id).append(TLAConstants.DEFINES).append(TLAConstants.CR).append(viewString);
			tlaBuffer.append(CLOSING_SEP).append(TLAConstants.CR);
		}
	}
	
	public void addPostCondition(final String postConditionString, final String attributeName) {
		if (postConditionString.trim().length() != 0) {
			final String id = SpecWriterUtilities.getValidIdentifier(TLAConstants.Schemes.POST_CONDITION_SCHEME);
			
			if (cfgBuffer != null) {
				cfgBuffer.append(TLAConstants.COMMENT).append("POSTCONDITION definition").append(TLAConstants.CR);
				cfgBuffer.append("POSTCONDITION").append(TLAConstants.CR).append(id).append(TLAConstants.CR);
			}

			tlaBuffer.append(TLAConstants.COMMENT).append("POSTCONDITION definition ").append(TLAConstants.ATTRIBUTE);
			tlaBuffer.append(attributeName).append(TLAConstants.CR);
			tlaBuffer.append(id).append(TLAConstants.DEFINES).append(TLAConstants.CR).append(postConditionString);
			tlaBuffer.append(CLOSING_SEP).append(TLAConstants.CR);
		}
	}
	
	public void addAlias(final String aliasString, final String attributeName) {
		if (aliasString.trim().length() != 0) {
			final String id = SpecWriterUtilities.getValidIdentifier(TLAConstants.Schemes.ALIAS_SCHEME);
			this.addAliasToCfg(id);

			tlaBuffer.append(TLAConstants.COMMENT).append("ALIAS definition ").append(TLAConstants.ATTRIBUTE);
			tlaBuffer.append(attributeName).append(TLAConstants.CR);
			tlaBuffer.append(id).append(TLAConstants.DEFINES).append(TLAConstants.CR).append(aliasString);
			tlaBuffer.append(CLOSING_SEP).append(TLAConstants.CR);
		}
	}
	
	/**
	 * Specifies an alias in the config file.
	 * @param aliasName Name of the alias to specify.
	 */
	public void addAliasToCfg(final String aliasName) {
		if (this.cfgBuffer != null) {
			this.cfgBuffer.append(TLAConstants.CR);
			this.cfgBuffer.append("ALIAS").append(TLAConstants.CR);
			this.cfgBuffer.append(TLAConstants.INDENT).append(aliasName).append(TLAConstants.CR);
		}
	}
	
    /**
     * Assigns a right side to a label using an id generated from given schema
     * @param constant, constant containing the values
     * @param schema schema to generate the Id
     * @return generated id
     */
	public String addArrowAssignment(final Assignment constant, final String schema) {
		return addArrowAssignmentToBuffers(tlaBuffer, cfgBuffer, constant, schema);
	}

    /**
     * Creates a serial version of an MV set in both files
     * @param mvSet typed set containing the model values
     * @param comment a comment to put before the declarations, null and empty strings are OK
     */
	public void addMVTypedSet(final TypedSet mvSet, final String comment, final String attributeName) {
		if (mvSet.getValueCount() != 0) {
            // create a declaration line
            // CONSTANTS
            // a, b, c
			if ((comment != null) && (comment.length() != 0)) {
                tlaBuffer.append(TLAConstants.COMMENT).append(comment).append(TLAConstants.ATTRIBUTE);
                tlaBuffer.append(attributeName).append(TLAConstants.CR);
            }
            tlaBuffer.append(TLAConstants.KeyWords.CONSTANTS).append(TLAConstants.CR).append(mvSet.toStringWithoutBraces());
            tlaBuffer.append(CLOSING_SEP).append(TLAConstants.CR);

			if (cfgBuffer != null) {
				// create MV assignments
				// a = a
				// b = b
				// c = c
				if ((comment != null) && (comment.length() != 0)) {
					cfgBuffer.append(TLAConstants.COMMENT).append(comment).append(TLAConstants.CR);
				}
				cfgBuffer.append(TLAConstants.KeyWords.CONSTANTS).append(TLAConstants.CR);
				for (int i = 0; i < mvSet.getValueCount(); i++) {
					final String mv = mvSet.getValue(i);
					cfgBuffer.append(mv).append(TLAConstants.EQ).append(mv).append(TLAConstants.CR);
				}
			}
        }
    }
}
