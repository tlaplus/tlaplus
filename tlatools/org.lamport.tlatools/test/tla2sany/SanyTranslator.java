package tla2sany;

import tla2sany.modanalyzer.SyntaxTreePrinter;
import tla2sany.parser.SyntaxTreeNode;
import tla2sany.parser.TLAplusParser;
import tla2sany.parser.TLAplusParserConstants;
import tla2sany.st.SyntaxTreeConstants;
import tla2sany.AstNode.Kind;

import java.io.PrintWriter;
import java.text.ParseException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.junit.Assert;

/**
 * Handles the translation of raw SANY output to the test file AST DSL.
 */
public class SanyTranslator {	

	/**
	 * Sometimes SANY provides very little structure in its parse output,
	 * basically just a flat list of tokens. This is most common when dealing
	 * with constructs that SANY doesn't care much about, like proof-related
	 * rules. Thus we have to re-parse this output to find its structure.
	 * That is what this class helps with. It follows the parser pattern
	 * outlined in https://craftinginterpreters.com/parsing-expressions.html
	 */
	private static class SanyReparser {

		/**
		 * A list of parse nodes emitted by SANY.
		 */
		private SyntaxTreeNode[] nodes;

		/**
		 * The current node in the list we are looking at.
		 */
		private int current;

		/**
		 * Constructs a new SANY reparser instance.
		 * 
		 * @param nodes The list of nodes to look at.
		 * @param start Which node to start at.
		 */
		public SanyReparser(SyntaxTreeNode[] nodes, int start) {
			this.nodes = nodes;
			this.current = start;
		}
		
		/**
		 * Constructs a new SANY reparser instance that reads from the start
		 * of the nodes array.
		 * 
		 * @param nodes The list of nodes to start at.
		 */
		public SanyReparser(SyntaxTreeNode[] nodes) {
			this(nodes, 0);
		}
		
		/**
		 * Clones this parser for the purpose of speculatively looking ahead
		 * to try and parse something that is possibly not what is thought.
		 * 
		 * @return A shallow clone of this parser.
		 */
		public SanyReparser lookahead() {
			return new SanyReparser(this.nodes, this.current);
		}
		
		/**
		 * If the lookahead resulted in a successful parse, merge the
		 * lookahead parser state into this one. It should be discarded
		 * otherwise.
		 * 
		 * @param lookahead The lookahead parser state.
		 */
		public void merge(SanyReparser lookahead) {
			this.current = lookahead.current;
		}
		
		/**
		 * Whether we are at the end of the list of nodes.
		 * 
		 * @return True if there are no more nodes to look at.
		 */
		public boolean isAtEnd() {
			return this.current == this.nodes.length;
		}

		/**
		 * Gets the kind of the node previously looked at.
		 * 
		 * @return The kind of the node previously looked at.
		 */
		private SyntaxTreeNode previous() {
			return this.nodes[this.current - 1];
		}
		
		/**
		 * If not at the end of the list, advance then return the last node
		 * kind.
		 * 
		 * @return The kind of the node which was advanced past.
		 */
		private SyntaxTreeNode advance() {
			if (!this.isAtEnd()) {
				this.current++;
			}
			return this.previous();
		}
		
		/**
		 * Peek at the node currently being looked at.
		 * 
		 * @return The node currently being looked at.
		 */
		public SyntaxTreeNode peek() {
			return this.nodes[this.current];
		}
		
		/**
		 * Check whether current node is of the given kind.
		 * 
		 * @param kind The kind to check.
		 * @return True if the current node is of the given kind.
		 */
		public boolean check(int kind) {
			return !this.isAtEnd() && this.peek().isKind(kind);
		}
		
		/**
		 * If current node is one of the given kinds, advance past it then
		 * return true.
		 * 
		 * @param kinds The list of kinds to check against.
		 * @return True if current node is one of the given kinds.
		 */
		public boolean match(int... kinds) {
			for (int kind : kinds) {
				if (check(kind)) {
					advance();
					return true;
				}
			}
		
			return false;
		}

		/**
		 * Consume the given node kind, or throw exception if current node is
		 * not of that kind.
		 * 
		 * @param kind The kind of node to expect.
		 * @param expected The expected node; provided for error messages.
		 * @return The kind of node consumed.
		 * @throws ParseException If node kind is not what was given.
		 */
		public SyntaxTreeNode consume(String expected, int... kinds) throws ParseException {
			for (int kind : kinds) {
				if (check(kind)) return advance();
			}
			if (this.isAtEnd()) {
				throw new ParseException(String.format("EOF; expected %s", expected), this.current);
			} else {
				throw new ParseException(String.format("Expected %s; actual %d", expected, this.peek().getKind()), this.current);
			}
		}

		/**
		 * Translates then consumes the current node, 
		 * 
		 * @param expected The expected node; provided for error messages.
		 * @return The kind of node consumed.
		 * @throws ParseException If node kind is not what was given.
		 */
		public AstNode translate(String expected) throws ParseException {
			if (this.isAtEnd()) {
				throw new ParseException(String.format("EOF; expected %s", expected), this.current);
			} else {
				return SanyTranslator.translate(this.advance());
			}
		}

		/**
		 * Flat-translates then consumes the current node, 
		 * 
		 * @param parent Parent node to which to add children.
		 * @param errorMessage Exception method to throw if no node exists.
		 * @return The kind of node consumed.
		 * @throws ParseException If node kind is not what was given.
		 */
		public void flatTranslate(AstNode parent, String errorMessage) throws ParseException {
			if (this.isAtEnd()) {
				throw new ParseException(errorMessage, this.current);
			} else {
				SanyTranslator.flatTranslate(parent, this.advance());
			}
		}
	}
	
	/**
	 * Parse a comma-separated list of identifiers.
	 * Ex. x, y, z
	 * 
	 * @param parser The SANY reparser state.
	 * @return A list of identifiers.
	 * @throws ParseException If input is not a valid sequence of comma-separated identifiers.
	 */
	private static List<AstNode> parseCommaSeparatedIds(SanyReparser parser) throws ParseException {
		List<AstNode> ids = new ArrayList<AstNode>();
		do {
			parser.consume("Expected identifier", TLAplusParserConstants.IDENTIFIER);
			ids.add(Kind.IDENTIFIER.asNode());
		} while (parser.match(TLAplusParserConstants.COMMA));
		return ids;
	}
	
	private static List<AstNode> parseCommaSeparatedNodes(SanyReparser parser) throws ParseException {
		List <AstNode> nodes = new ArrayList<AstNode>();
		do {
			nodes.add(parser.translate("Expected definition or expression"));
		} while (parser.match(TLAplusParserConstants.COMMA));
		return nodes;
	}
	
	/**
	 * Parse a tuple of identifiers.
	 * Ex. <<x, y, z>>
	 * 
	 * @param parser The SANY reparser state.
	 * @return An AST node for the tuple of identifiers.
	 * @throws ParseException If input is not a valid tuple of identifiers.
	 */
	private static AstNode parseTupleOfIdentifiers(SanyReparser parser) throws ParseException {
		AstNode tuple = Kind.TUPLE_OF_IDENTIFIERS.asNode();
		parser.consume("Expected <<", TLAplusParserConstants.LAB);
		tuple.addChild(Kind.LANGLE_BRACKET.asNode());
		tuple.addChildren(parseCommaSeparatedIds(parser));
		parser.consume("Expected >>", TLAplusParserConstants.RAB);
		tuple.addChild(Kind.RANGLE_BRACKET.asNode());
		return tuple;
	}
	
	/**
	 * Parses a quantifier bound.
	 * Ex. <<x, y, z>> \in Nat \X Nat \X Nat
	 * 
	 * @param parser The SANY reparser state.
	 * @return An AST node for the quantifier bound.
	 * @throws ParseException If input is not a valid quantifier bound.
	 */
	private static AstNode parseQuantifierBound(SanyReparser parser) throws ParseException {
		AstNode bound = Kind.QUANTIFIER_BOUND.asNode();
		if (parser.check(TLAplusParserConstants.LAB)) {
			bound.addChild(parseTupleOfIdentifiers(parser));
		} else if (parser.check(TLAplusParserConstants.IDENTIFIER)) {
			bound.addChildren(parseCommaSeparatedIds(parser));
		} else {
			throw new ParseException(String.format("Failed to parse quantifier bound %d", parser.peek()), parser.current);
		}
		parser.consume("Expected \\in", SyntaxTreeConstants.T_IN);
		bound.addChild(Kind.SET_IN.asNode());
		bound.addField("set", parser.translate("Expected expression"));
		return bound;
	}

	/**
	 * Parses a list of either quantifier bounds or simple comma-separated
	 * identifiers. This is used in both TAKE and PICK proof steps.
	 *  
	 * @param parser The SANY reparser state.
	 * @return 
	 * @throws ParseException
	 */
	private static List<AstNode> parseBoundListOrIdentifierList(SanyReparser parser) throws ParseException {
		List<AstNode> children = new ArrayList<AstNode>();
		// Lookahead to try parsing comma-separated list of quantifier bounds
		SanyReparser lookahead = parser.lookahead();
		try {
			do {
				children.add(parseQuantifierBound(lookahead));
			} while (lookahead.match(TLAplusParserConstants.COMMA));
			parser.merge(lookahead);
			return children;
		} catch (ParseException e) {
			// It must be a list of identifiers instead
			children.addAll(parseCommaSeparatedIds(parser));
			return children;
		}
	}
	
	private static List<AstNode> repeat(SyntaxTreeNode node) throws ParseException {
		List<AstNode> children = new ArrayList<AstNode>();
		for (SyntaxTreeNode child : node.getHeirs()) {
			children.add(translate(child));
		}
		
		return children;
	}
	
	private static int parseUseBodyDefs(SyntaxTreeNode[] heirs, int offset, AstNode useBodyExpr) throws ParseException {
		AstNode moduleRef = null;
		for (; offset < heirs.length && !heirs[offset].isKind(TLAplusParserConstants.DF); offset++) {
			switch (heirs[offset].getKind()) {
				case TLAplusParserConstants.COMMA: {
					break;
				}
				case TLAplusParserConstants.MODULE: {
					moduleRef = Kind.MODULE_REF.asNode();
					break;
				} case TLAplusParserConstants.IDENTIFIER: {
					if (null == moduleRef) {
						useBodyExpr.addChild(Kind.IDENTIFIER_REF.asNode());
					} else {
						moduleRef.addChild(Kind.IDENTIFIER_REF.asNode());
						useBodyExpr.addChild(moduleRef);
						moduleRef = null;
					}
						break;
				}
				default: {
					useBodyExpr.addChild(translate(heirs[offset]));
					break;
				}
			}
		}
		return offset;
	}
	
	/**
	 * Unfortunately SANY does not do much structured parsing of proof
	 * structures (which makes sense since TLAPM has its own parser) so we
	 * have to parse the flat sequence of tokens ourselves.
	 * 
	 * @param heirs The heirs of the terminal proof node.
	 * @param offset Offset into the heirs after which BY ONLY occurs.
	 * @return A use body AST node.
	 * @throws ParseException
	 */
	private static AstNode parseUseBody(SyntaxTreeNode[] heirs, int offset) throws ParseException {
		AstNode useBody = Kind.USE_BODY.asNode();
		if (heirs[offset].isKind(TLAplusParserConstants.ONLY)) {
			offset++;
		}
		if (!heirs[offset].isKind(TLAplusParserConstants.DF)) {
			AstNode useBodyExpr = Kind.USE_BODY_EXPR.asNode();
			useBody.addChild(useBodyExpr);
			offset = parseUseBodyDefs(heirs, offset, useBodyExpr);
		}
		if (offset < heirs.length) { 
			Assert.assertEquals(TLAplusParserConstants.DF, heirs[offset].getKind());
			offset++;
			AstNode useBodyDef = Kind.USE_BODY_DEF.asNode();
			useBody.addChild(useBodyDef);
			offset = parseUseBodyDefs(heirs, offset, useBodyDef);
		}
		return useBody;
	}
	
	private static AstNode id(SyntaxTreeNode input) throws ParseException {
		Assert.assertEquals(TLAplusParserConstants.IDENTIFIER, input.getKind());
		switch (input.getImage()) {
			case "TRUE": return Kind.BOOLEAN.asNode();
			default: return Kind.IDENTIFIER_REF.asNode();
		}
	}
	
	/**
	 * Gets a prefix op AST node from a string representation of it.
	 * 
	 * @param op String representation of a prefix operator.
	 * @return AST node corresponding to the given prefix operator string.
	 * @throws ParseException If op string has no corresponding AST node.
	 */
	private static AstNode prefixOpFromString(String op) throws ParseException {
		switch (op) {
			case "SUBSET": return Kind.POWERSET.asNode();
			default: throw new ParseException(String.format("Operator translation not defined: %s", op), 0);
		}
	}
	
	/**
	 * Gets an infix op AST node from a string representation of it.
	 * 
	 * @param op String representation of an infix operator.
	 * @return AST node corresponding to the given infix operator string.
	 * @throws ParseException If op string has no corresponding AST node.
	 */
	private static AstNode infixOpFromString(String op) throws ParseException {
		switch (op) {
			case "/\\": return Kind.LAND.asNode();
			case "\\/": return Kind.LOR.asNode();
			case "+": return Kind.PLUS.asNode();
			case "-": return Kind.MINUS.asNode();
			case "*": return Kind.MUL.asNode();
			case "/": return Kind.SLASH.asNode();
			case "=": return Kind.EQ.asNode();
			case ">": return Kind.GT.asNode();
			case "=<": return Kind.LEQ.asNode();
			case "\\in": return Kind.IN.asNode();
			case "\\union": return Kind.CUP.asNode();
			case "\\intersect": return Kind.CAP.asNode();
			case "=>": return Kind.IMPLIES.asNode();
			case "\\o": return Kind.CIRC.asNode();
			default: throw new ParseException(String.format("Operator translation not defined: %s", op), 0);
		}
	}
	
	/**
	 * Chops the beginning & ending elements off of the given array, starting
	 * from the given index.
	 * 
	 * @param input The array to chop.
	 * @param startIndex Index from which to start chopping.
	 * @return Array with first and last elements removed.
	 */
	private static SyntaxTreeNode[] chop(SyntaxTreeNode[] input, int startIndex) {
		return Arrays.copyOfRange(input, startIndex, input.length - 1);
	}
	
	/**
	 * Chops the beginning & ending elements off of the given array. Useful
	 * when dealing with an array like ["(", <thing you care about>, ")"].
	 * Often used with a call to commaSeparated.
	 * 
	 * @param input The array to chop.
	 * @return Array with first and last elements removed.
	 */
	private static SyntaxTreeNode[] chop(SyntaxTreeNode[] input) {
		return chop(input, 1);
	}
	
	/**
	 * Translates a variable-length comma-separated list of children into
	 * a list of AST nodes.
	 * 
	 * @param heirs The comma-separated heirs to process.
	 * @return Corresponding list of AST nodes.
	 * @throws ParseException If unable to parse one of the nodes.
	 */
	private static List<AstNode> commaSeparated(SyntaxTreeNode[] heirs) throws ParseException {
		List<AstNode> children = new ArrayList<AstNode>();
		for (int i = 0; i < heirs.length; i += 2) {
			children.add(translate(heirs[i]));
			if (i < heirs.length - 1) {
				Assert.assertEquals(TLAplusParserConstants.COMMA, heirs[i+1].getKind());
			}
		}
		return children;
	}
	
	/**
	 * Similar to the translate method, but for node types where SANY has an
	 * extra intermediate node that the AST DSL flattens out. Instead of a
	 * new node being created and returned, nodes are added to the provided
	 * parent node.
	 * 
	 * @param parent The parent node to which to add children.
	 * @param node The SANY node type to translate.
	 * @throws ParseException If a translation is not yet defined for the node.
	 */
	private static void flatTranslate(AstNode parent, SyntaxTreeNode node) throws ParseException {
		SyntaxTreeNode[] heirs = node.getHeirs();
		SanyReparser parser = new SanyReparser(heirs);
		switch (node.getKind()) {
			case SyntaxTreeConstants.N_IdentLHS: { // f ==, f(a, b) ==, etc.
				parser.consume("Expected identifier", TLAplusParserConstants.IDENTIFIER);
				parent.addField("name", Kind.IDENTIFIER.asNode());
				if (parser.match(TLAplusParserConstants.LBR)) {
					do {
						// TODO: handle & test for operator declarations ex. _ + _
						parent.addChild(translate(parser.consume("parameter", SyntaxTreeConstants.N_IdentDecl)));
					} while (parser.match(TLAplusParserConstants.COMMA));
					parser.consume("Expected )", TLAplusParserConstants.RBR);
				}
				break;
			} case SyntaxTreeConstants.N_OpArgs: { // (p1, p2, ..., pn)
				parser.consume("Expected (", TLAplusParserConstants.LBR);
				parent.addChildren(parseCommaSeparatedNodes(parser));
				parser.consume("Expected )", TLAplusParserConstants.RBR);
				break;
			} default: {
				throw new ParseException(String.format("Unhandled conversion from kind %d image %s", node.getKind(), node.getImage()), 0);
			}
		}
		Assert.assertTrue(parser.isAtEnd());
	}
	
	/**
	 * A somewhat monstrous function which translates the parse tree emitted
	 * by SANY to the parse tree defined by the AST DSL. This function has a
	 * lot of cases but the translation process is very mechanical. This
	 * function also serves as an in-depth regression test on the format of
	 * SANY's parse tree, due to all the included assertions.
	 * 
	 * In the event that a new test is added for a node kind which does not
	 * yet have a defined translation, the thrown ParseException should
	 * contain info on the kind ID. Search this kind ID in either SyntaxTreeConstants
	 * or TLAplusParserConstants, add a new case to the top-level switch
	 * statement for the kind ID, then set a debug breakpoint in that case.
	 * Run the test in the debugger to look at the object emitted by SANY;
	 * the node children will be in some order in the heirs array. In this
	 * fashion you can define the necessary translation to the AST DSL by
	 * copying the approach taken in other switch branches. Don't be
	 * intimidated! It is easier than it looks. It helps to add assert
	 * statements as documentation of what kinds SANY emits in each heir.
	 * 
	 * @param node The SANY syntax node to translate to the AST DSL node.
	 * @return An AST DSL node corresponding to the given SANY node.
	 * @throws ParseException If a translation is not yet defined for the node.
	 */
	public static AstNode translate(SyntaxTreeNode node) throws ParseException {
		SyntaxTreeNode[] heirs = node.getHeirs();
		SanyReparser parser = new SanyReparser(heirs);
		switch (node.getKind()) {
			case SyntaxTreeConstants.N_Module: { // ---- MODULE Test ---- ... ====
				AstNode module = Kind.MODULE.asNode();
				Assert.assertEquals(4, heirs.length);
				Assert.assertEquals(SyntaxTreeConstants.N_BeginModule, heirs[0].getKind());
				SyntaxTreeNode header = heirs[0];
				SyntaxTreeNode[] headerHeirs = header.getHeirs();
				Assert.assertEquals(3, headerHeirs.length);
				int kind = headerHeirs[0].getKind();
				Assert.assertTrue(kind == TLAplusParserConstants._BM0 || kind == TLAplusParserConstants._BM1);
				module.addChild(Kind.HEADER_LINE.asNode());
				Assert.assertEquals(TLAplusParserConstants.IDENTIFIER, headerHeirs[1].getKind());
				module.addField("name", Kind.IDENTIFIER.asNode());
				Assert.assertEquals(TLAplusParserConstants.SEPARATOR, headerHeirs[2].getKind());
				module.addChild(Kind.HEADER_LINE.asNode());
				Assert.assertEquals(SyntaxTreeConstants.N_Extends, heirs[1].getKind());
				module.addChildren(repeat(heirs[1]));
				Assert.assertEquals(SyntaxTreeConstants.N_Body, heirs[2].getKind());
				module.addChildren(repeat(heirs[2]));
				Assert.assertEquals(SyntaxTreeConstants.N_EndModule, heirs[3].getKind());
				module.addChild(translate(heirs[3]));
				return module;
			} case SyntaxTreeConstants.N_EndModule: { // ====
				Assert.assertEquals(1, heirs.length);
				Assert.assertEquals(TLAplusParserConstants.END_MODULE, heirs[0].getKind());
				return Kind.DOUBLE_LINE.asNode();
			} case TLAplusParserConstants.SEPARATOR: { // ----
				return Kind.SINGLE_LINE.asNode();
			} case SyntaxTreeConstants.N_VariableDeclaration: { // VARIABLES x, y, z
				AstNode variables = Kind.VARIABLE_DECLARATION.asNode();
				Assert.assertTrue(heirs.length >= 2);
				Assert.assertEquals(TLAplusParserConstants.VARIABLE, heirs[0].getKind());
				for (int i = 1; i < heirs.length; i += 2) {
					Assert.assertEquals(TLAplusParserConstants.IDENTIFIER, heirs[i].getKind());
					variables.addChild(Kind.IDENTIFIER.asNode());
					if (i + 1 < heirs.length) {
						Assert.assertEquals(TLAplusParserConstants.COMMA, heirs[i+1].getKind());
					}
				}
				return variables;
			} case SyntaxTreeConstants.N_Instance: { // INSTANCE M, LOCAL INSTANCE N, etc.
				Assert.assertTrue(heirs.length == 1 || heirs.length == 2);
				if (1 == heirs.length) {
					Assert.assertEquals(SyntaxTreeConstants.N_NonLocalInstance, heirs[0].getKind());
					return translate(heirs[0]);
				} else {
					AstNode localDefn = Kind.LOCAL_DEFINITION.asNode();
					Assert.assertEquals(TLAplusParserConstants.LOCAL, heirs[0].getKind());
					Assert.assertEquals(SyntaxTreeConstants.N_NonLocalInstance, heirs[1].getKind());
					localDefn.addChild(translate(heirs[1]));
					return localDefn;
				}
			} case SyntaxTreeConstants.N_NonLocalInstance: { // INSTANCE M WITH a <- b, c <- d
				AstNode instance = Kind.INSTANCE.asNode();
				Assert.assertTrue(heirs.length >= 2);
				Assert.assertEquals(TLAplusParserConstants.INSTANCE, heirs[0].getKind());
				Assert.assertEquals(TLAplusParserConstants.IDENTIFIER, heirs[1].getKind());
				instance.addChild(Kind.IDENTIFIER_REF.asNode());
				if (heirs.length > 2) {
					Assert.assertEquals(TLAplusParserConstants.WITH, heirs[2].getKind());
					instance.addChildren(commaSeparated(Arrays.copyOfRange(heirs, 3, heirs.length)));
				}
				return instance;
			} case SyntaxTreeConstants.N_ModuleDefinition: {
				AstNode moduleDefinition = Kind.MODULE_DEFINITION.asNode();
				Assert.assertEquals(3, heirs.length);
				Assert.assertEquals(SyntaxTreeConstants.N_IdentLHS, heirs[0].getKind());
				flatTranslate(moduleDefinition, heirs[0]);
				Assert.assertEquals(TLAplusParserConstants.DEF, heirs[1].getKind());
				moduleDefinition.addChild(Kind.DEF_EQ.asNode());
				Assert.assertEquals(SyntaxTreeConstants.N_NonLocalInstance, heirs[2].getKind());
				moduleDefinition.addChild(translate(heirs[2]));
				return moduleDefinition;
			} case SyntaxTreeConstants.N_Substitution: {
				AstNode substitution = Kind.SUBSTITUTION.asNode();
				Assert.assertEquals(3, heirs.length);
				// heirs[0] is some identifier or prefix/infix/postfix op
				substitution.addChild(translate(heirs[0]));
				Assert.assertEquals(TLAplusParserConstants.SUBSTITUTE, heirs[1].getKind());
				substitution.addChild(Kind.GETS.asNode());
				// heirs[2] is some operator or expression
				substitution.addChild(translate(heirs[2]));
				return substitution;
			} case SyntaxTreeConstants.N_OperatorDefinition: { // ex. op(a, b) == expr
				AstNode operatorDefinition = Kind.OPERATOR_DEFINITION.asNode();
				Assert.assertEquals(3, heirs.length);
				switch (heirs[0].getKind()) {
					case SyntaxTreeConstants.N_IdentLHS: {
						flatTranslate(operatorDefinition, heirs[0]);
						break;
					} case SyntaxTreeConstants.N_PrefixLHS: {
						Assert.fail("Unimplemented");
					} case SyntaxTreeConstants.N_InfixLHS: {
						Assert.fail("Unimplemented");
					} case SyntaxTreeConstants.N_PostfixLHS: {
						Assert.fail("Unimplemented");
					} default: {
						throw new ParseException(String.format("Invalid operator definition LHS kind %d, image %s", heirs[0].getKind(), heirs[0].image), 0);
					}
				}
				Assert.assertEquals(TLAplusParserConstants.DEF, heirs[1].getKind());
				operatorDefinition.addChild(translate(heirs[1]));
				// heirs[2] is of indeterminate expression type
				operatorDefinition.addField("definition", translate(heirs[2]));
				return operatorDefinition;
			} case SyntaxTreeConstants.N_IdentDecl: { // f ==, f(a, b) ==, etc.
				Assert.assertTrue(heirs.length >= 1);
				Assert.assertEquals(TLAplusParserConstants.IDENTIFIER, heirs[0].getKind());
				if (1 == heirs.length) {
					return Kind.IDENTIFIER.asNode();
				} else {
					Assert.assertTrue(heirs.length >= 4);
					AstNode opDeclaration = Kind.OPERATOR_DECLARATION.asNode();
					opDeclaration.addField("name", Kind.IDENTIFIER.asNode());
					Assert.assertEquals(TLAplusParserConstants.LBR, heirs[1].getKind());
					// TODO: test multiple placeholders
					opDeclaration.addChildren(commaSeparated(chop(heirs, 2)));
					Assert.assertEquals(TLAplusParserConstants.RBR, heirs[heirs.length-1].getKind());
					return opDeclaration;
				}
			} case SyntaxTreeConstants.N_Recursive: { // RECURSIVE F(_, _), G(_)
				AstNode recursiveDeclaration = Kind.RECURSIVE_DECLARATION.asNode();
				Assert.assertEquals(2, heirs.length);
				Assert.assertEquals(TLAplusParserConstants.RECURSIVE, heirs[0].getKind());
				Assert.assertEquals(SyntaxTreeConstants.N_IdentDecl, heirs[1].getKind());
				recursiveDeclaration.addChild(translate(heirs[1]));
				// TODO: test comma-separated recursive declarations
				return recursiveDeclaration;
			} case TLAplusParserConstants.US: {
				return Kind.PLACEHOLDER.asNode();
			} case TLAplusParserConstants.DEF: { // ==
				Assert.assertEquals(0, heirs.length);
				return Kind.DEF_EQ.asNode();
			} case SyntaxTreeConstants.N_ConjList: { // Multi-line aligned conjunction list
				AstNode conjList = Kind.CONJ_LIST.asNode();
				for (SyntaxTreeNode heir : heirs) {
					Assert.assertEquals(SyntaxTreeConstants.N_ConjItem, heir.getKind());
					conjList.addChild(translate(heir));
				}
				return conjList;
			} case SyntaxTreeConstants.N_ConjItem: { // /\ expr
				AstNode conjItem = Kind.CONJ_ITEM.asNode();
				Assert.assertEquals(2, heirs.length);
				Assert.assertEquals(TLAplusParserConstants.AND, heirs[0].getKind());
				conjItem.addChild(Kind.BULLET_CONJ.asNode());
				// heirs[1] is of indeterminate expression type
				conjItem.addChild(translate(heirs[1]));
				return conjItem;
			} case SyntaxTreeConstants.N_DisjList: { // Multi-line aligned disjunction list
				AstNode disjList = Kind.DISJ_LIST.asNode();
				for (SyntaxTreeNode heir : heirs) {
					Assert.assertEquals(SyntaxTreeConstants.N_DisjItem, heir.getKind());
					disjList.addChild(translate(heir));
				}
				return disjList;
			} case SyntaxTreeConstants.N_DisjItem: { // \/ expr
				AstNode disjItem = Kind.DISJ_ITEM.asNode();
				Assert.assertEquals(2, heirs.length);
				Assert.assertEquals(TLAplusParserConstants.OR, heirs[0].getKind());
				disjItem.addChild(Kind.BULLET_DISJ.asNode());
				// heirs[1] is of indeterminate expression type
				disjItem.addChild(translate(heirs[1]));
				return disjItem;
			} case SyntaxTreeConstants.N_GeneralId: { // foo!bar!baz!x
				Assert.assertEquals(2, heirs.length);
				// TODO: handle ID prefix
				Assert.assertEquals(SyntaxTreeConstants.N_IdPrefix, heirs[0].getKind());
				SyntaxTreeNode[] prefix = heirs[0].getHeirs();
				AstNode prefixedOp = null;
				if (0 != prefix.length) {
					prefixedOp = Kind.PREFIXED_OP.asNode();
					prefixedOp.addField("prefix", translate(heirs[0]));
				}

				AstNode op = null;
				switch (heirs[1].getKind()) {
					case TLAplusParserConstants.IDENTIFIER: {
						op = translate(heirs[1]);
						break;
					} case SyntaxTreeConstants.N_InfixOp: {
						op = Kind.INFIX_OP_SYMBOL.asNode().addChild(translate(heirs[1]));
						break;
					} case SyntaxTreeConstants.N_NonExpPrefixOp: {
						op = Kind.PREFIX_OP_SYMBOL.asNode().addChild(Kind.NEGATIVE.asNode());
						break;
					} default: {
						Assert.fail(heirs[1].getImage());
					}
				}
				
				return prefixedOp == null ? op : prefixedOp.addField("op", op);
			} case SyntaxTreeConstants.N_IdPrefix: {
				AstNode subexpr = Kind.SUBEXPR_PREFIX.asNode();
				Assert.assertTrue(heirs.length > 0);
				for (SyntaxTreeNode heir : heirs) {
					subexpr.addChild(translate(heir));
				}
				return subexpr;
			} case SyntaxTreeConstants.N_IdPrefixElement: {
				Assert.assertEquals(2, heirs.length);
				Assert.assertEquals(TLAplusParserConstants.IDENTIFIER, heirs[0].getKind());
				Assert.assertEquals(TLAplusParserConstants.BANG, heirs[1].getKind());
				return Kind.SUBEXPR_COMPONENT.asNode()
						.addChild(Kind.IDENTIFIER_REF.asNode());
			} case TLAplusParserConstants.IDENTIFIER: { // ex. x
				Assert.assertEquals(0, heirs.length);
				return id(node);
			} case SyntaxTreeConstants.N_Number: { // 1, 3, 100, etc.
				Assert.assertEquals(1, heirs.length);
				Assert.assertEquals(TLAplusParserConstants.NUMBER_LITERAL, heirs[0].getKind());
				String image = heirs[0].image.toString();
				if (image.matches("\\d+")) {
					return Kind.NAT_NUMBER.asNode();
				} else if (image.matches("\\\\[bB][0|1]+")) {
					return Kind.BINARY_NUMBER.asNode()
							.addChild(Kind.FORMAT.asNode())
							.addChild(Kind.VALUE.asNode());
				} else if (image.matches("\\\\[oO][0-7]+")) {
					return Kind.OCTAL_NUMBER.asNode()
							.addChild(Kind.FORMAT.asNode())
							.addChild(Kind.VALUE.asNode());
				} else if (image.matches("\\\\[hH][0-9a-fA-F]+")) {
					return Kind.HEX_NUMBER.asNode()
							.addChild(Kind.FORMAT.asNode())
							.addChild(Kind.VALUE.asNode());
				} else {
					throw new ParseException(String.format("Invalid number literal format %s", image), 0);
				}
			} case SyntaxTreeConstants.N_Real: { // 2.178, 3.14, etc.
				Assert.assertEquals(3, heirs.length);
				Assert.assertEquals(TLAplusParserConstants.NUMBER_LITERAL, heirs[0].getKind());
				Assert.assertEquals(TLAplusParserConstants.DOT, heirs[1].getKind());
				Assert.assertEquals(TLAplusParserConstants.NUMBER_LITERAL, heirs[2].getKind());
				return Kind.REAL_NUMBER.asNode();
			} case SyntaxTreeConstants.N_String: { // ex. "foobar"
				AstNode string = Kind.STRING.asNode();
				Assert.assertEquals(0, heirs.length);
				System.out.println(node.image);
				int[] codepoints = node.image.toString().codePoints().toArray();
				// The AST DSL records escaped characters in strings
				for (int i = 0; i < codepoints.length; i++) {
					int c = codepoints[i];
					if (0 == i || codepoints.length - 1 == i) {
						// SANY includes the start & end quotes in the string
						continue;
					}
					if (c == '\\' || c == '\'' || c == '\"' || c == '\n' || c == '\r' || c == '\t') {
						string.addChild(Kind.ESCAPE_CHAR.asNode());
					}
				}
				return string;
			} case SyntaxTreeConstants.N_Tuple: { // ex. <<1, 2, 3>>
				AstNode tuple = Kind.TUPLE_LITERAL.asNode();
				Assert.assertTrue(heirs.length >= 2);
				Assert.assertEquals(TLAplusParserConstants.LAB, heirs[0].getKind());
				tuple.addChild(translate(heirs[0]));
				tuple.addChildren(commaSeparated(chop(heirs)));
				Assert.assertEquals(TLAplusParserConstants.RAB, heirs[heirs.length-1].getKind());
				tuple.addChild(translate(heirs[heirs.length-1]));
				return tuple;
			} case TLAplusParserConstants.LAB: { // <<
				Assert.assertEquals(0, heirs.length);
				return Kind.LANGLE_BRACKET.asNode();
			} case TLAplusParserConstants.RAB: { // >>
				Assert.assertEquals(0, heirs.length);
				return Kind.RANGLE_BRACKET.asNode();
			} case SyntaxTreeConstants.N_SetEnumerate: { // {1, 3, 5}
				AstNode setLiteral = Kind.FINITE_SET_LITERAL.asNode();
				Assert.assertTrue(heirs.length >= 2);
				Assert.assertEquals(TLAplusParserConstants.LBC, heirs[0].getKind());
				setLiteral.addChildren(commaSeparated(chop(heirs)));
				Assert.assertEquals(TLAplusParserConstants.RBC, heirs[heirs.length-1].getKind());
				return setLiteral;
			} case SyntaxTreeConstants.N_SubsetOf: { // {x \in S : P(x)}
				AstNode setFilter = Kind.SET_FILTER.asNode();
				parser.consume("Expected {", TLAplusParserConstants.LBC);
				setFilter.addField("generator", parseQuantifierBound(parser));
				parser.consume("Expected :", TLAplusParserConstants.COLON);
				setFilter.addField("filter", parser.translate("Expected expression"));
				parser.consume("Expected }", TLAplusParserConstants.RBC);
				Assert.assertTrue(parser.isAtEnd());
				return setFilter;
			} case SyntaxTreeConstants.N_SetOfFcns: { // [S -> P]
				AstNode setOfFunctions = Kind.SET_OF_FUNCTIONS.asNode();
				Assert.assertEquals(5, heirs.length);
				Assert.assertEquals(TLAplusParserConstants.LSB, heirs[0].getKind());
				// heirs[1] is of indeterminate expression type
				setOfFunctions.addChild(translate(heirs[1]));
				Assert.assertEquals(TLAplusParserConstants.ARROW, heirs[2].getKind());
				setOfFunctions.addChild(Kind.MAPS_TO.asNode());
				// heirs[3] is of indeterminate expression type
				setOfFunctions.addChild(translate(heirs[3]));
				Assert.assertEquals(TLAplusParserConstants.RSB, heirs[4].getKind());
				return setOfFunctions;
			} case SyntaxTreeConstants.N_IfThenElse: { // IF x THEN y ELSE z
				AstNode ite = Kind.IF_THEN_ELSE.asNode();
				Assert.assertEquals(6, heirs.length);
				Assert.assertEquals(TLAplusParserConstants.IF, heirs[0].getKind());
				// heirs[1] is of indeterminate expression type
				ite.addField("if", translate(heirs[1]));
				Assert.assertEquals(TLAplusParserConstants.THEN, heirs[2].getKind());
				// heirs[3] is of indeterminate expression type
				ite.addField("then", translate(heirs[3]));
				Assert.assertEquals(TLAplusParserConstants.ELSE, heirs[4].getKind());
				// heirs[5] is of indeterminate expression type
				ite.addField("else", translate(heirs[5]));
				return ite;
			} case SyntaxTreeConstants.N_Case: { // CASE A -> B [] C -> D [] OTHER -> E
				AstNode cases = Kind.CASE.asNode();
				Assert.assertTrue(heirs.length >= 2);
				Assert.assertEquals(TLAplusParserConstants.CASE, heirs[0].getKind());
				Assert.assertEquals(SyntaxTreeConstants.N_CaseArm, heirs[1].getKind());
				cases.addChild(translate(heirs[1]));
				int offset = 2;
				while (offset < heirs.length) {
					Assert.assertEquals(TLAplusParserConstants.CASESEP, heirs[offset].getKind());
					cases.addChild(Kind.CASE_BOX.asNode());
					offset++;
					if (offset == heirs.length - 1) {
						Assert.assertTrue(heirs[offset].isKind(SyntaxTreeConstants.N_CaseArm) || heirs[offset].isKind(SyntaxTreeConstants.N_OtherArm));
					} else {
						Assert.assertEquals(SyntaxTreeConstants.N_CaseArm, heirs[offset].getKind());
					}
					cases.addChild(translate(heirs[offset]));
					offset++;
				}
				return cases;
			} case SyntaxTreeConstants.N_CaseArm: { // P -> Q
				AstNode caseArm = Kind.CASE_ARM.asNode();
				Assert.assertEquals(3, heirs.length);
				// heirs[0] is of indeterminate expression type
				caseArm.addChild(translate(heirs[0]));
				Assert.assertEquals(TLAplusParserConstants.ARROW, heirs[1].getKind());
				caseArm.addChild(Kind.CASE_ARROW.asNode());
				// heirs[2] is of indeterminate expression type
				caseArm.addChild(translate(heirs[2]));
				return caseArm;
			} case SyntaxTreeConstants.N_OtherArm: { // OTHER -> expr
				AstNode otherArm = Kind.OTHER_ARM.asNode();
				Assert.assertEquals(3, heirs.length);
				Assert.assertEquals(TLAplusParserConstants.OTHER, heirs[0].getKind());
				Assert.assertEquals(TLAplusParserConstants.ARROW, heirs[1].getKind());
				otherArm.addChild(Kind.CASE_ARROW.asNode());
				// heirs[2] is of indeterminate expression type
				otherArm.addChild(translate(heirs[2]));
				return otherArm;
			} case SyntaxTreeConstants.N_ActionExpr: { // [expr]_subexpr or <<expr>>_subexpr
				boolean allowStutter = heirs[0].isKind(TLAplusParserConstants.LSB);
				AstNode actionExpr = allowStutter ? Kind.STEP_EXPR_OR_STUTTER.asNode() : Kind.STEP_EXPR_NO_STUTTER.asNode();
				Assert.assertEquals(allowStutter ? TLAplusParserConstants.LSB : TLAplusParserConstants.LAB, heirs[0].getKind());
				if (!allowStutter) {
					actionExpr.addChild(Kind.LANGLE_BRACKET.asNode());
				}
				// heirs[1] is of indeterminate expression type
				actionExpr.addChild(translate(heirs[1]));
				Assert.assertEquals(allowStutter ? TLAplusParserConstants.ARSB : TLAplusParserConstants.ARAB, heirs[2].getKind());
				if (!allowStutter) {
					actionExpr.addChild(Kind.RANGLE_BRACKET_SUB.asNode());
				}
				// heirs[3] is of indeterminate subscript expression type
				actionExpr.addChild(translate(heirs[3]));
				return actionExpr;
			} case SyntaxTreeConstants.N_FairnessExpr: { // WF_x(action)
				AstNode fairness = Kind.FAIRNESS.asNode();
				Assert.assertEquals(5, heirs.length);
				Assert.assertTrue(heirs[0].isKind(TLAplusParserConstants.WF) || heirs[0].isKind(TLAplusParserConstants.SF));
				// heirs[1] is of indeterminate subscript expression type
				fairness.addChild(translate(heirs[1]));
				Assert.assertEquals(TLAplusParserConstants.LBR, heirs[2].getKind());
				// heirs[3] is of indeterminate expression type
				fairness.addChild(translate(heirs[3]));
				Assert.assertEquals(TLAplusParserConstants.RBR, heirs[4].getKind());
				return fairness;
			} case SyntaxTreeConstants.N_LetIn: { // LET f == x IN expr
				AstNode letIn = Kind.LET_IN.asNode();
				Assert.assertEquals(4, heirs.length);
				Assert.assertEquals(TLAplusParserConstants.LET, heirs[0].getKind());
				Assert.assertEquals(SyntaxTreeConstants.N_LetDefinitions, heirs[1].getKind());
				letIn.addChildren(repeat(heirs[1]));
				Assert.assertEquals(TLAplusParserConstants.LETIN, heirs[2].getKind());
				// heirs[3] is of indeterminate expression type
				letIn.addField("expression", translate(heirs[3]));
				return letIn;
			} case SyntaxTreeConstants.N_ParenExpr: {
				AstNode paren = Kind.PARENTHESES.asNode();
				Assert.assertEquals(3, heirs.length);
				Assert.assertEquals(TLAplusParserConstants.LBR, heirs[0].getKind());
				// heirs[1] is of indeterminate expression type
				paren.addChild(translate(heirs[1]));
				Assert.assertEquals(TLAplusParserConstants.RBR, heirs[2].getKind());
				return paren;
			} case SyntaxTreeConstants.N_OpApplication: { // f(a, b, c) or nonfix op
				AstNode nameOrSymbol = translate(parser.consume("Expected general ID", SyntaxTreeConstants.N_GeneralId));
				AstNode op = null;
				switch (nameOrSymbol.kind) {
					case IDENTIFIER_REF: {
						op = Kind.BOUND_OP.asNode();
						op.addField("name", nameOrSymbol);
						break;
					} case PREFIX_OP_SYMBOL: case INFIX_OP_SYMBOL: case POSTFIX_OP_SYMBOL: {
						op = Kind.BOUND_NONFIX_OP.asNode();
						op.addField("symbol", nameOrSymbol);
						break;
					} default: {
						Assert.fail(String.format("Unhandled op case %S", nameOrSymbol.kind));
					}
				}
				flatTranslate(op, parser.consume("Expected op args", SyntaxTreeConstants.N_OpArgs));
				return op;
			} case SyntaxTreeConstants.N_FcnAppl: {
				AstNode functionEvaluation = Kind.FUNCTION_EVALUATION.asNode();
				Assert.assertTrue(heirs.length >= 4);
				// heirs[0] is of indeterminate expression type
				functionEvaluation.addChild(translate(heirs[0]));
				Assert.assertEquals(TLAplusParserConstants.LSB, heirs[1].getKind());
				functionEvaluation.addChildren(commaSeparated(Arrays.copyOfRange(heirs, 2, heirs.length-1)));
				Assert.assertEquals(TLAplusParserConstants.RSB, heirs[heirs.length-1].getKind());
				return functionEvaluation;
			} case SyntaxTreeConstants.N_PrefixExpr: { // ex. SUBSET P
				AstNode boundPrefixOp = Kind.BOUND_PREFIX_OP.asNode();
				// Hilariously, the negative "-" prefix operator here appears as an infix operator
				if (parser.match(SyntaxTreeConstants.N_GenInfixOp)) {
					AstNode symbol = translate(parser.previous());
					// We have to rewrite the minus symbol to be a negative symbol
					if (Kind.PREFIXED_OP == symbol.kind) {
						symbol = Kind.PREFIXED_OP.asNode()
								.addField("prefix", symbol.fields.get("prefix"))
								.addField("op", Kind.NEGATIVE.asNode());
					} else if (Kind.MINUS == symbol.kind) {
						symbol = Kind.NEGATIVE.asNode();
					} else {
						Assert.fail(symbol.kind.name);
					}
					boundPrefixOp.addField("symbol", symbol);
				} else {
					boundPrefixOp.addField("symbol", translate(parser.consume("prefix op", SyntaxTreeConstants.N_GenPrefixOp)));
				}
				boundPrefixOp.addField("rhs", parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
				return boundPrefixOp;
			} case SyntaxTreeConstants.N_InfixExpr: { // ex. a + b
				AstNode boundInfixOp = Kind.BOUND_INFIX_OP.asNode();
				Assert.assertEquals(3, heirs.length);
				// heirs[0] is of indeterminate expression type
				boundInfixOp.addField("lhs", translate(heirs[0]));
				Assert.assertEquals(SyntaxTreeConstants.N_GenInfixOp, heirs[1].getKind());
				boundInfixOp.addField("symbol", translate(heirs[1]));
				// heirs[2] is of indeterminate expression type
				boundInfixOp.addField("rhs", translate(heirs[2]));
				return boundInfixOp;
			} case SyntaxTreeConstants.N_GenPrefixOp: { // ex. foo!bar!baz!SUBSET
				Assert.assertEquals(2, heirs.length);
				// TODO: handle prefix
				Assert.assertEquals(SyntaxTreeConstants.N_IdPrefix, heirs[0].getKind());
				Assert.assertEquals(SyntaxTreeConstants.N_PrefixOp, heirs[1].getKind());
				return translate(heirs[1]);
			} case SyntaxTreeConstants.N_GenInfixOp: { // ex. foo!bar!baz!+
				Assert.assertEquals(2, heirs.length);
				// TODO: handle prefix
				Assert.assertEquals(SyntaxTreeConstants.N_IdPrefix, heirs[0].getKind());
				Assert.assertEquals(SyntaxTreeConstants.N_InfixOp, heirs[1].getKind());
				return translate(heirs[1]);
			} case SyntaxTreeConstants.N_PrefixOp: { // ex. SUBSET
				Assert.assertEquals(0, heirs.length);
				return prefixOpFromString(node.image.toString());
			} case SyntaxTreeConstants.N_InfixOp: { // ex. +, -, /, /\
				Assert.assertEquals(0, heirs.length);
				return infixOpFromString(node.image.toString());
			} case SyntaxTreeConstants.N_Assumption: {
				AstNode assumption = Kind.ASSUMPTION.asNode();
				Assert.assertEquals(2, heirs.length);
				Assert.assertEquals(TLAplusParserConstants.ASSUME, heirs[0].getKind());
				// heirs[1] is of indeterminate expression type
				assumption.addChild(translate(heirs[1]));
				return assumption;
			} case SyntaxTreeConstants.N_Theorem: { // THEOREM name == ...
				/**
				 * Cases:
				 *  1. Unnamed theorem without proof
				 *  2. Named theorem without proof
				 *  3. Unnamed theorem with proof
				 *  4. Named theorem with proof
				 */
				AstNode theorem = Kind.THEOREM.asNode();
				Assert.assertTrue(heirs.length >= 2);
				Assert.assertTrue(
					heirs[0].isKind(TLAplusParserConstants.THEOREM)
					|| heirs[0].isKind(TLAplusParserConstants.PROPOSITION)
				);
				boolean isNamed =
					heirs[1].isKind(TLAplusParserConstants.IDENTIFIER)
					&& heirs.length >= 3
					&& heirs[2].isKind(TLAplusParserConstants.DEF);
				boolean hasProof =
					(isNamed && heirs.length == 5)
					|| (!isNamed && heirs.length == 3);
				if (isNamed) {
					Assert.assertEquals(TLAplusParserConstants.IDENTIFIER, heirs[1].getKind());
					theorem.addField("name", Kind.IDENTIFIER.asNode());
					Assert.assertEquals(TLAplusParserConstants.DEF, heirs[2].getKind());
					theorem.addChild(Kind.DEF_EQ.asNode());
					// heirs[3] is of expression or assume/prove type
					theorem.addChild(translate(heirs[3]));
					if (hasProof) {
						// heirs[4] is of indeterminate proof type
						theorem.addChild(translate(heirs[4]));
					}
				} else {
					// heirs[1] is of expression or assume/prove type
					theorem.addChild(translate(heirs[1]));
					if (hasProof) {
						// heirs[2] is of indeterminate proof type
						theorem.addChild(translate(heirs[2]));
					}
				}
				return theorem;
			} case SyntaxTreeConstants.N_TerminalProof: { // PROOF BY DEF >
				AstNode proof = Kind.TERMINAL_PROOF.asNode();
				Assert.assertTrue(heirs.length >= 1);
				int offset = 0;
				if (heirs[offset].isKind(TLAplusParserConstants.PROOF)) {
					offset++;
				}
				if (heirs[offset].isKind(TLAplusParserConstants.BY)) {
					offset++;
					proof.addChild(parseUseBody(heirs, offset));
				} else {
					Assert.assertTrue(
						heirs[offset].isKind(TLAplusParserConstants.OBVIOUS)
						|| heirs[offset].isKind(TLAplusParserConstants.OMITTED));
				}
				return proof;
			} case SyntaxTreeConstants.N_Proof: {
				AstNode proof = Kind.NON_TERMINAL_PROOF.asNode();
				Assert.assertTrue(heirs.length > 0);
				int offset = 0;
				if (heirs[offset].isKind(TLAplusParserConstants.PROOF)) {
					offset++;
				}
				for (; offset < heirs.length; offset++) {
					proof.addChild(translate(heirs[offset]));
				}
				return proof;
			} case SyntaxTreeConstants.N_ProofStep: {
				AstNode proofStepId = Kind.PROOF_STEP_ID.asNode();
				parser.consume("Expected proof step ID", TLAplusParserConstants.ProofStepLexeme, TLAplusParserConstants.ProofStepDotLexeme, TLAplusParserConstants.BareLevelLexeme);
				proofStepId.addField("level", Kind.LEVEL.asNode());
				proofStepId.addField("name", Kind.NAME.asNode());
				AstNode proofStep = null;
				if (parser.match(SyntaxTreeConstants.N_QEDStep)) {
					proofStep = Kind.QED_STEP.asNode();
					proofStep.addChild(proofStepId);
					if (!parser.isAtEnd()) {
						proofStep.addChild(parser.translate("Expected proof"));
					}
				} else {
					proofStep = Kind.PROOF_STEP.asNode();
					proofStep.addChild(proofStepId);
					AstNode proofStepStatement = parser.translate("Expected proof step");
					proofStep.addChild(proofStepStatement);
					if (!parser.isAtEnd()) {
						proofStepStatement.addChild(parser.translate("Expected proof"));
					}
				}
				Assert.assertTrue(parser.isAtEnd());
				return proofStep;
			} case SyntaxTreeConstants.N_DefStep: { // DEFINE op == ...
				AstNode proof = Kind.DEFINITION_PROOF_STEP.asNode();
				parser.match(TLAplusParserConstants.DEFINE);
				do {
					proof.addChild(parser.translate("Expected expression"));
				} while (!parser.isAtEnd());
				Assert.assertTrue(parser.isAtEnd());
				return proof;
			} case SyntaxTreeConstants.N_HaveStep: { // HAVE x > y
				AstNode proof = Kind.HAVE_PROOF_STEP.asNode();
				parser.consume("Expected HAVE", TLAplusParserConstants.HAVE);
				proof.addChild(parser.translate("Expected expression"));
				Assert.assertTrue(parser.isAtEnd());
				return proof;
			} case SyntaxTreeConstants.N_WitnessStep: { // WITNESS x > y, y > z, ...
				AstNode proof = Kind.WITNESS_PROOF_STEP.asNode();
				parser.consume("Expected WITNESS", TLAplusParserConstants.WITNESS);
				proof.addChildren(parseCommaSeparatedNodes(parser));
				Assert.assertTrue(parser.isAtEnd());
				return proof;
			} case SyntaxTreeConstants.N_TakeStep: {
				AstNode proof = Kind.TAKE_PROOF_STEP.asNode();
				parser.consume("Expected TAKE", TLAplusParserConstants.TAKE);
				proof.addChildren(parseBoundListOrIdentifierList(parser));
				Assert.assertTrue(parser.isAtEnd());
				return proof;
			} case SyntaxTreeConstants.N_AssertStep: {
				AstNode proof = Kind.SUFFICES_PROOF_STEP.asNode();
				parser.match(TLAplusParserConstants.SUFFICES);
				proof.addChild(parser.translate("Expected expression"));
				Assert.assertTrue(parser.isAtEnd());
				return proof;
			} case SyntaxTreeConstants.N_CaseStep: {
				AstNode proof = Kind.CASE_PROOF_STEP.asNode();
				parser.consume("Expected CASE", TLAplusParserConstants.CASE);
				proof.addChild(parser.translate("Expected expression"));
				Assert.assertTrue(parser.isAtEnd());
				return proof;
			} case SyntaxTreeConstants.N_PickStep: {
				AstNode proof = Kind.PICK_PROOF_STEP.asNode();
				parser.consume("Expected PICK", TLAplusParserConstants.PICK);
				proof.addChildren(parseBoundListOrIdentifierList(parser));
				parser.consume("Expected :", TLAplusParserConstants.COLON);
				proof.addChild(parser.translate("Expected expression"));
				Assert.assertTrue(parser.isAtEnd());
				return proof;
			} case SyntaxTreeConstants.N_UseOrHide: {
				AstNode proof = Kind.USE_OR_HIDE.asNode();
				parser.consume("Expected USE or HIDE", TLAplusParserConstants.USE, TLAplusParserConstants.HIDE);
				AstNode useBody = Kind.USE_BODY.asNode();
				proof.addChild(useBody);
				if (!parser.check(TLAplusParserConstants.DEF)) {
					AstNode useBodyExpr = Kind.USE_BODY_EXPR.asNode();
					useBody.addChild(useBodyExpr);
					do {
						if (parser.match(TLAplusParserConstants.MODULE)) {
							AstNode moduleRef = Kind.MODULE_REF.asNode();
							useBodyExpr.addChild(moduleRef);
							parser.consume("Expected identifier", TLAplusParserConstants.IDENTIFIER);
							moduleRef.addChild(Kind.IDENTIFIER_REF.asNode());
						} else {
							useBodyExpr.addChild(parser.translate("Expected expression"));
						}
					} while (parser.match(TLAplusParserConstants.COMMA));
				}
				if (parser.match(TLAplusParserConstants.DEF)) {
					AstNode useBodyDef = Kind.USE_BODY_DEF.asNode();
					useBody.addChild(useBodyDef);
					do {
						if (parser.match(TLAplusParserConstants.MODULE)) {
							AstNode moduleRef = Kind.MODULE_REF.asNode();
							useBodyDef.addChild(moduleRef);
							parser.consume("Expected identifier", TLAplusParserConstants.IDENTIFIER);
							moduleRef.addChild(Kind.IDENTIFIER_REF.asNode());
						} else {
							useBodyDef.addChild(parser.translate("Expected operator or expression"));
						}
					} while (parser.match(TLAplusParserConstants.COMMA));
				}
				Assert.assertTrue(parser.isAtEnd());
				return proof;
			} default: {
				throw new ParseException(String.format("Unhandled conversion from kind %d image %s", node.getKind(), node.getImage()), 0);
			}
		}
	}
	
	/**
	 * Converts the SANY parse tree to a normalized form comparable to the
	 * AST DSL.
	 * 
	 * @param sany The SANY parser, having completed parsing a TLA+ file.
	 * @return The root node of the translated AST.
	 * @throws ParseException If unable to convert the SANY parse tree.
	 */
	public static AstNode toAst(TLAplusParser sany) throws ParseException {
		AstNode sourceFile = Kind.SOURCE_FILE.asNode();
		sourceFile.addChild(translate(sany.ParseTree));
		return sourceFile;
	}

	public static void printSanyParseTree(TLAplusParser sanyTree) {
		PrintWriter out = new PrintWriter(System.out);
		SyntaxTreePrinter.print(sanyTree, out);
		out.flush();
	}
}
