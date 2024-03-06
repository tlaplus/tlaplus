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
import java.util.stream.Collectors;

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
		public SyntaxTreeNode consume(int... kinds) throws ParseException {
			for (int kind : kinds) {
				if (check(kind)) return advance();
			}
			String expected = Arrays.stream(kinds).mapToObj(String::valueOf).collect(Collectors.joining(", "));
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
		
		public AstNode translate(int... expected) throws ParseException {
			return SanyTranslator.translate(this.consume(expected));
		}
		
		public SanyReparser recurseOn(int... expected) throws ParseException {
			SyntaxTreeNode node = this.consume(expected);
			return new SanyReparser(node.getHeirs());
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
			parser.consume(TLAplusParserConstants.IDENTIFIER);
			ids.add(Kind.IDENTIFIER.asNode());
		} while (parser.match(TLAplusParserConstants.COMMA));
		return ids;
	}
	
	private static List<AstNode> parseCommaSeparatedNodes(SanyReparser parser, String expected) throws ParseException {
		List <AstNode> nodes = new ArrayList<AstNode>();
		do {
			nodes.add(parser.translate(expected));
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
		parser.consume(TLAplusParserConstants.LAB);
		tuple.addChild(Kind.LANGLE_BRACKET.asNode());
		tuple.addChildren(parseCommaSeparatedIds(parser));
		parser.consume(TLAplusParserConstants.RAB);
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
		parser.consume(SyntaxTreeConstants.T_IN);
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
	
	private static void parseUseBodyDefs(SanyReparser parser, AstNode parent) throws ParseException {
		do {
			if (parser.match(TLAplusParserConstants.MODULE)) {
				AstNode moduleRef = Kind.MODULE_REF.asNode();
				moduleRef.addChild(parser.translate(TLAplusParserConstants.IDENTIFIER));
				parent.addChild(moduleRef);
			} else {
				parent.addChild(parser.translate("operator or expression"));
			}
		} while (parser.match(TLAplusParserConstants.COMMA));
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
	private static AstNode parseUseBody(SanyReparser parser) throws ParseException {
		AstNode useBody = Kind.USE_BODY.asNode();
		if (!parser.check(TLAplusParserConstants.DF)) {
			AstNode useBodyExpr = Kind.USE_BODY_EXPR.asNode();
			parseUseBodyDefs(parser, useBodyExpr);
			useBody.addChild(useBodyExpr);
		}
		if (parser.match(TLAplusParserConstants.DF)) {
			AstNode useBodyDef = Kind.USE_BODY_DEF.asNode();
			parseUseBodyDefs(parser, useBodyDef);
			useBody.addChild(useBodyDef);
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
			case "-.": return Kind.NEGATIVE.asNode();
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
			case ":=": return Kind.ASSIGN.asNode();
			case "::=": return Kind.BNF_RULE.asNode();
			case ":>": return Kind.MAP_TO.asNode();
			default: throw new ParseException(String.format("Operator translation not defined: %s", op), 0);
		}
	}

	private static AstNode postfixOpFromString(String op) throws ParseException {
		switch (op) {
			case "^+": return Kind.SUP_PLUS.asNode();
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
			case SyntaxTreeConstants.N_IdentLHS: { // f ==, f(a, b) ==, f(g(_, _)), etc.
				parser.consume(TLAplusParserConstants.IDENTIFIER);
				parent.addField("name", Kind.IDENTIFIER.asNode());
				if (parser.match(TLAplusParserConstants.LBR)) {
					do {
						parent.addChild(
							parser.translate(
								SyntaxTreeConstants.N_IdentDecl,
								SyntaxTreeConstants.N_PrefixDecl,
								SyntaxTreeConstants.N_InfixDecl,
								SyntaxTreeConstants.N_PostfixDecl));
					} while (parser.match(TLAplusParserConstants.COMMA));
					parser.consume(TLAplusParserConstants.RBR);
				}
				break;
			} case SyntaxTreeConstants.N_OpArgs: { // (p1, p2, ..., pn)
				parser.consume(TLAplusParserConstants.LBR);
				parent.addChildren(parseCommaSeparatedNodes(parser, "expression"));
				parser.consume(TLAplusParserConstants.RBR);
				break;
			} case SyntaxTreeConstants.N_ProofStep: { // <1>c QED
				AstNode qedStep = Kind.QED_STEP.asNode();
				qedStep.addChild(parser.translate(
						TLAplusParserConstants.ProofStepLexeme,
						TLAplusParserConstants.ProofStepDotLexeme,
						TLAplusParserConstants.BareLevelLexeme));
				parser.consume(SyntaxTreeConstants.N_QEDStep);
				if (!parser.isAtEnd()) {
					qedStep.addChild(parser.translate("proof"));
				}
				parent.addChild(qedStep);
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
	 * intimidated! It is easier than it looks.
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
				// TODO: test operator substitution
				substitution.addChild(parser.translate(TLAplusParserConstants.IDENTIFIER));
				substitution.addChild(parser.translate(TLAplusParserConstants.SUBSTITUTE));
				substitution.addChild(parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
				return substitution;
			} case TLAplusParserConstants.SUBSTITUTE: {
				Assert.assertTrue(parser.isAtEnd());
				return Kind.GETS.asNode();
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
			} case SyntaxTreeConstants.N_IdentDecl: { // f, f(_, _), etc.
				parser.consume(TLAplusParserConstants.IDENTIFIER);
				if (parser.isAtEnd()) {
					return Kind.IDENTIFIER.asNode();
				}
				AstNode op = Kind.OPERATOR_DECLARATION.asNode();
				op.addField("name", Kind.IDENTIFIER.asNode());
				parser.consume(TLAplusParserConstants.LBR);
				do {
					op.addChild(parser.translate(TLAplusParserConstants.US));
				} while (parser.match(TLAplusParserConstants.COMMA));
				parser.consume(TLAplusParserConstants.RBR);
				// TODO: test higher-order operator parameters
				Assert.assertTrue(parser.isAtEnd());
				return op;
			} case SyntaxTreeConstants.N_PrefixDecl: { // -. _
				AstNode op = Kind.OPERATOR_DECLARATION.asNode();
				AstNode symbol = Kind.PREFIX_OP_SYMBOL.asNode();
				symbol.addField("symbol", parser.translate(SyntaxTreeConstants.N_NonExpPrefixOp));
				op.addChild(symbol);
				op.addChild(parser.translate(TLAplusParserConstants.US));
				Assert.assertTrue(parser.isAtEnd());
				return op;
			} case SyntaxTreeConstants.N_InfixDecl: { // _ + _, _ - _
				AstNode op = Kind.OPERATOR_DECLARATION.asNode();
				op.addChild(parser.translate(TLAplusParserConstants.US));
				AstNode symbol = Kind.INFIX_OP_SYMBOL.asNode();
				symbol.addField("symbol", parser.translate(SyntaxTreeConstants.N_InfixOp));
				op.addChild(symbol);
				op.addChild(parser.translate(TLAplusParserConstants.US));
				Assert.assertTrue(parser.isAtEnd());
				return op;
			} case SyntaxTreeConstants.N_PostfixDecl: { // _ ', _ ^+
				AstNode op = Kind.OPERATOR_DECLARATION.asNode();
				op.addChild(parser.translate(TLAplusParserConstants.US));
				AstNode symbol = Kind.POSTFIX_OP_SYMBOL.asNode();
				symbol.addField("symbol", parser.translate(SyntaxTreeConstants.N_PostfixOp));
				op.addChild(symbol);
				Assert.assertTrue(parser.isAtEnd());
				return op;
			} case SyntaxTreeConstants.N_Recursive: { // RECURSIVE F(_, _), G(_)
				AstNode recursiveDeclaration = Kind.RECURSIVE_DECLARATION.asNode();
				parser.consume(TLAplusParserConstants.RECURSIVE);
				recursiveDeclaration.addChildren(parseCommaSeparatedNodes(parser, "operator declaration"));
				Assert.assertTrue(parser.isAtEnd());
				return recursiveDeclaration;
			} case TLAplusParserConstants.US: {
				Assert.assertTrue(parser.isAtEnd());
				return Kind.PLACEHOLDER.asNode();
			} case TLAplusParserConstants.DEF: { // ==
				Assert.assertTrue(parser.isAtEnd());
				return Kind.DEF_EQ.asNode();
			} case SyntaxTreeConstants.N_ConjList: { // Multi-line aligned conjunction list
				AstNode conjList = Kind.CONJ_LIST.asNode();
				do {
					conjList.addChild(parser.translate(SyntaxTreeConstants.N_ConjItem));
				} while (!parser.isAtEnd());
				Assert.assertTrue(parser.isAtEnd());
				return conjList;
			} case SyntaxTreeConstants.N_ConjItem: { // /\ expr
				AstNode conjItem = Kind.CONJ_ITEM.asNode();
				conjItem.addChild(parser.translate(TLAplusParserConstants.AND));
				conjItem.addChild(parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
				return conjItem;
			} case TLAplusParserConstants.AND: {
				Assert.assertTrue(parser.isAtEnd());
				return Kind.BULLET_CONJ.asNode();
			} case SyntaxTreeConstants.N_DisjList: { // Multi-line aligned disjunction list
				AstNode disjList = Kind.DISJ_LIST.asNode();
				do {
					disjList.addChild(parser.translate(SyntaxTreeConstants.N_DisjItem));
				} while (!parser.isAtEnd());
				Assert.assertTrue(parser.isAtEnd());
				return disjList;
			} case SyntaxTreeConstants.N_DisjItem: { // \/ expr
				AstNode disjItem = Kind.DISJ_ITEM.asNode();
				disjItem.addChild(parser.translate(TLAplusParserConstants.OR));
				disjItem.addChild(parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
				return disjItem;
			} case TLAplusParserConstants.OR: {
				Assert.assertTrue(parser.isAtEnd());
				return Kind.BULLET_DISJ.asNode();
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
						op = Kind.PREFIX_OP_SYMBOL.asNode().addChild(translate(heirs[1]));
						break;
					} default: {
						Assert.fail(heirs[1].getImage());
					}
				}
				
				return prefixedOp == null ? op : prefixedOp.addField("op", op);
			} case SyntaxTreeConstants.N_IdPrefix: {
				AstNode subexpr = Kind.SUBEXPR_PREFIX.asNode();
				do {
					subexpr.addChild(parser.translate(SyntaxTreeConstants.N_IdPrefixElement));
				} while (!parser.isAtEnd());
				Assert.assertTrue(parser.isAtEnd());
				return subexpr;
			} case SyntaxTreeConstants.N_IdPrefixElement: {
				AstNode subexprComponent = Kind.SUBEXPR_COMPONENT.asNode();
				parser.consume(TLAplusParserConstants.IDENTIFIER);
				subexprComponent.addChild(Kind.IDENTIFIER_REF.asNode());
				parser.consume(TLAplusParserConstants.BANG);
				Assert.assertTrue(parser.isAtEnd());
				return subexprComponent;
			} case TLAplusParserConstants.IDENTIFIER: { // ex. x
				Assert.assertTrue(parser.isAtEnd());
				return id(node);
			} case SyntaxTreeConstants.N_Number: { // 1, 3, 100, etc.
				String image = parser.consume(TLAplusParserConstants.NUMBER_LITERAL).image.toString();
				Assert.assertTrue(parser.isAtEnd());
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
				parser.consume(TLAplusParserConstants.NUMBER_LITERAL);
				parser.consume(TLAplusParserConstants.DOT);
				parser.consume(TLAplusParserConstants.NUMBER_LITERAL);
				Assert.assertTrue(parser.isAtEnd());
				return Kind.REAL_NUMBER.asNode();
			} case SyntaxTreeConstants.N_String: { // ex. "foobar"
				AstNode string = Kind.STRING.asNode();
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
				Assert.assertTrue(parser.isAtEnd());
				return string;
			} case SyntaxTreeConstants.N_Tuple: { // ex. <<1, 2, 3>>
				AstNode tuple = Kind.TUPLE_LITERAL.asNode();
				tuple.addChild(parser.translate(TLAplusParserConstants.LAB));
				if (!parser.check(TLAplusParserConstants.RAB)) {
					tuple.addChildren(parseCommaSeparatedNodes(parser, "expression"));
				}
				tuple.addChild(parser.translate(TLAplusParserConstants.RAB));
				Assert.assertTrue(parser.isAtEnd());
				return tuple;
			} case TLAplusParserConstants.LAB: { // <<
				Assert.assertTrue(parser.isAtEnd());
				return Kind.LANGLE_BRACKET.asNode();
			} case TLAplusParserConstants.RAB: { // >>
				Assert.assertTrue(parser.isAtEnd());
				return Kind.RANGLE_BRACKET.asNode();
			} case TLAplusParserConstants.ARAB: { // >>_
				Assert.assertTrue(parser.isAtEnd());
				return Kind.RANGLE_BRACKET_SUB.asNode();
			} case SyntaxTreeConstants.N_SetEnumerate: { // {1, 3, 5}
				AstNode setLiteral = Kind.FINITE_SET_LITERAL.asNode();
				parser.consume(TLAplusParserConstants.LBC);
				if (!parser.check(TLAplusParserConstants.RBC)) {
					setLiteral.addChildren(parseCommaSeparatedNodes(parser, "expression"));
				}
				parser.consume(TLAplusParserConstants.RBC);
				Assert.assertTrue(parser.isAtEnd());
				return setLiteral;
			} case SyntaxTreeConstants.N_SubsetOf: { // {x \in S : P(x)}
				AstNode setFilter = Kind.SET_FILTER.asNode();
				parser.consume(TLAplusParserConstants.LBC);
				setFilter.addField("generator", parseQuantifierBound(parser));
				parser.consume(TLAplusParserConstants.COLON);
				setFilter.addField("filter", parser.translate("Expected expression"));
				parser.consume(TLAplusParserConstants.RBC);
				Assert.assertTrue(parser.isAtEnd());
				return setFilter;
			} case SyntaxTreeConstants.N_SetOfFcns: { // [S -> P]
				AstNode setOfFunctions = Kind.SET_OF_FUNCTIONS.asNode();
				parser.consume(TLAplusParserConstants.LSB);
				setOfFunctions.addChild(parser.translate("expression"));
				parser.consume(TLAplusParserConstants.ARROW);
				setOfFunctions.addChild(Kind.MAPS_TO.asNode());
				setOfFunctions.addChild(parser.translate("expression"));
				parser.consume(TLAplusParserConstants.RSB);
				Assert.assertTrue(parser.isAtEnd());
				return setOfFunctions;
			} case SyntaxTreeConstants.N_IfThenElse: { // IF x THEN y ELSE z
				AstNode ite = Kind.IF_THEN_ELSE.asNode();
				parser.consume(TLAplusParserConstants.IF);
				ite.addField("if", parser.translate("expression"));
				parser.consume(TLAplusParserConstants.THEN);
				ite.addField("then", parser.translate("expression"));
				parser.consume(TLAplusParserConstants.ELSE);
				ite.addField("else", parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
				return ite;
			} case SyntaxTreeConstants.N_Case: { // CASE A -> B [] C -> D [] OTHER -> E
				AstNode cases = Kind.CASE.asNode();
				parser.consume(TLAplusParserConstants.CASE);
				cases.addChild(parser.translate(SyntaxTreeConstants.N_CaseArm));
				while (parser.match(TLAplusParserConstants.CASESEP)) {
					cases.addChild(Kind.CASE_BOX.asNode());
					cases.addChild(parser.translate(SyntaxTreeConstants.N_CaseArm, SyntaxTreeConstants.N_OtherArm));
				}
				Assert.assertTrue(parser.isAtEnd());
				return cases;
			} case SyntaxTreeConstants.N_CaseArm: { // P -> Q
				AstNode caseArm = Kind.CASE_ARM.asNode();
				caseArm.addChild(parser.translate("expression"));
				parser.consume(TLAplusParserConstants.ARROW);
				caseArm.addChild(Kind.CASE_ARROW.asNode());
				caseArm.addChild(parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
				return caseArm;
			} case SyntaxTreeConstants.N_OtherArm: { // OTHER -> expr
				AstNode otherArm = Kind.OTHER_ARM.asNode();
				parser.consume(TLAplusParserConstants.OTHER);
				parser.consume(TLAplusParserConstants.ARROW);
				otherArm.addChild(Kind.CASE_ARROW.asNode());
				otherArm.addChild(parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
				return otherArm;
			} case SyntaxTreeConstants.N_ActionExpr: { // [expr]_subexpr or <<expr>>_subexpr
				AstNode actionExpr = null;
				if (parser.match(TLAplusParserConstants.LSB)) {
					actionExpr = Kind.STEP_EXPR_OR_STUTTER.asNode();
					actionExpr.addChild(parser.translate("expression"));
					parser.consume(TLAplusParserConstants.ARSB);
					actionExpr.addChild(parser.translate("subscript expression"));
				} else {
					actionExpr = Kind.STEP_EXPR_NO_STUTTER.asNode();
					actionExpr.addChild(parser.translate(TLAplusParserConstants.LAB));
					actionExpr.addChild(parser.translate("expression"));
					actionExpr.addChild(parser.translate(TLAplusParserConstants.ARAB));
					actionExpr.addChild(parser.translate("subscript expression"));
				}
				Assert.assertTrue(parser.isAtEnd());
				return actionExpr;
			} case SyntaxTreeConstants.N_FairnessExpr: { // WF_x(action)
				AstNode fairness = Kind.FAIRNESS.asNode();
				parser.consume(TLAplusParserConstants.WF, TLAplusParserConstants.SF);
				fairness.addChild(parser.translate("subscript expression"));
				parser.consume(TLAplusParserConstants.LBR);
				fairness.addChild(parser.translate("expression"));
				parser.consume(TLAplusParserConstants.RBR);
				Assert.assertTrue(parser.isAtEnd());
				return fairness;
			} case SyntaxTreeConstants.N_LetIn: { // LET f == x IN expr
				AstNode letIn = Kind.LET_IN.asNode();
				parser.consume(TLAplusParserConstants.LET);
				letIn.addChildren(repeat(parser.consume(SyntaxTreeConstants.N_LetDefinitions)));
				parser.consume(TLAplusParserConstants.LETIN);
				letIn.addField("expression", parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
				return letIn;
			} case SyntaxTreeConstants.N_ParenExpr: { // ( expr )
				AstNode paren = Kind.PARENTHESES.asNode();
				parser.consume(TLAplusParserConstants.LBR);
				paren.addChild(parser.translate("expression"));
				parser.consume(TLAplusParserConstants.RBR);
				Assert.assertTrue(parser.isAtEnd());
				return paren;
			} case SyntaxTreeConstants.N_OpApplication: { // f(a, b, c) or nonfix op
				AstNode nameOrSymbol = parser.translate(SyntaxTreeConstants.N_GeneralId);
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
				flatTranslate(op, parser.consume(SyntaxTreeConstants.N_OpArgs));
				Assert.assertTrue(parser.isAtEnd());
				return op;
			} case SyntaxTreeConstants.N_FcnAppl: { // f[x,y,z]
				AstNode functionEvaluation = Kind.FUNCTION_EVALUATION.asNode();
				functionEvaluation.addChild(parser.translate("expression"));
				parser.consume(TLAplusParserConstants.LSB);
				functionEvaluation.addChildren(parseCommaSeparatedNodes(parser, "expression"));
				parser.consume(TLAplusParserConstants.RSB);
				Assert.assertTrue(parser.isAtEnd());
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
					boundPrefixOp.addField("symbol", parser.translate(SyntaxTreeConstants.N_GenPrefixOp));
				}
				boundPrefixOp.addField("rhs", parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
				return boundPrefixOp;
			} case SyntaxTreeConstants.N_InfixExpr: { // ex. a + b
				AstNode boundInfixOp = Kind.BOUND_INFIX_OP.asNode();
				Assert.assertEquals(3, heirs.length);
				boundInfixOp.addField("lhs", parser.translate("expression"));
				boundInfixOp.addField("symbol", parser.translate(SyntaxTreeConstants.N_GenInfixOp));
				boundInfixOp.addField("rhs", parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
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
				Assert.assertTrue(parser.isAtEnd());
				return prefixOpFromString(node.image.toString());
			} case SyntaxTreeConstants.N_NonExpPrefixOp: { // ex. -.
				Assert.assertTrue(parser.isAtEnd());
				return prefixOpFromString(node.image.toString());
			} case SyntaxTreeConstants.N_InfixOp: { // ex. +, -, /, /\
				Assert.assertTrue(parser.isAtEnd());
				return infixOpFromString(node.image.toString());
			} case SyntaxTreeConstants.N_PostfixOp: { // ex. ^+, '
				Assert.assertTrue(parser.isAtEnd());
				return postfixOpFromString(node.image.toString());
			} case SyntaxTreeConstants.N_Assumption: {
				AstNode assumption = Kind.ASSUMPTION.asNode();
				parser.consume(TLAplusParserConstants.ASSUME);
				if (parser.match(TLAplusParserConstants.IDENTIFIER)) {
					assumption.addField("name", Kind.IDENTIFIER.asNode());
					parser.consume(TLAplusParserConstants.DEF);
					assumption.addChild(Kind.DEF_EQ.asNode());
				}
				assumption.addChild(parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
				return assumption;
			} case SyntaxTreeConstants.N_Theorem: { // THEOREM name == ...
				AstNode theorem = Kind.THEOREM.asNode();
				parser.consume(TLAplusParserConstants.THEOREM, TLAplusParserConstants.PROPOSITION);
				if (parser.match(TLAplusParserConstants.IDENTIFIER)) {
					theorem.addField("name", Kind.IDENTIFIER.asNode());
					parser.consume(TLAplusParserConstants.DEF);
					theorem.addChild(Kind.DEF_EQ.asNode());
				}
				theorem.addChild(parser.translate("expression or assume/prove"));
				if (!parser.isAtEnd()) {
					theorem.addChild(parser.translate("proof"));
				}
				Assert.assertTrue(parser.isAtEnd());
				return theorem;
			} case SyntaxTreeConstants.N_TerminalProof: { // PROOF BY DEF >
				AstNode proof = Kind.TERMINAL_PROOF.asNode();
				parser.match(TLAplusParserConstants.PROOF);
				if (parser.match(TLAplusParserConstants.OBVIOUS, TLAplusParserConstants.OMITTED)) {
					return proof;
				}
				parser.consume(TLAplusParserConstants.BY);
				parser.match(TLAplusParserConstants.ONLY);
				proof.addChild(parseUseBody(parser));
				Assert.assertTrue(parser.isAtEnd());
				return proof;
			} case SyntaxTreeConstants.N_Proof: { // A series of proof steps
				AstNode proof = Kind.NON_TERMINAL_PROOF.asNode();
				parser.match(TLAplusParserConstants.PROOF);
				while (parser.match(SyntaxTreeConstants.N_ProofStep)) {
					if (parser.isAtEnd()) {
						// This must be the QED step, which we pull up to this level
						flatTranslate(proof, parser.previous());
					} else {
						proof.addChild(translate(parser.previous()));
					}
				}
				Assert.assertTrue(parser.isAtEnd());
				return proof;
			} case SyntaxTreeConstants.N_ProofStep: { // <1>a. HAVE x > y
				AstNode proofStep = Kind.PROOF_STEP.asNode();
				proofStep.addChild(parser.translate(
						TLAplusParserConstants.ProofStepLexeme,
						TLAplusParserConstants.ProofStepDotLexeme,
						TLAplusParserConstants.BareLevelLexeme));
				AstNode proofStepStatement = parser.translate("proof step statement");
				proofStep.addChild(proofStepStatement);
				if (!parser.isAtEnd()) {
					proofStepStatement.addChild(parser.translate("proof"));
				}
				Assert.assertTrue(parser.isAtEnd());
				return proofStep;
			}
			case TLAplusParserConstants.ProofStepLexeme:
			case TLAplusParserConstants.ProofStepDotLexeme:
			case TLAplusParserConstants.BareLevelLexeme: {
				AstNode proofStepId = Kind.PROOF_STEP_ID.asNode();
				proofStepId.addField("level", Kind.LEVEL.asNode());
				proofStepId.addField("name", Kind.NAME.asNode());
				return proofStepId;
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
				parser.consume(TLAplusParserConstants.HAVE);
				proof.addChild(parser.translate("Expected expression"));
				Assert.assertTrue(parser.isAtEnd());
				return proof;
			} case SyntaxTreeConstants.N_WitnessStep: { // WITNESS x > y, y > z, ...
				AstNode proof = Kind.WITNESS_PROOF_STEP.asNode();
				parser.consume(TLAplusParserConstants.WITNESS);
				proof.addChildren(parseCommaSeparatedNodes(parser, "definition or expression"));
				Assert.assertTrue(parser.isAtEnd());
				return proof;
			} case SyntaxTreeConstants.N_TakeStep: { // TAKE x, y \in Nat, z \in Real
				AstNode proof = Kind.TAKE_PROOF_STEP.asNode();
				parser.consume(TLAplusParserConstants.TAKE);
				proof.addChildren(parseBoundListOrIdentifierList(parser));
				Assert.assertTrue(parser.isAtEnd());
				return proof;
			} case SyntaxTreeConstants.N_AssertStep: { // SUFFICES x \in Real
				AstNode proof = Kind.SUFFICES_PROOF_STEP.asNode();
				parser.match(TLAplusParserConstants.SUFFICES);
				proof.addChild(parser.translate("Expected expression"));
				Assert.assertTrue(parser.isAtEnd());
				return proof;
			} case SyntaxTreeConstants.N_CaseStep: { // CASE y < 0
				AstNode proof = Kind.CASE_PROOF_STEP.asNode();
				parser.consume(TLAplusParserConstants.CASE);
				proof.addChild(parser.translate("Expected expression"));
				Assert.assertTrue(parser.isAtEnd());
				return proof;
			} case SyntaxTreeConstants.N_PickStep: { // PICK x \in Nat : x > 0
				AstNode proof = Kind.PICK_PROOF_STEP.asNode();
				parser.consume(TLAplusParserConstants.PICK);
				proof.addChildren(parseBoundListOrIdentifierList(parser));
				parser.consume(TLAplusParserConstants.COLON);
				proof.addChild(parser.translate("Expected expression"));
				Assert.assertTrue(parser.isAtEnd());
				return proof;
			} case SyntaxTreeConstants.N_UseOrHide: { // USE A, B DEFS MODULE M, +
				AstNode proof = Kind.USE_OR_HIDE.asNode();
				parser.consume(TLAplusParserConstants.USE, TLAplusParserConstants.HIDE);
				proof.addChild(parseUseBody(parser));
				Assert.assertTrue(parser.isAtEnd());
				return proof;
			} case SyntaxTreeConstants.N_Label: { // lbl(a, b) :: expr
				AstNode label = Kind.LABEL.asNode();
				label.addField("name", Kind.IDENTIFIER.asNode());
				SyntaxTreeNode labelName = parser.consume(SyntaxTreeConstants.N_GeneralId, SyntaxTreeConstants.N_OpApplication);
				if (labelName.isKind(SyntaxTreeConstants.N_OpApplication)) {
					SanyReparser nameParser = new SanyReparser(labelName.getHeirs());
					nameParser.consume(SyntaxTreeConstants.N_GeneralId);
					flatTranslate(label, nameParser.consume(SyntaxTreeConstants.N_OpArgs));
				}
				label.addChild(parser.translate(TLAplusParserConstants.COLONCOLON));
				label.addField("expression", parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
				return label;
			} case TLAplusParserConstants.COLONCOLON: {
				return Kind.LABEL_AS.asNode();
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

	/**
	 * Quick debug helper function to dump the SANY parse tree to a string.
	 * 
	 * @param sanyTree The SANY parse tree.
	 */
	public static void printSanyParseTree(TLAplusParser sanyTree) {
		PrintWriter out = new PrintWriter(System.out);
		SyntaxTreePrinter.print(sanyTree, out);
		out.flush();
	}
}
