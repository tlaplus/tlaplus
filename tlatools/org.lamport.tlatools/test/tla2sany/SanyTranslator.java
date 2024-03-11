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
		 * Gets the node previously looked at.
		 * 
		 * @return The kind of the node previously looked at.
		 */
		private SyntaxTreeNode previous() {
			return this.nodes[this.current - 1];
		}
		
		/**
		 * If not at the end of the list, advance then return the last node.
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
		 * Peek at the node currently being looked at without consuming it.
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
		 * @return The consumed node.
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
		 * @return The translated consumed node.
		 * @throws ParseException If no more nodes exist to be consumed.
		 */
		public AstNode translate(String expected) throws ParseException {
			if (this.isAtEnd()) {
				throw new ParseException(String.format("EOF; expected %s", expected), this.current);
			} else {
				return SanyTranslator.translate(this.advance());
			}
		}
		
		/**
		 * Translates then consumes the current node, if it's of given kind.
		 * 
		 * @param expected The expected node; provided for error messages.
		 * @return The translated consumed node.
		 * @throws ParseException If node kind is not what was given.
		 */
		public AstNode translate(int... expected) throws ParseException {
			return SanyTranslator.translate(this.consume(expected));
		}
		
		public void flatTranslate(AstNode parent, int... expected) throws ParseException {
			SanyTranslator.flatTranslate(parent, this.consume(expected));
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
	 * Parses an unstructured quantifier bound, presented as a flat token list.
	 * Ex. <<x, y, z>> \in Nat \X Nat \X Nat
	 * 
	 * @param parser The SANY reparser state.
	 * @return An AST node for the quantifier bound.
	 * @throws ParseException If input is not a valid quantifier bound.
	 */
	private static AstNode parseUnstructuredQuantifierBound(SanyReparser parser) throws ParseException {
		AstNode bound = Kind.QUANTIFIER_BOUND.asNode();
		if (parser.check(TLAplusParserConstants.LAB)) {
			bound.addChild(parseTupleOfIdentifiers(parser));
		} else if (parser.check(TLAplusParserConstants.IDENTIFIER)) {
			bound.addChildren(parseCommaSeparatedIds(parser));
		} else {
			throw new ParseException(String.format("Failed to parse quantifier bound %d", parser.peek().getKind()), parser.current);
		}
		parser.consume(SyntaxTreeConstants.T_IN);
		bound.addChild(Kind.SET_IN.asNode());
		bound.addField("set", parser.translate("expression"));
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
				children.add(parseUnstructuredQuantifierBound(lookahead));
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
	
	private static AstNode parseAssumeProve(SanyReparser parser) throws ParseException {
		AstNode assumeProve = Kind.ASSUME_PROVE.asNode();
		parser.consume(TLAplusParserConstants.ASSUME);
		do {
			if (parser.match(SyntaxTreeConstants.N_Label)) {
				AstNode inner = Kind.INNER_ASSUME_PROVE.asNode();
				SanyReparser innerParser = new SanyReparser(parser.previous().getHeirs());
				innerParser.consume(SyntaxTreeConstants.N_GeneralId);
				inner.addChild(Kind.IDENTIFIER.asNode());
				inner.addChild(innerParser.translate(TLAplusParserConstants.COLONCOLON));
				inner.addChild(innerParser.translate(SyntaxTreeConstants.N_AssumeProve));
				Assert.assertTrue(innerParser.isAtEnd());
				assumeProve.addField("assumption", inner);
			} else {
				assumeProve.addField("assumption", parser.translate("expression or new statement"));
			}
		} while (parser.match(TLAplusParserConstants.COMMA));
		parser.consume(TLAplusParserConstants.PROVE);
		assumeProve.addField("conclusion", parser.translate("expression"));
		return assumeProve;
	}
	
	private static AstNode id(SyntaxTreeNode input) throws ParseException {
		Assert.assertEquals(TLAplusParserConstants.IDENTIFIER, input.getKind());
		switch (input.getImage()) {
			case "TRUE": return Kind.BOOLEAN.asNode();
			case "FALSE": return Kind.BOOLEAN.asNode();
			case "BOOLEAN": return Kind.BOOLEAN_SET.asNode();
			case "STRING": return Kind.STRING_SET.asNode();
			case "Nat": return Kind.NAT_NUMBER_SET.asNode();
			case "Int": return Kind.INT_NUMBER_SET.asNode();
			case "Real": return Kind.REAL_NUMBER_SET.asNode();
			case "@": return Kind.PREV_FUNC_VAL.asNode();
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
			case "\\lnot": return Kind.LNOT.asNode();
			case "\\neg": return Kind.LNOT.asNode();
			case "~": return Kind.LNOT.asNode();
			case "UNION": return Kind.UNION.asNode();
			case "SUBSET": return Kind.POWERSET.asNode();
			case "DOMAIN": return Kind.DOMAIN.asNode();
			case "-.": return Kind.NEGATIVE.asNode();
			case "ENABLED": return Kind.ENABLED.asNode();
			case "UNCHANGED": return Kind.UNCHANGED.asNode();
			case "[]": return Kind.ALWAYS.asNode();
			case "<>": return Kind.EVENTUALLY.asNode();
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
			case "&": return Kind.AMP.asNode();
			case "&&": return Kind.AMPAMP.asNode();
			case "\\approx": return Kind.APPROX.asNode();
			case ":=": return Kind.ASSIGN.asNode();
			case "\\asymp": return Kind.ASYMP.asNode();
			case "\\bigcirc": return Kind.BIGCIRC.asNode();
			case "::=": return Kind.BNF_RULE.asNode();
			case "\\bullet": return Kind.BULLET.asNode();
			case "\\intersect": return Kind.CAP.asNode();
			case "\\cap": return Kind.CAP.asNode();
			case "\\cdot": return Kind.CDOT.asNode();
			case "\\o": return Kind.CIRC.asNode();
			case "\\circ": return Kind.CIRC.asNode();
			case "@@": return Kind.COMPOSE.asNode();
			case "\\cong": return Kind.CONG.asNode();
			case "\\union": return Kind.CUP.asNode();
			case "\\cup": return Kind.CUP.asNode();
			case "\\div": return Kind.DIV.asNode();
			case "$": return Kind.DOL.asNode();
			case "$$": return Kind.DOLDOL.asNode();
			case "\\doteq": return Kind.DOTEQ.asNode();
			case "..": return Kind.DOTS_2.asNode();
			case "...": return Kind.DOTS_3.asNode();
			case "=": return Kind.EQ.asNode();
			case "\\equiv": return Kind.EQUIV.asNode();
			case "!!": return Kind.EXCL.asNode();
			case ">=": return Kind.GEQ.asNode();
			case "\\geq": return Kind.GEQ.asNode();
			case "\\gg": return Kind.GG.asNode();
			case ">": return Kind.GT.asNode();
			case "##": return Kind.HASHHASH.asNode();
			case "<=>": return Kind.IFF.asNode();
			case "=>": return Kind.IMPLIES.asNode();
			case "\\in": return Kind.IN.asNode();
			case "/\\": return Kind.LAND.asNode();
			case "\\land": return Kind.LAND.asNode();
			case "=|": return Kind.LD_TTILE.asNode();
			case "~>": return Kind.LEADS_TO.asNode();
			case "<=": return Kind.LEQ.asNode();
			case "=<": return Kind.LEQ.asNode();
			case "\\leq": return Kind.LEQ.asNode();
			case "\\ll": return Kind.LL.asNode();
			case "\\/": return Kind.LOR.asNode();
			case "\\lor": return Kind.LOR.asNode();
			case "-|": return Kind.LS_TTILE.asNode();
			case "<": return Kind.LT.asNode();
			case "<:": return Kind.MAP_FROM.asNode();
			case ":>": return Kind.MAP_TO.asNode();
			case "-": return Kind.MINUS.asNode();
			case "--": return Kind.MINUSMINUS.asNode();
			case "%": return Kind.MOD.asNode();
			case "%%": return Kind.MODMOD.asNode();
			case "*": return Kind.MUL.asNode();
			case "**": return Kind.MULMUL.asNode();
			case "/=": return Kind.NEQ.asNode();
			case "#": return Kind.NEQ.asNode();
			case "\\notin": return Kind.NOTIN.asNode();
			case "(.)": return Kind.ODOT.asNode();
			case "\\odot": return Kind.ODOT.asNode();
			case "(-)": return Kind.OMINUS.asNode();
			case "\\ominus": return Kind.OMINUS.asNode();
			case "(+)": return Kind.OPLUS.asNode();
			case "\\oplus": return Kind.OPLUS.asNode();
			case "(/)": return Kind.OSLASH.asNode();
			case "\\oslash": return Kind.OSLASH.asNode();
			case "(\\X)": return Kind.OTIMES.asNode();
			case "\\otimes": return Kind.OTIMES.asNode();
			case "+": return Kind.PLUS.asNode();
			case "-+->": return Kind.PLUS_ARROW.asNode();
			case "++": return Kind.PLUSPLUS.asNode();
			case "^": return Kind.POW.asNode();
			case "^^": return Kind.POWPOW.asNode();
			case "\\prec": return Kind.PREC.asNode();
			case "\\preceq": return Kind.PRECEQ.asNode();
			case "\\propto": return Kind.PROPTO.asNode();
			case "??": return Kind.QQ.asNode();
			case "|=": return Kind.RD_TTILE.asNode();
			case "|-": return Kind.RS_TTILE.asNode();
			case "\\": return Kind.SETMINUS.asNode();
			case "\\sim": return Kind.SIM.asNode();
			case "\\simeq": return Kind.SIMEQ.asNode();
			case "/": return Kind.SLASH.asNode();
			case "//": return Kind.SLASHSLASH.asNode();
			case "\\sqcap": return Kind.SQCAP.asNode();
			case "\\sqcup": return Kind.SQCUP.asNode();
			case "\\sqsubset": return Kind.SQSUBSET.asNode();
			case "\\sqsubseteq": return Kind.SQSUBSETEQ.asNode();
			case "\\sqsupset": return Kind.SQSUPSET.asNode();
			case "\\sqsupseteq": return Kind.SQSUPSETEQ.asNode();
			case "\\star": return Kind.STAR.asNode();
			case "\\subset": return Kind.SUBSET.asNode();
			case "\\subseteq": return Kind.SUBSETEQ.asNode();
			case "\\succ": return Kind.SUCC.asNode();
			case "\\succeq": return Kind.SUCCEQ.asNode();
			case "\\supset": return Kind.SUPSET.asNode();
			case "\\supseteq": return Kind.SUPSETEQ.asNode();
			case "\\X": return Kind.TIMES.asNode();
			case "\\times": return Kind.TIMES.asNode();
			case "\\uplus": return Kind.UPLUS.asNode();
			case "|": return Kind.VERT.asNode();
			case "||": return Kind.VERTVERT.asNode();
			case "\\wr": return Kind.WR.asNode();
			default: throw new ParseException(String.format("Operator translation not defined: %s", op), 0);
		}
	}

	private static AstNode postfixOpFromString(String op) throws ParseException {
		switch (op) {
			case "^+": return Kind.SUP_PLUS.asNode();
			case "^*": return Kind.ASTERISK.asNode();
			case "^#": return Kind.SUP_HASH.asNode();
			case "'": return Kind.PRIME.asNode();
			default: throw new ParseException(String.format("Operator translation not defined: %s", op), 0);
		}
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
		SanyReparser parser = new SanyReparser(node.getHeirs());
		switch (node.getKind()) {
			case SyntaxTreeConstants.N_BeginModule: {
				parser.consume(TLAplusParserConstants._BM0, TLAplusParserConstants._BM1);
				parent.addChild(Kind.HEADER_LINE.asNode());
				parser.consume(TLAplusParserConstants.IDENTIFIER);
				parent.addField("name", Kind.IDENTIFIER.asNode());
				parser.consume(TLAplusParserConstants.SEPARATOR);
				parent.addChild(Kind.HEADER_LINE.asNode());
				break;
			} case SyntaxTreeConstants.N_Extends: {
				if (parser.match(TLAplusParserConstants.EXTENDS)) {
					AstNode extensions = Kind.EXTENDS.asNode();
					do {
						extensions.addChild(parser.translate(TLAplusParserConstants.IDENTIFIER));
					} while (parser.match(TLAplusParserConstants.COMMA));
					parent.addChild(extensions);
				}
				break;
			} case SyntaxTreeConstants.N_Body: {
				while (!parser.isAtEnd()) {
					parent.addChild(parser.translate("unit"));
				}
				break;
			} case SyntaxTreeConstants.N_IdentLHS: { // f ==, f(a, b) ==, f(g(_, _)), etc.
				parser.consume(TLAplusParserConstants.IDENTIFIER);
				parent.addField("name", Kind.IDENTIFIER.asNode());
				if (parser.match(TLAplusParserConstants.LBR)) {
					do {
						parent.addField(
							"parameter",
							parser.translate(
								SyntaxTreeConstants.N_IdentDecl,
								SyntaxTreeConstants.N_PrefixDecl,
								SyntaxTreeConstants.N_InfixDecl,
								SyntaxTreeConstants.N_PostfixDecl));
					} while (parser.match(TLAplusParserConstants.COMMA));
					parser.consume(TLAplusParserConstants.RBR);
				}
				break;
			} case SyntaxTreeConstants.N_PrefixLHS: { // \lnot x == ...
				AstNode op = Kind.PREFIX_OP_SYMBOL.asNode();
				op.addChild(prefixOpFromString(parser.advance().getImage()));
				parent.addField("name", op);
				parser.consume(TLAplusParserConstants.IDENTIFIER);
				parent.addField("parameter", Kind.IDENTIFIER.asNode());
				break;
			} case SyntaxTreeConstants.N_InfixLHS: { // x \oplus y == ...
				AstNode op = Kind.INFIX_OP_SYMBOL.asNode();
				parser.consume(TLAplusParserConstants.IDENTIFIER);
				parent.addField("parameter", Kind.IDENTIFIER.asNode());
				op.addChild(infixOpFromString(parser.advance().getImage()));
				parent.addField("name", op);
				parser.consume(TLAplusParserConstants.IDENTIFIER);
				parent.addField("parameter", Kind.IDENTIFIER.asNode());
				break;
			} case SyntaxTreeConstants.N_PostfixLHS: { // x ^+ == ...
				AstNode op = Kind.POSTFIX_OP_SYMBOL.asNode();
				parser.consume(TLAplusParserConstants.IDENTIFIER);
				parent.addField("parameter", Kind.IDENTIFIER.asNode());
				op.addChild(postfixOpFromString(parser.advance().getImage()));
				parent.addField("name", op);
				break;
			} case SyntaxTreeConstants.N_OpArgs: { // (p1, p2, ..., pn)
				parser.consume(TLAplusParserConstants.LBR);
				do {
					parent.addField("parameter", parser.translate("expression"));
				} while (parser.match(TLAplusParserConstants.COMMA));
				parser.consume(TLAplusParserConstants.RBR);
				break;
			} case SyntaxTreeConstants.N_MaybeBound: { // \in Nat or nothing
				if (!parser.isAtEnd()) {
					parser.consume(SyntaxTreeConstants.T_IN);
					parent.addChild(Kind.SET_IN.asNode());
					parent.addField("set", parser.translate("expression"));
				}
				break;
			} case SyntaxTreeConstants.N_FieldVal: { // foo |-> 3
				parser.consume(TLAplusParserConstants.IDENTIFIER);
				parent.addChild(Kind.IDENTIFIER.asNode());
				parent.addChild(parser.translate(TLAplusParserConstants.MAPTO));
				parent.addChild(parser.translate("expression"));
				break;
			} case SyntaxTreeConstants.N_FieldSet: { // foo : Nat
				parser.consume(TLAplusParserConstants.IDENTIFIER);
				parent.addChild(Kind.IDENTIFIER.asNode());
				parser.consume(TLAplusParserConstants.COLON);
				parent.addChild(parser.translate("expression"));
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
		SanyReparser parser = new SanyReparser(node.getHeirs());
		switch (node.getKind()) {
			case SyntaxTreeConstants.N_Module: { // ---- MODULE Test ---- ... ====
				AstNode module = Kind.MODULE.asNode();
				parser.flatTranslate(module, SyntaxTreeConstants.N_BeginModule);
				parser.flatTranslate(module, SyntaxTreeConstants.N_Extends);
				parser.flatTranslate(module, SyntaxTreeConstants.N_Body);
				module.addChild(parser.translate(SyntaxTreeConstants.N_EndModule));
				return module;
			} case SyntaxTreeConstants.N_EndModule: { // ====
				parser.consume(TLAplusParserConstants.END_MODULE);
				Assert.assertTrue(parser.isAtEnd());
				return Kind.DOUBLE_LINE.asNode();
			} case TLAplusParserConstants.SEPARATOR: { // ----
				Assert.assertTrue(parser.isAtEnd());
				return Kind.SINGLE_LINE.asNode();
			} case SyntaxTreeConstants.N_ParamDeclaration: { // CONSTANTS x, f(_, _)
				AstNode constants = Kind.CONSTANT_DECLARATION.asNode();
				parser.consume(SyntaxTreeConstants.N_ConsDecl);
				do {
					constants.addChild(parser.translate(
						SyntaxTreeConstants.N_IdentDecl,
						SyntaxTreeConstants.N_PrefixDecl,
						SyntaxTreeConstants.N_InfixDecl,
						SyntaxTreeConstants.N_PostfixDecl));
				} while (parser.match(TLAplusParserConstants.COMMA));
				Assert.assertTrue(parser.isAtEnd());
				return constants;
			} case SyntaxTreeConstants.N_VariableDeclaration: { // VARIABLES x, y, z
				AstNode variables = Kind.VARIABLE_DECLARATION.asNode();
				parser.consume(TLAplusParserConstants.VARIABLE);
				variables.addChildren(parseCommaSeparatedIds(parser));
				Assert.assertTrue(parser.isAtEnd());
				return variables;
			} case SyntaxTreeConstants.N_Instance: { // INSTANCE M, LOCAL INSTANCE N, etc.
				if (parser.match(TLAplusParserConstants.LOCAL)) {
					AstNode localDefn = Kind.LOCAL_DEFINITION.asNode();
					localDefn.addChild(parser.translate(SyntaxTreeConstants.N_NonLocalInstance));
					Assert.assertTrue(parser.isAtEnd());
					return localDefn;
				} else {
					AstNode instance = parser.translate(SyntaxTreeConstants.N_NonLocalInstance);
					Assert.assertTrue(parser.isAtEnd());
					return instance;
				}
			} case SyntaxTreeConstants.N_NonLocalInstance: { // INSTANCE M WITH a <- b, c <- d
				AstNode instance = Kind.INSTANCE.asNode();
				parser.consume(TLAplusParserConstants.INSTANCE);
				instance.addChild(parser.translate(TLAplusParserConstants.IDENTIFIER));
				if (parser.match(TLAplusParserConstants.WITH)) {
					do {
						instance.addChild(parser.translate(SyntaxTreeConstants.N_Substitution));
					} while (parser.match(TLAplusParserConstants.COMMA));
				}
				Assert.assertTrue(parser.isAtEnd());
				return instance;
			} case SyntaxTreeConstants.N_ModuleDefinition: { // M == INSTANCE O WITH x <- y
				AstNode moduleDefinition = Kind.MODULE_DEFINITION.asNode();
				parser.flatTranslate(moduleDefinition, SyntaxTreeConstants.N_IdentLHS);
				moduleDefinition.addChild(parser.translate(TLAplusParserConstants.DEF));
				moduleDefinition.addChild(parser.translate(SyntaxTreeConstants.N_NonLocalInstance));
				Assert.assertTrue(parser.isAtEnd());
				return moduleDefinition;
			} case SyntaxTreeConstants.N_Substitution: { // x <- y
				AstNode substitution = Kind.SUBSTITUTION.asNode();
				substitution.addChild(parser.translate(
						TLAplusParserConstants.IDENTIFIER,
						SyntaxTreeConstants.N_NonExpPrefixOp,
						SyntaxTreeConstants.N_InfixOp,
						SyntaxTreeConstants.N_PostfixOp));
				substitution.addChild(parser.translate(TLAplusParserConstants.SUBSTITUTE));
				substitution.addChild(parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
				return substitution;
			} case TLAplusParserConstants.SUBSTITUTE: { // <-
				Assert.assertTrue(parser.isAtEnd());
				return Kind.GETS.asNode();
			} case SyntaxTreeConstants.N_OperatorDefinition: { // op(a, b) == expr
				AstNode operatorDefinition = Kind.OPERATOR_DEFINITION.asNode();
				parser.flatTranslate(operatorDefinition,
						SyntaxTreeConstants.N_IdentLHS,
						SyntaxTreeConstants.N_PrefixLHS,
						SyntaxTreeConstants.N_InfixLHS,
						SyntaxTreeConstants.N_PostfixLHS);
				operatorDefinition.addChild(parser.translate(TLAplusParserConstants.DEF));
				operatorDefinition.addField("definition", parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
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
					op.addField("parameter", parser.translate(TLAplusParserConstants.US));
				} while (parser.match(TLAplusParserConstants.COMMA));
				parser.consume(TLAplusParserConstants.RBR);
				Assert.assertTrue(parser.isAtEnd());
				return op;
			} case SyntaxTreeConstants.N_Recursive: { // RECURSIVE F(_, _), G(_)
				AstNode recursiveDeclaration = Kind.RECURSIVE_DECLARATION.asNode();
				parser.consume(TLAplusParserConstants.RECURSIVE);
				recursiveDeclaration.addChildren(parseCommaSeparatedNodes(parser, "operator declaration"));
				Assert.assertTrue(parser.isAtEnd());
				return recursiveDeclaration;
			} case TLAplusParserConstants.US: { // _
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
			} case TLAplusParserConstants.AND: { // /\
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
			} case TLAplusParserConstants.OR: { // \/
				Assert.assertTrue(parser.isAtEnd());
				return Kind.BULLET_DISJ.asNode();
			} case SyntaxTreeConstants.N_GeneralId: { // foo!bar!baz!x
				SyntaxTreeNode prefix = parser.consume(SyntaxTreeConstants.N_IdPrefix);
				if (parser.match(SyntaxTreeConstants.N_StructOp)) {
					AstNode subexpr = Kind.SUBEXPRESSION.asNode();
					subexpr.addChild(translate(prefix));
					subexpr.addChild(Kind.SUBEXPR_TREE_NAV.asNode().addChild(translate(parser.previous())));
					Assert.assertTrue(parser.isAtEnd());
					return subexpr;
				} else if (parser.match(TLAplusParserConstants.ProofStepLexeme)) {
					// TODO
				} else {
					parser.consume(
						TLAplusParserConstants.IDENTIFIER,
						SyntaxTreeConstants.N_NonExpPrefixOp,
						SyntaxTreeConstants.N_InfixOp,
						SyntaxTreeConstants.N_PostfixOp);
				}
				AstNode op = translate(parser.previous());
				Assert.assertTrue(parser.isAtEnd());
				if (0 == prefix.getHeirs().length) {
					return op;
				}
				return Kind.PREFIXED_OP.asNode()
						.addField("prefix", translate(prefix))
						.addField("op", op);
			} case SyntaxTreeConstants.N_IdPrefix: { // A!B!C!
				AstNode subexpr = Kind.SUBEXPR_PREFIX.asNode();
				do {
					subexpr.addChild(parser.translate(SyntaxTreeConstants.N_IdPrefixElement));
				} while (!parser.isAtEnd());
				Assert.assertTrue(parser.isAtEnd());
				return subexpr;
			} case SyntaxTreeConstants.N_IdPrefixElement: { // A!
				AstNode component = null;
				if (parser.match(TLAplusParserConstants.IDENTIFIER)) {
					component = Kind.SUBEXPR_COMPONENT.asNode();
					if (parser.match(SyntaxTreeConstants.N_OpArgs)) {
						AstNode op = Kind.BOUND_OP.asNode();
						op.addField("name", Kind.IDENTIFIER_REF.asNode());
						flatTranslate(op, parser.previous());
						component.addChild(op);
					} else {
						component.addChild(Kind.IDENTIFIER_REF.asNode());
					}
				} else if (parser.match(SyntaxTreeConstants.N_OpArgs)) {
					component = Kind.SUBEXPR_TREE_NAV.asNode();
					AstNode args = Kind.OPERATOR_ARGS.asNode();
					SanyReparser argParser = new SanyReparser(parser.previous().getHeirs());
					argParser.consume(TLAplusParserConstants.LBR);
					do {
						args.addChild(argParser.translate("op or expression"));
					} while (argParser.match(TLAplusParserConstants.COMMA));
					argParser.consume(TLAplusParserConstants.RBR);
					Assert.assertTrue(argParser.isAtEnd());
					component.addChild(args);
				} else {
					component = Kind.SUBEXPR_TREE_NAV.asNode();
					component.addChild(parser.translate(SyntaxTreeNode.N_StructOp));
				}
				parser.consume(TLAplusParserConstants.BANG);
				Assert.assertTrue(parser.isAtEnd());
				return component;
			} case SyntaxTreeConstants.N_StructOp: { // op!<<!>>!:!@
				if (!parser.isAtEnd()) {
					parser.consume(SyntaxTreeConstants.N_Number);
					Assert.assertTrue(parser.isAtEnd());
					return Kind.CHILD_ID.asNode();
				}
				Assert.assertTrue(parser.isAtEnd());
				String image = node.getImage();
				switch (image) {
					case "<<": return Kind.LANGLE_BRACKET.asNode();
					case ">>": return Kind.RANGLE_BRACKET.asNode();
					case ":": return Kind.COLON.asNode();
					case "@": return Kind.ADDRESS.asNode();
					default: throw new ParseException(String.format("Unknown subexpression tree nav symbol %s", image), parser.current);
				}
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
				// Set filters are restrictive and only allow one element from generator
				AstNode bound = Kind.QUANTIFIER_BOUND.asNode();
				if (parser.match(TLAplusParserConstants.IDENTIFIER)) {
					bound.addField("intro", Kind.IDENTIFIER.asNode());
				} else {
					bound.addField("intro", parser.translate(SyntaxTreeConstants.N_IdentifierTuple));
				}
				parser.consume(SyntaxTreeConstants.T_IN);
				bound.addChild(Kind.SET_IN.asNode());
				bound.addField("set", parser.translate("expression"));
				setFilter.addField("generator", bound);
				parser.consume(TLAplusParserConstants.COLON);
				setFilter.addField("filter", parser.translate("expression"));
				parser.consume(TLAplusParserConstants.RBC);
				Assert.assertTrue(parser.isAtEnd());
				return setFilter;
			} case SyntaxTreeConstants.N_SetOfAll: { // {f(x) : x \in Nat}
				AstNode setMap = Kind.SET_MAP.asNode();
				parser.consume(TLAplusParserConstants.LBC);
				setMap.addField("map", parser.translate("expression"));
				parser.consume(TLAplusParserConstants.COLON);
				do {
					setMap.addField("generator", parser.translate(SyntaxTreeConstants.N_QuantBound));
				} while (parser.match(TLAplusParserConstants.COMMA));
				parser.consume(TLAplusParserConstants.RBC);
				Assert.assertTrue(parser.isAtEnd());
				return setMap;
			} case SyntaxTreeConstants.N_BoundQuant: { // \A x, y \in Nat, z \in Real: expr
				AstNode quant = Kind.BOUNDED_QUANTIFICATION.asNode();
				quant.addField("quantifier", parser.translate(TLAplusParserConstants.EXISTS, TLAplusParserConstants.FORALL));
				do {
					quant.addField("bound", parser.translate(SyntaxTreeConstants.N_QuantBound));
				} while (parser.match(TLAplusParserConstants.COMMA));
				parser.consume(TLAplusParserConstants.COLON);
				quant.addField("expression", parser.translate("expression"));
				return quant;
			} case SyntaxTreeConstants.N_UnboundQuant: { // \AA x, y : P(x, y)
				AstNode quant = Kind.UNBOUNDED_QUANTIFICATION.asNode();
				quant.addField("quantifier", parser.translate(
						TLAplusParserConstants.EXISTS,
						TLAplusParserConstants.FORALL,
						TLAplusParserConstants.T_FORALL,
						TLAplusParserConstants.T_EXISTS));
				do {
					parser.consume(TLAplusParserConstants.IDENTIFIER);
					quant.addField("intro", Kind.IDENTIFIER.asNode());
				} while (parser.match(TLAplusParserConstants.COMMA));
				parser.consume(TLAplusParserConstants.COLON);
				quant.addField("expression", parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
				return quant;
			} case SyntaxTreeConstants.N_UnboundOrBoundChoose: { // CHOOSE x \in Nat : x > 0
				AstNode choose = Kind.CHOOSE.asNode();
				parser.consume(TLAplusParserConstants.CHOOSE);
				if (parser.match(TLAplusParserConstants.IDENTIFIER)) {
					choose.addField("intro", Kind.IDENTIFIER.asNode());
				} else {
					choose.addField("intro", parser.translate(SyntaxTreeConstants.N_IdentifierTuple));
				}
				parser.flatTranslate(choose, SyntaxTreeNode.N_MaybeBound);
				parser.consume(TLAplusParserConstants.COLON);
				choose.addField("expression", parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
				return choose;
			} case TLAplusParserConstants.EXISTS: { // \E
				Assert.assertTrue(parser.isAtEnd());
				return Kind.EXISTS.asNode();
			} case TLAplusParserConstants.FORALL: { // \A
				Assert.assertTrue(parser.isAtEnd());
				return Kind.FORALL.asNode();
			} case TLAplusParserConstants.T_FORALL: { // \AA
				Assert.assertTrue(parser.isAtEnd());
				return Kind.TEMPORAL_FORALL.asNode();
			} case TLAplusParserConstants.T_EXISTS: { // \EE
				Assert.assertTrue(parser.isAtEnd());
				return Kind.TEMPORAL_EXISTS.asNode();
			} case SyntaxTreeConstants.N_QuantBound: { // x, y \in Nat
				AstNode quantBound = Kind.QUANTIFIER_BOUND.asNode();
				if (parser.check(TLAplusParserConstants.IDENTIFIER)) {
					do {
						parser.consume(TLAplusParserConstants.IDENTIFIER);
						quantBound.addField("intro", Kind.IDENTIFIER.asNode());
					} while (parser.match(TLAplusParserConstants.COMMA));
				} else {
					quantBound.addField("intro", parser.translate(SyntaxTreeConstants.N_IdentifierTuple));
				}
				parser.consume(SyntaxTreeConstants.T_IN);
				quantBound.addChild(Kind.SET_IN.asNode());
				quantBound.addField("set", parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
				return quantBound;
			} case SyntaxTreeConstants.N_IdentifierTuple: { // <<a, b, c>>
				AstNode tuple = parseTupleOfIdentifiers(parser);
				Assert.assertTrue(parser.isAtEnd());
				return tuple;
			} case SyntaxTreeConstants.N_FcnConst: { // [n \in Nat |-> 2*n]
				AstNode function = Kind.FUNCTION_LITERAL.asNode();
				parser.consume(TLAplusParserConstants.LSB);
				do {
					function.addChild(parser.translate(SyntaxTreeConstants.N_QuantBound));
				} while (parser.match(TLAplusParserConstants.COMMA));
				function.addChild(parser.translate(TLAplusParserConstants.MAPTO));
				function.addChild(parser.translate("expression"));
				parser.consume(TLAplusParserConstants.RSB);
				Assert.assertTrue(parser.isAtEnd());
				return function;
			} case TLAplusParserConstants.MAPTO: { // |->
				Assert.assertTrue(parser.isAtEnd());
				return Kind.ALL_MAP_TO.asNode();
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
			} case SyntaxTreeConstants.N_Except: { // [f EXCEPT ![x] = y]
				AstNode except = Kind.EXCEPT.asNode();
				parser.consume(TLAplusParserConstants.LSB);
				except.addField("expr_to_update", parser.translate("expression"));
				parser.consume(TLAplusParserConstants.EXCEPT);
				do {
					except.addChild(parser.translate(SyntaxTreeConstants.N_ExceptSpec));
				} while (parser.match(TLAplusParserConstants.COMMA));
				parser.consume(TLAplusParserConstants.RSB);
				Assert.assertTrue(parser.isAtEnd());
				return except;
			} case SyntaxTreeConstants.N_ExceptSpec: { // ![x] = y
				AstNode update = Kind.EXCEPT_UPDATE.asNode();
				parser.consume(TLAplusParserConstants.BANG);
				AstNode updateSpec = Kind.EXCEPT_UPDATE_SPECIFIER.asNode();
				do {
					updateSpec.addChild(parser.translate(SyntaxTreeConstants.N_ExceptComponent));
				} while (!parser.match(SyntaxTreeConstants.T_EQUAL));
				update.addField("update_specifier", updateSpec);
				update.addField("new_val", parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
				return update;
			} case SyntaxTreeConstants.N_ExceptComponent: { // [x]
				if (parser.match(TLAplusParserConstants.LSB)) {
					AstNode update = Kind.EXCEPT_UPDATE_FN_APPL.asNode();
					update.addChildren(parseCommaSeparatedNodes(parser, "expression"));
					parser.consume(TLAplusParserConstants.RSB);
					Assert.assertTrue(parser.isAtEnd());
					return update;
				} else {
					AstNode update = Kind.EXCEPT_UPDATE_RECORD_FIELD.asNode();
					parser.consume(TLAplusParserConstants.DOT);
					update.addChild(parser.translate(TLAplusParserConstants.IDENTIFIER));
					Assert.assertTrue(parser.isAtEnd());
					return update;
				}
			} case SyntaxTreeConstants.N_RcdConstructor: { // [foo |-> 1, bar |-> 2]
				AstNode record = Kind.RECORD_LITERAL.asNode();
				parser.consume(TLAplusParserConstants.LSB);
				do {
					parser.flatTranslate(record, SyntaxTreeConstants.N_FieldVal);
				} while (parser.match(TLAplusParserConstants.COMMA));
				parser.consume(TLAplusParserConstants.RSB);
				Assert.assertTrue(parser.isAtEnd());
				return record;
			} case SyntaxTreeConstants.N_SetOfRcds: { // [foo : Nat, bar : Real]
				AstNode record = Kind.SET_OF_RECORDS.asNode();
				parser.consume(TLAplusParserConstants.LSB);
				do {
					parser.flatTranslate(record, SyntaxTreeConstants.N_FieldSet);
				} while (parser.match(TLAplusParserConstants.COMMA));
				parser.consume(TLAplusParserConstants.RSB);
				Assert.assertTrue(parser.isAtEnd());
				return record;
			} case SyntaxTreeConstants.N_RecordComponent: { // foo.bar
				AstNode record = Kind.RECORD_VALUE.asNode();
				record.addChild(parser.translate("expression"));
				parser.consume(TLAplusParserConstants.DOT);
				record.addChild(parser.translate(TLAplusParserConstants.IDENTIFIER));
				Assert.assertTrue(parser.isAtEnd());
				return record;
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
			} case SyntaxTreeConstants.N_Times: { // S \X P \X Q
				List<AstNode> exprs = new ArrayList<AstNode>();
				do {
					exprs.add(parser.translate("expression"));
				} while (parser.match(SyntaxTreeConstants.N_GenInfixOp));
				// Convert flat list to left-associative tree
				AstNode lhs = exprs.get(0);
				for (int i = 1; i < exprs.size(); i++) {
					AstNode op = Kind.BOUND_INFIX_OP.asNode();
					op.addField("lhs", lhs);
					op.addField("symbol", Kind.TIMES.asNode());
					op.addField("rhs", exprs.get(i));
					lhs = op;
				}
				Assert.assertTrue(parser.isAtEnd());
				return lhs;
			} case SyntaxTreeConstants.N_FcnAppl: { // f[x,y,z]
				AstNode functionEvaluation = Kind.FUNCTION_EVALUATION.asNode();
				functionEvaluation.addChild(parser.translate("expression"));
				parser.consume(TLAplusParserConstants.LSB);
				functionEvaluation.addChildren(parseCommaSeparatedNodes(parser, "expression"));
				parser.consume(TLAplusParserConstants.RSB);
				Assert.assertTrue(parser.isAtEnd());
				return functionEvaluation;
			} case SyntaxTreeConstants.N_OpApplication: { // f(a, b, c) or nonfix op
				SyntaxTreeNode id = parser.consume(SyntaxTreeConstants.N_GeneralId);
				SanyReparser idParser = new SanyReparser(id.getHeirs());
				SyntaxTreeNode prefix = idParser.consume(SyntaxTreeConstants.N_IdPrefix);
				AstNode nameOrSymbol = idParser.translate(
						TLAplusParserConstants.IDENTIFIER,
						SyntaxTreeConstants.N_NonExpPrefixOp,
						SyntaxTreeConstants.N_InfixOp,
						SyntaxTreeConstants.N_PostfixOp);
				Assert.assertTrue(idParser.isAtEnd());
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
				parser.flatTranslate(op, SyntaxTreeConstants.N_OpArgs);
				Assert.assertTrue(parser.isAtEnd());
				if (prefix.getHeirs().length > 0) {
					AstNode prefixedOp = Kind.PREFIXED_OP.asNode();
					prefixedOp.addField("prefix", translate(prefix));
					prefixedOp.addField("op", op);
					return prefixedOp;
				} else {
					return op;
				}
			} case SyntaxTreeConstants.N_PrefixDecl: { // Prefix op declaration, ex. f(-. _) == ...
				AstNode op = Kind.OPERATOR_DECLARATION.asNode();
				op.addField("name", parser.translate(SyntaxTreeConstants.N_NonExpPrefixOp));
				op.addChild(parser.translate(TLAplusParserConstants.US));
				Assert.assertTrue(parser.isAtEnd());
				return op;
			} case SyntaxTreeConstants.N_PrefixExpr: { // Prefix op application, full expression ex. SUBSET x
				AstNode boundPrefixOp = Kind.BOUND_PREFIX_OP.asNode();
				// Hilariously, the negative "-" prefix operator here appears as an infix operator
				if (parser.match(SyntaxTreeConstants.N_GenInfixOp)) {
					boundPrefixOp.addField("symbol", Kind.NEGATIVE.asNode());
				} else {
					boundPrefixOp.addField("symbol", parser.translate(SyntaxTreeConstants.N_GenPrefixOp));
				}
				boundPrefixOp.addField("rhs", parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
				return boundPrefixOp;
			} case SyntaxTreeConstants.N_GenPrefixOp: { // Prefix op application, just operator ex. SUBSET
				SyntaxTreeNode prefix = parser.consume(SyntaxTreeConstants.N_IdPrefix);
				// ID prefix is holdover from TLA+ v1, not used in v2; superseded by nonfix ops
				Assert.assertEquals(0, prefix.getHeirs().length);
				SyntaxTreeNode op = parser.consume(SyntaxTreeConstants.N_PrefixOp);
				Assert.assertTrue(parser.isAtEnd());
				return prefixOpFromString(op.getImage());
			} case SyntaxTreeConstants.N_GenNonExpPrefixOp: { // Prefix op as higher-order op parameter
				SyntaxTreeNode prefix = parser.consume(SyntaxTreeConstants.N_IdPrefix);
				Assert.assertEquals(0, prefix.getHeirs().length);
				AstNode op = parser.translate(SyntaxTreeConstants.N_NonExpPrefixOp);
				Assert.assertTrue(parser.isAtEnd());
				return op;
			} case SyntaxTreeConstants.N_NonExpPrefixOp: { // Prefix op symbol; declaration, nonfix, or ref
				AstNode op = Kind.PREFIX_OP_SYMBOL.asNode();
				Assert.assertTrue(parser.isAtEnd());
				return op.addChild(prefixOpFromString(node.image.toString()));
			} case SyntaxTreeConstants.N_InfixDecl: { // _ + _, _ - _
				AstNode op = Kind.OPERATOR_DECLARATION.asNode();
				op.addChild(parser.translate(TLAplusParserConstants.US));
				op.addField("name", parser.translate(SyntaxTreeConstants.N_InfixOp));
				op.addChild(parser.translate(TLAplusParserConstants.US));
				Assert.assertTrue(parser.isAtEnd());
				return op;
			} case SyntaxTreeConstants.N_InfixExpr: { // Infix op application, full expression ex. 1 + 2
				AstNode boundInfixOp = Kind.BOUND_INFIX_OP.asNode();
				boundInfixOp.addField("lhs", parser.translate("expression"));
				// Have to flatten out the N_GenInfixOp parse logic here to preserve
				// that translation rule as a viable entry point for op references.
				SyntaxTreeNode genOp = parser.consume(SyntaxTreeConstants.N_GenInfixOp);
				SanyReparser genOpParser = new SanyReparser(genOp.getHeirs());
				SyntaxTreeNode prefix = genOpParser.consume(SyntaxTreeConstants.N_IdPrefix);
				Assert.assertEquals(0, prefix.getHeirs().length);
				SyntaxTreeNode op = genOpParser.consume(SyntaxTreeConstants.N_InfixOp, SyntaxTreeConstants.T_IN);
				Assert.assertTrue(genOpParser.isAtEnd());
				boundInfixOp.addField("symbol", infixOpFromString(op.getImage()));
				boundInfixOp.addField("rhs", parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
				return boundInfixOp;
			} case SyntaxTreeConstants.N_GenInfixOp: { // Infix op application, just the symbol ex. +
				SyntaxTreeNode prefix = parser.consume(SyntaxTreeConstants.N_IdPrefix);
				// ID prefix is holdover from TLA+ v1, not used in v2; superseded by nonfix ops
				Assert.assertEquals(0, prefix.getHeirs().length);
				// Sometimes \in appears as N_InfixOp, and sometimes it appears as T_IN
				AstNode op = parser.translate(SyntaxTreeConstants.N_InfixOp, SyntaxTreeConstants.T_IN);
				Assert.assertTrue(parser.isAtEnd());
				return op;
			} case SyntaxTreeConstants.N_InfixOp: { // Infix op symbol; declaration, nonfix, or ref
				AstNode op = Kind.INFIX_OP_SYMBOL.asNode();
				Assert.assertTrue(parser.isAtEnd());
				return op.addChild(infixOpFromString(node.image.toString()));
			} case SyntaxTreeConstants.N_PostfixDecl: { // _ ', _ ^+
				AstNode op = Kind.OPERATOR_DECLARATION.asNode();
				op.addChild(parser.translate(TLAplusParserConstants.US));
				op.addField("name", parser.translate(SyntaxTreeConstants.N_PostfixOp));
				Assert.assertTrue(parser.isAtEnd());
				return op;
			} case SyntaxTreeConstants.N_PostfixExpr: { // Postfix op application, full expression ex. x^+
				AstNode boundPostfixOp = Kind.BOUND_POSTFIX_OP.asNode();
				boundPostfixOp.addField("lhs", parser.translate("expression"));
				// Have to flatten out the N_GenPostfixOp parse logic here to preserve
				// that translation rule as a viable entry point for op references.
				SyntaxTreeNode genOp = parser.consume(SyntaxTreeConstants.N_GenPostfixOp);
				SanyReparser genOpParser = new SanyReparser(genOp.getHeirs());
				SyntaxTreeNode prefix = genOpParser.consume(SyntaxTreeConstants.N_IdPrefix);
				Assert.assertEquals(0, prefix.getHeirs().length);
				SyntaxTreeNode op = genOpParser.consume(SyntaxTreeConstants.N_PostfixOp);
				Assert.assertTrue(genOpParser.isAtEnd());
				Assert.assertTrue(parser.isAtEnd());
				boundPostfixOp.addField("symbol", postfixOpFromString(op.getImage()));
				return boundPostfixOp;
			} case SyntaxTreeConstants.N_GenPostfixOp: { // Postfix op reference, just the symbol ex. ^+
				SyntaxTreeNode prefix = parser.consume(SyntaxTreeConstants.N_IdPrefix);
				// ID prefix is holdover from TLA+ v1, not used in v2; superseded by nonfix ops
				Assert.assertEquals(0, prefix.getHeirs().length);
				AstNode op = parser.translate(SyntaxTreeConstants.N_PostfixOp);
				Assert.assertTrue(parser.isAtEnd());
				return op;
			} case SyntaxTreeConstants.N_PostfixOp: { // Postfix op symbol; declaration, nonfix, or ref
				AstNode op = Kind.POSTFIX_OP_SYMBOL.asNode();
				Assert.assertTrue(parser.isAtEnd());
				return op.addChild(postfixOpFromString(node.image.toString()));
			} case SyntaxTreeConstants.T_IN: { // \in as an infix operator
				Assert.assertTrue(parser.isAtEnd());
				return Kind.IN.asNode();
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
			} case SyntaxTreeConstants.N_Lambda: {
				AstNode lambda = Kind.LAMBDA.asNode();
				parser.consume(TLAplusParserConstants.LAMBDA);
				do {
					parser.consume(TLAplusParserConstants.IDENTIFIER);
					lambda.addChild(Kind.IDENTIFIER.asNode());
				} while (parser.match(TLAplusParserConstants.COMMA));
				parser.consume(TLAplusParserConstants.COLON);
				lambda.addChild(parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
				return lambda;
			} case SyntaxTreeConstants.N_Theorem: { // THEOREM name == ...
				AstNode theorem = Kind.THEOREM.asNode();
				parser.consume(TLAplusParserConstants.THEOREM, TLAplusParserConstants.PROPOSITION);
				if (parser.match(TLAplusParserConstants.IDENTIFIER)) {
					theorem.addField("name", Kind.IDENTIFIER.asNode());
					parser.consume(TLAplusParserConstants.DEF);
					theorem.addChild(Kind.DEF_EQ.asNode());
				}
				theorem.addField("statement", parser.translate("expression or assume/prove"));
				if (!parser.isAtEnd()) {
					theorem.addField("proof", parser.translate("proof"));
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
					proof.addChild(parser.translate("expression"));
				} while (!parser.isAtEnd());
				Assert.assertTrue(parser.isAtEnd());
				return proof;
			} case SyntaxTreeConstants.N_HaveStep: { // HAVE x > y
				AstNode proof = Kind.HAVE_PROOF_STEP.asNode();
				parser.consume(TLAplusParserConstants.HAVE);
				proof.addChild(parser.translate("expression"));
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
				proof.addChild(parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
				return proof;
			} case SyntaxTreeConstants.N_CaseStep: { // CASE y < 0
				AstNode proof = Kind.CASE_PROOF_STEP.asNode();
				parser.consume(TLAplusParserConstants.CASE);
				proof.addChild(parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
				return proof;
			} case SyntaxTreeConstants.N_PickStep: { // PICK x \in Nat : x > 0
				AstNode proof = Kind.PICK_PROOF_STEP.asNode();
				parser.consume(TLAplusParserConstants.PICK);
				proof.addChildren(parseBoundListOrIdentifierList(parser));
				parser.consume(TLAplusParserConstants.COLON);
				proof.addChild(parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
				return proof;
			} case SyntaxTreeConstants.N_UseOrHide: { // USE A, B DEFS MODULE M, +
				AstNode proof = Kind.USE_OR_HIDE.asNode();
				parser.consume(TLAplusParserConstants.USE, TLAplusParserConstants.HIDE);
				proof.addChild(parseUseBody(parser));
				Assert.assertTrue(parser.isAtEnd());
				return proof;
			} case SyntaxTreeConstants.N_AssumeProve: { // ASSUME P PROVE Q
				AstNode assumeProve = parseAssumeProve(parser);
				Assert.assertTrue(parser.isAtEnd());
				return assumeProve;
			} case SyntaxTreeConstants.N_NewSymb: { // NEW TEMPORAL T \in S
				AstNode newStatement = Kind.NEW.asNode();
				int[] statementLevels = {
						TLAplusParserConstants.CONSTANT,
						TLAplusParserConstants.VARIABLE,
						TLAplusParserConstants.STATE,
						TLAplusParserConstants.ACTION,
						TLAplusParserConstants.TEMPORAL
					};
				if (parser.match(TLAplusParserConstants.NEW)) {
					if (parser.match(statementLevels)) {
						newStatement.addChild(Kind.STATEMENT_LEVEL.asNode());
					}
				} else {
					parser.consume(statementLevels);
					newStatement.addChild(Kind.STATEMENT_LEVEL.asNode());
				}
				newStatement.addChild(parser.translate(SyntaxTreeConstants.N_IdentDecl));
				if (parser.match(TLAplusParserConstants.IN)) {
					newStatement.addChild(Kind.SET_IN.asNode());
					newStatement.addChild(parser.translate("expression"));
				}
				Assert.assertTrue(parser.isAtEnd());
				return newStatement;
			} case SyntaxTreeConstants.N_Label: { // lbl(a, b) :: expr
				AstNode label = Kind.LABEL.asNode();
				label.addField("name", Kind.IDENTIFIER.asNode());
				SyntaxTreeNode labelName = parser.consume(SyntaxTreeConstants.N_GeneralId, SyntaxTreeConstants.N_OpApplication);
				if (labelName.isKind(SyntaxTreeConstants.N_OpApplication)) {
					SanyReparser nameParser = new SanyReparser(labelName.getHeirs());
					nameParser.consume(SyntaxTreeConstants.N_GeneralId);
					nameParser.flatTranslate(label, SyntaxTreeConstants.N_OpArgs);
				}
				label.addChild(parser.translate(TLAplusParserConstants.COLONCOLON));
				label.addField("expression", parser.translate("expression"));
				Assert.assertTrue(parser.isAtEnd());
				return label;
			} case TLAplusParserConstants.COLONCOLON: { // ::
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
