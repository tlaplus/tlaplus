package tla2sany;

import tla2sany.modanalyzer.SyntaxTreePrinter;
import tla2sany.parser.SyntaxTreeNode;
import tla2sany.parser.TLAplusParser;
import tla2sany.parser.TLAplusParserConstants;
import tla2sany.st.SyntaxTreeConstants;
import tla2sany.st.TreeNode;

import java.io.PrintWriter;
import java.lang.Character;
import java.text.ParseException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.junit.Assert;

public class AstDsl {	
	/**
	 * Enumeration of all node kinds in the AST DSL. This list was generated
	 * by running the following short Python3 script against node-types.json
	 * in the tree-sitter-tlaplus repository:
	 * 
	 * import json
	 * f = open('src/node-types.json', 'r', encoding='utf-8')
	 * data = json.load(f)
	 * f.close()
	 * names = [
     *   f'\t\t{item["type"].upper()} ("{item["type"]}")'
     *   for item in data
     *   if item['named'] and not item['type'].startswith('_')
	 * ]
	 * print(',\n'.join(names) + ';\n')
	 */
	public static enum AstNodeKind {
		ADDRESS ("address"),
		ALL_MAP_TO ("all_map_to"),
		ALWAYS ("always"),
		APPROX ("approx"),
		ASSIGN ("assign"),
		ASSUME_PROVE ("assume_prove"),
		ASSUMPTION ("assumption"),
		ASYMP ("asymp"),
		BIGCIRC ("bigcirc"),
		BINARY_NUMBER ("binary_number"),
		BLOCK_COMMENT ("block_comment"),
		BLOCK_COMMENT_TEXT ("block_comment_text"),
		BNF_RULE ("bnf_rule"),
		BOOLEAN ("boolean"),
		BOUND_INFIX_OP ("bound_infix_op"),
		BOUND_NONFIX_OP ("bound_nonfix_op"),
		BOUND_OP ("bound_op"),
		BOUND_POSTFIX_OP ("bound_postfix_op"),
		BOUND_PREFIX_OP ("bound_prefix_op"),
		BOUNDED_QUANTIFICATION ("bounded_quantification"),
		BULLET ("bullet"),
		BULLET_CONJ ("bullet_conj"),
		BULLET_DISJ ("bullet_disj"),
		CAP ("cap"),
		CASE ("case"),
		CASE_ARM ("case_arm"),
		CASE_ARROW ("case_arrow"),
		CASE_BOX ("case_box"),
		CASE_PROOF_STEP ("case_proof_step"),
		CDOT ("cdot"),
		CHILD_ID ("child_id"),
		CHOOSE ("choose"),
		CIRC ("circ"),
		COLON ("colon"),
		CONG ("cong"),
		CONJ_ITEM ("conj_item"),
		CONJ_LIST ("conj_list"),
		CONSTANT_DECLARATION ("constant_declaration"),
		CUP ("cup"),
		DEF_EQ ("def_eq"),
		DEFINITION_PROOF_STEP ("definition_proof_step"),
		DISJ_ITEM ("disj_item"),
		DISJ_LIST ("disj_list"),
		DIV ("div"),
		DOMAIN ("domain"),
		DOTEQ ("doteq"),
		DOTS_2 ("dots_2"),
		DOTS_3 ("dots_3"),
		DOUBLE_LINE ("double_line"),
		ENABLED ("enabled"),
		EQ ("eq"),
		EQUIV ("equiv"),
		ESCAPE_CHAR ("escape_char"),
		EVENTUALLY ("eventually"),
		EXCEPT ("except"),
		EXCEPT_UPDATE ("except_update"),
		EXCEPT_UPDATE_FN_APPL ("except_update_fn_appl"),
		EXCEPT_UPDATE_RECORD_FIELD ("except_update_record_field"),
		EXCEPT_UPDATE_SPECIFIER ("except_update_specifier"),
		EXCL ("excl"),
		EXISTS ("exists"),
		EXTENDS ("extends"),
		FAIR ("fair"),
		FAIRNESS ("fairness"),
		FINITE_SET_LITERAL ("finite_set_literal"),
		FORALL ("forall"),
		FUNCTION_DEFINITION ("function_definition"),
		FUNCTION_EVALUATION ("function_evaluation"),
		FUNCTION_LITERAL ("function_literal"),
		GEQ ("geq"),
		GETS ("gets"),
		GG ("gg"),
		HAVE_PROOF_STEP ("have_proof_step"),
		HEADER_LINE ("header_line"),
		HEX_NUMBER ("hex_number"),
		IF_THEN_ELSE ("if_then_else"),
		IFF ("iff"),
		IMPLIES ("implies"),
		IN ("in"),
		INFIX_OP_SYMBOL ("infix_op_symbol"),
		INNER_ASSUME_PROVE ("inner_assume_prove"),
		INSTANCE ("instance"),
		INT_NUMBER_SET ("int_number_set"),
		LABEL ("label"),
		LABEL_AS ("label_as"),
		LAMBDA ("lambda"),
		LAND ("land"),
		LANGLE_BRACKET ("langle_bracket"),
		LD_TTILE ("ld_ttile"),
		LEADS_TO ("leads_to"),
		LEQ ("leq"),
		LET_IN ("let_in"),
		LEVEL ("level"),
		LL ("ll"),
		LNOT ("lnot"),
		LOCAL_DEFINITION ("local_definition"),
		LOR ("lor"),
		LS_TTILE ("ls_ttile"),
		LT ("lt"),
		MAPS_TO ("maps_to"),
		MINUS ("minus"),
		MODULE ("module"),
		MODULE_DEFINITION ("module_definition"),
		MODULE_REF ("module_ref"),
		NAT_NUMBER ("nat_number"),
		NAT_NUMBER_SET ("nat_number_set"),
		NEGATIVE ("negative"),
		NEQ ("neq"),
		NEW ("new"),
		NON_TERMINAL_PROOF ("non_terminal_proof"),
		NOTIN ("notin"),
		OCTAL_NUMBER ("octal_number"),
		ODOT ("odot"),
		OMINUS ("ominus"),
		OPERATOR_ARGS ("operator_args"),
		OPERATOR_DECLARATION ("operator_declaration"),
		OPERATOR_DEFINITION ("operator_definition"),
		OPLUS ("oplus"),
		OSLASH ("oslash"),
		OTHER_ARM ("other_arm"),
		OTIMES ("otimes"),
		PARENTHESES ("parentheses"),
		PCAL_ALGORITHM ("pcal_algorithm"),
		PCAL_ALGORITHM_BODY ("pcal_algorithm_body"),
		PCAL_ALGORITHM_START ("pcal_algorithm_start"),
		PCAL_ASSERT ("pcal_assert"),
		PCAL_ASSIGN ("pcal_assign"),
		PCAL_AWAIT ("pcal_await"),
		PCAL_DEFINITIONS ("pcal_definitions"),
		PCAL_EITHER ("pcal_either"),
		PCAL_GOTO ("pcal_goto"),
		PCAL_IF ("pcal_if"),
		PCAL_LHS ("pcal_lhs"),
		PCAL_MACRO ("pcal_macro"),
		PCAL_MACRO_CALL ("pcal_macro_call"),
		PCAL_MACRO_DECL ("pcal_macro_decl"),
		PCAL_PRINT ("pcal_print"),
		PCAL_PROC_CALL ("pcal_proc_call"),
		PCAL_PROC_DECL ("pcal_proc_decl"),
		PCAL_PROC_VAR_DECL ("pcal_proc_var_decl"),
		PCAL_PROC_VAR_DECLS ("pcal_proc_var_decls"),
		PCAL_PROCEDURE ("pcal_procedure"),
		PCAL_PROCESS ("pcal_process"),
		PCAL_RETURN ("pcal_return"),
		PCAL_SKIP ("pcal_skip"),
		PCAL_VAR_DECL ("pcal_var_decl"),
		PCAL_VAR_DECLS ("pcal_var_decls"),
		PCAL_WHILE ("pcal_while"),
		PCAL_WITH ("pcal_with"),
		PICK_PROOF_STEP ("pick_proof_step"),
		PLUS ("plus"),
		PLUS_ARROW ("plus_arrow"),
		POSTFIX_OP_SYMBOL ("postfix_op_symbol"),
		POWERSET ("powerset"),
		PREC ("prec"),
		PRECEQ ("preceq"),
		PREFIX_OP_SYMBOL ("prefix_op_symbol"),
		PREFIXED_OP ("prefixed_op"),
		PREV_FUNC_VAL ("prev_func_val"),
		PROOF_STEP ("proof_step"),
		PROOF_STEP_ID ("proof_step_id"),
		PROOF_STEP_REF ("proof_step_ref"),
		PROPTO ("propto"),
		QED_STEP ("qed_step"),
		QQ ("qq"),
		QUANTIFIER_BOUND ("quantifier_bound"),
		RANGLE_BRACKET ("rangle_bracket"),
		RANGLE_BRACKET_SUB ("rangle_bracket_sub"),
		RD_TTILE ("rd_ttile"),
		REAL_NUMBER_SET ("real_number_set"),
		RECORD_LITERAL ("record_literal"),
		RECORD_VALUE ("record_value"),
		RECURSIVE_DECLARATION ("recursive_declaration"),
		RS_TTILE ("rs_ttile"),
		SET_FILTER ("set_filter"),
		SET_IN ("set_in"),
		SET_MAP ("set_map"),
		SET_OF_FUNCTIONS ("set_of_functions"),
		SET_OF_RECORDS ("set_of_records"),
		SIM ("sim"),
		SIMEQ ("simeq"),
		SINGLE_LINE ("single_line"),
		SOURCE_FILE ("source_file"),
		SQCAP ("sqcap"),
		SQCUP ("sqcup"),
		SQSUBSET ("sqsubset"),
		SQSUBSETEQ ("sqsubseteq"),
		SQSUPSET ("sqsupset"),
		SQSUPSETEQ ("sqsupseteq"),
		STAR ("star"),
		STEP_EXPR_NO_STUTTER ("step_expr_no_stutter"),
		STEP_EXPR_OR_STUTTER ("step_expr_or_stutter"),
		STRING ("string"),
		SUBEXPR_COMPONENT ("subexpr_component"),
		SUBEXPR_PREFIX ("subexpr_prefix"),
		SUBEXPR_TREE_NAV ("subexpr_tree_nav"),
		SUBEXPRESSION ("subexpression"),
		SUBSET ("subset"),
		SUBSETEQ ("subseteq"),
		SUBSTITUTION ("substitution"),
		SUCC ("succ"),
		SUCCEQ ("succeq"),
		SUFFICES_PROOF_STEP ("suffices_proof_step"),
		SUP_PLUS ("sup_plus"),
		SUPSET ("supset"),
		SUPSETEQ ("supseteq"),
		TAKE_PROOF_STEP ("take_proof_step"),
		TEMPORAL_EXISTS ("temporal_exists"),
		TEMPORAL_FORALL ("temporal_forall"),
		TERMINAL_PROOF ("terminal_proof"),
		THEOREM ("theorem"),
		TIMES ("times"),
		TUPLE_LITERAL ("tuple_literal"),
		TUPLE_OF_IDENTIFIERS ("tuple_of_identifiers"),
		UNBOUNDED_QUANTIFICATION ("unbounded_quantification"),
		UNCHANGED ("unchanged"),
		UNION ("union"),
		UPLUS ("uplus"),
		USE_BODY ("use_body"),
		USE_BODY_DEF ("use_body_def"),
		USE_BODY_EXPR ("use_body_expr"),
		USE_OR_HIDE ("use_or_hide"),
		VARIABLE_DECLARATION ("variable_declaration"),
		VERTVERT ("vertvert"),
		WITNESS_PROOF_STEP ("witness_proof_step"),
		WR ("wr"),
		AMP ("amp"),
		AMPAMP ("ampamp"),
		ASTERISK ("asterisk"),
		BOOLEAN_SET ("boolean_set"),
		COMMENT ("comment"),
		COMPOSE ("compose"),
		DOL ("dol"),
		DOLDOL ("doldol"),
		EXTRAMODULAR_TEXT ("extramodular_text"),
		FORMAT ("format"),
		GT ("gt"),
		HASHHASH ("hashhash"),
		IDENTIFIER ("identifier"),
		IDENTIFIER_REF ("identifier_ref"),
		MAP_FROM ("map_from"),
		MAP_TO ("map_to"),
		MINUSMINUS ("minusminus"),
		MOD ("mod"),
		MODMOD ("modmod"),
		MUL ("mul"),
		MULMUL ("mulmul"),
		NAME ("name"),
		PCAL_END_EITHER ("pcal_end_either"),
		PCAL_END_IF ("pcal_end_if"),
		PCAL_END_WHILE ("pcal_end_while"),
		PCAL_END_WITH ("pcal_end_with"),
		PLACEHOLDER ("placeholder"),
		PLUSPLUS ("plusplus"),
		POW ("pow"),
		POWPOW ("powpow"),
		PRIME ("prime"),
		REAL_NUMBER ("real_number"),
		SETMINUS ("setminus"),
		SLASH ("slash"),
		SLASHSLASH ("slashslash"),
		STRING_SET ("string_set"),
		SUP_HASH ("sup_hash"),
		VALUE ("value"),
		VERT ("vert");

		/**
		 * The node kind name as found in the unparsed AST.
		 */
		public final String name;
		
		/**
		 * A static map from node kind name to enum to avoid linear lookups.
		 */
		private static final Map<String, AstNodeKind> nameMap = new HashMap<String, AstNodeKind>();
		
		/**
		 * Tracks node kinds that go unused; useful for identifying gaps in testing.
		 */
		private static final Set<AstNodeKind> unused = new HashSet<AstNodeKind>();
		
		/**
		 * Initialize the static maps on class load.
		 */
		static {
			for (AstNodeKind k : AstNodeKind.values()) {
				AstNodeKind.nameMap.put(k.name, k);
			}
			
			AstNodeKind.unused.addAll(AstNodeKind.nameMap.values());
		}
		
		/**
		 * Private constructor for the enum so it can have a string field.
		 * 
		 * @param name The node kind name as found in the unparsed AST.
		 */
		private AstNodeKind(String name) {
			this.name = name;
		}
		
		/**
		 * Get list of unused AST node kinds; useful for identifying gaps in testing.
		 * 
		 * @return The list of AST node kinds that were never constructed during parsing.
		 */
		public static List<AstNodeKind> getUnused() {
			return new ArrayList<AstNodeKind>(AstNodeKind.unused);
		}
		
		/**
		 * Gets the AST node kind enum from the unparsed AST string.
		 * 
		 * @param text The node kind name from the unparsed AST string.
		 * @return An enum corresponding to the given node kind name.
		 * @throws ParseException If no such node kind name is found.
		 */
		public static AstNodeKind fromString(String text) throws ParseException {
			if (AstNodeKind.nameMap.containsKey(text)) {
				AstNodeKind kind = AstNodeKind.nameMap.get(text);
				AstNodeKind.unused.remove(kind);
				return kind;
			} else {
				throw new ParseException(String.format("Could not find node %s", text), 0);
			}
		}
		
		/**
		 * Quickly creates an AST node of this kind.
		 * 
		 * @return An AST node of this kind.
		 */
		public AstNode asNode() {
			return new AstNode(this);
		}
	}
	
	/**
	 * An abstract syntax tree (AST) node defining a parse tree.
	 */
	public static class AstNode {
		/**
		 * The kind of the AST node.
		 */
		public final AstNodeKind kind;
		
		/**
		 * List of both named & unnamed children, in order of appearance.
		 */
		public final List<AstNode> children;
		
		/**
		 * List of named children in order of appearance.
		 */
		public final Map<String, AstNode> fields;
		
		/**
		 * Index to quickly check whether a child is named or not, and get its
		 * field name if so.
		 */
		private final Map<AstNode, String> fieldNames;

		/**
		 * Constructs an AST node.
		 * 
		 * @param kind The kind of the AST node.
		 * @param children The children of the AST node.
		 * @param fields The named field children of the AST node.
		 */
		public AstNode(AstNodeKind kind, List<AstNode> children, Map<String, AstNode> fields) {
			this.kind = kind;
			this.children = children;
			this.fields = fields;
			HashMap<AstNode, String> fieldNames = new HashMap<AstNode, String>();
			for (Map.Entry<String, AstNode> entry : this.fields.entrySet()) {
				fieldNames.put(entry.getValue(), entry.getKey());
			}
			this.fieldNames = fieldNames;
		}
		
		/**
		 * Constructs an AST node with no fields.
		 * 
		 * @param kind The kind of the AST node.
		 * @param children The children of the AST node.
		 */
		public AstNode(AstNodeKind kind, List<AstNode> children) {
			this(kind, children, new HashMap<String, AstNode>());
		}
		
		/**
		 * Constructs an AST node with no children or fields.
		 * 
		 * @param kind The kind of the AST node.
		 */
		public AstNode(AstNodeKind kind) {
			this(kind, new ArrayList<AstNode>());
		}
		
		/**
		 * Adds a child to this AST node.
		 * 
		 * @param child The child to add.
		 * @return This AST node for function chaining purposes.
		 */
		public AstNode addChild(AstNode child) {
			this.children.add(child);
			return this;
		}
		
		/**
		 * Adds multiple children to this AST node.
		 * 
		 * @param children The children to add.
		 * @return This AST node for function chaining purposes.
		 */
		public AstNode addChildren(List<AstNode> children) {
			this.children.addAll(children);
			return this;
		}
		
		/**
		 * Adds a field to this AST node.
		 * 
		 * @param name The name of the field to add.
		 * @param child The child to add for that field name.
		 * @return This AST node for function chaining purposes.
		 */
		public AstNode addField(String name, AstNode child) {
			this.children.add(child);
			this.fields.put(name, child);
			this.fieldNames.put(child, name);
			return this;
		}
		
		/**
		 * Builds a string representation of the subtree using a StringBuilder.
		 * 
		 * @param sb The StringBuilder onto which to append output.
		 */
		private void toString(StringBuilder sb) {
			sb.append('(');
			sb.append(this.kind.name);
			if (!this.children.isEmpty()) {
				sb.append(' ');
			}
			for (int i = 0; i < this.children.size(); i++) {
				AstNode child = this.children.get(i);
				if (this.fieldNames.containsKey(child)) {
					sb.append(this.fieldNames.get(child));
					sb.append(": ");
					child.toString(sb);
				} else {
					child.toString(sb);
				}
				if (i < this.children.size() - 1) {
					sb.append(' ');
				}
			}
			sb.append(')');
		}
		
		/**
		 * Dumps the AST node subtree to a string. Useful for debugging. The
		 * inverse of the parse function.
		 * 
		 * @return String representation of this AST subtree.
		 */
		public String toString() {
			StringBuilder sb = new StringBuilder();
			this.toString(sb);
			return sb.toString();
		}
		
		/**
		 * Test the subtree of the given AST node for equality with this one.
		 * 
		 * @param other The AST node to test for equality.
		 */
		public void testEquality(AstNode other) {
			Assert.assertEquals(this.kind, other.kind);
			Assert.assertEquals(this.children.size(), other.children.size());
			for (int i = 0; i < this.children.size(); i++) {
				AstNode thisChild = this.children.get(i);
				AstNode otherChild = other.children.get(i);
				if (this.fieldNames.containsKey(thisChild)) {
					Assert.assertEquals(this.fieldNames.get(thisChild), other.fieldNames.get(otherChild));
				}
				thisChild.testEquality(otherChild);
			}
		}
	}
	
	/**
	 * Mutable class tracking parser state to avoid string copies.
	 */
	private static class ParserState {
		/**
		 * The parser's current index in the string.
		 */
		public int i;
		
		/**
		 * The unparsed input string.
		 */
		public final String input;
		
		/**
		 * Whether to log each character consumed.
		 */
		private final boolean log;
		
		/**
		 * Initializes the parser state with the input string.
		 * 
		 * @param input The string to parse.
		 * @param log Whether to log each consumed char.
		 */
		public ParserState(String input, boolean log) {
			this.i = 0;
			this.input = input;
			this.log = log;
		}
		
		/**
		 * Whether the input has been fully consumed.
		 * 
		 * @return True if there is no input remaining.
		 */
		public boolean isEof() {
			return i >= input.length();
		}

		/**
		 * Consumes input until encountering a non-whitespace char.
		 */
		public void consumeWhitespace() {
			while (!this.isEof() && Character.isWhitespace(input.charAt(i))) {
				this.consume();
			}
		}
		
		/**
		 * Whether the current char is the given char.
		 * 
		 * @param c The char to check.
		 * @return True if not EOF and char matches.
		 */
		public boolean matches(char c) {
			return !this.isEof() && input.charAt(i) == c;
		}
		
		/**
		 * Consumes the current char without any checks. Possibly logs this act.
		 * 
		 * @return The consumed char.
		 */
		private char consume() {
			char c = input.charAt(i);
			if (this.log) {
				System.out.println(c);
			}
			i++;
			return c;
		}
		
		/**
		 * Consume the current char if it is as expected.
		 * 
		 * @param c The expected char.
		 * @return Whether the current char was consumed.
		 */
		public boolean consumeIf(char c) {
			if (this.matches(c)) {
				this.consume();
				return true;
			} else {
				return false;
			}
		}
		
		/**
		 * Whether the current char is an identifier char.
		 * 
		 * @return True if it is an identifier char.
		 */
		public boolean isIdentifierChar() {
			return !this.isEof() && (Character.isLetter(input.charAt(i)) || input.charAt(i) == '_');
		}
		
		/**
		 * Consumes the upcoming identifier then returns it as a string.
		 * 
		 * @return The consumed identifier.
		 */
		public String consumeIdentifier() {
			StringBuilder sb = new StringBuilder();
			while (this.isIdentifierChar()) {
				sb.append(this.consume());
			}
			
			return sb.toString();
		}
		
		/**
		 * Constructs an appropriate parse exception for the current position.
		 * 
		 * @param expected The char or element that was expected instead.
		 * @return A relatively informative parse exception to throw.
		 */
		public ParseException error(String expected) {
			if (this.isEof()) {
				return new ParseException(String.format("Unexpected EOF; expected %s: %s", expected, input), i);
			} else {
				return new ParseException(String.format("Unexpected char %c; expected %s at index %d: %s", input.charAt(i), expected, i, input), i);
			}
		}
	}
	
	/**
	 * Performs the actual parsing of the AST DSL by mutating a parser state
	 * in place. Thankfully S-expressions are easy to parse in a single
	 * recursive function.
	 * 
	 * @param s Parser state holding the input string and current index.
	 * @return Root node of the AST subtree at this point in the input.
	 * @throws ParseException If invalid S-expression syntax is encountered.
	 */
	private static AstNode parseAst(ParserState s) throws ParseException {
		s.consumeWhitespace();
		// Looking for ex. (source_file ...)
		if (s.consumeIf('(')) {
			s.consumeWhitespace();
			if (!s.isIdentifierChar()) {
				throw s.error("Identifier Char");
			}
			AstNodeKind kind = AstNodeKind.fromString(s.consumeIdentifier());
			List<AstNode> children = new ArrayList<AstNode>();
			Map<String, AstNode> fields = new HashMap<String, AstNode>();
			s.consumeWhitespace();
			while (!s.isEof() && !s.matches(')')) {
				if (s.matches('(')) {
					// Found unnamed child ex. (source_file (module ... ))
					children.add(parseAst(s));
				} else if (s.isIdentifierChar()) {
					// Found named field child ex. (bound_op name: (...) ...)
					String fieldName = s.consumeIdentifier();
					s.consumeWhitespace();
					if (s.consumeIf(':')) {
						s.consumeWhitespace();
						if (s.matches('(')) {
							// Recurse to get actual named child
							AstNode namedChild = parseAst(s);
							fields.put(fieldName, namedChild);
							children.add(namedChild);
						} else {
							throw s.error("(");
						}
					} else {
						throw s.error(":");
					}
				} else {
					throw s.error("(");
				}
				s.consumeWhitespace();
			}
			
			if (!s.consumeIf(')')) {
				throw s.error(")");
			}
			
			return new AstNode(kind, children, fields);
		} else {
			throw s.error("(");
		}
	}
	
	/**
	 * Parse the given S-expression string into an abstract syntax tree.
	 * 
	 * @param input The S-expression in string form.
	 * @return Root node of the AST.
	 * @throws ParseException If invalid S-expression syntax is encountered.
	 */
	public static AstNode parseAst(String input) throws ParseException {
		return parseAst(new ParserState(input, false));
	}
	
	public static void printSanyParseTree(TLAplusParser sanyTree) {
		PrintWriter out = new PrintWriter(System.out);
		SyntaxTreePrinter.print(sanyTree, out);
		out.flush();
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
					moduleRef = AstNodeKind.MODULE_REF.asNode();
					break;
				} case TLAplusParserConstants.IDENTIFIER: {
					if (null == moduleRef) {
						useBodyExpr.addChild(AstNodeKind.IDENTIFIER_REF.asNode());
					} else {
						moduleRef.addChild(AstNodeKind.IDENTIFIER_REF.asNode());
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
		AstNode useBody = AstNodeKind.USE_BODY.asNode();
		if (heirs[offset].isKind(TLAplusParserConstants.ONLY)) {
			offset++;
		}
		if (!heirs[offset].isKind(TLAplusParserConstants.DF)) {
			AstNode useBodyExpr = AstNodeKind.USE_BODY_EXPR.asNode();
			useBody.addChild(useBodyExpr);
			offset = parseUseBodyDefs(heirs, offset, useBodyExpr);
		}
		if (offset < heirs.length) { 
			Assert.assertEquals(TLAplusParserConstants.DF, heirs[offset].getKind());
			offset++;
			AstNode useBodyDef = AstNodeKind.USE_BODY_DEF.asNode();
			useBody.addChild(useBodyDef);
			offset = parseUseBodyDefs(heirs, offset, useBodyDef);
		}
		return useBody;
	}
	
	private static AstNode id(SyntaxTreeNode input) throws ParseException {
		Assert.assertEquals(TLAplusParserConstants.IDENTIFIER, input.getKind());
		switch (input.getImage()) {
			case "TRUE": return AstNodeKind.BOOLEAN.asNode();
			default: return AstNodeKind.IDENTIFIER_REF.asNode();
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
			case "SUBSET": return AstNodeKind.POWERSET.asNode();
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
			case "\\/": return AstNodeKind.LOR.asNode();
			case "+": return AstNodeKind.PLUS.asNode();
			case "-": return AstNodeKind.MINUS.asNode();
			case "*": return AstNodeKind.MUL.asNode();
			case "/": return AstNodeKind.SLASH.asNode();
			case "=": return AstNodeKind.EQ.asNode();
			case ">": return AstNodeKind.GT.asNode();
			case "=<": return AstNodeKind.LEQ.asNode();
			case "\\in": return AstNodeKind.IN.asNode();
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
		switch (node.getKind()) {
			case SyntaxTreeConstants.N_IdentLHS: { // f ==, f(a, b) ==, etc.
				Assert.assertTrue(heirs.length >= 1);
				Assert.assertEquals(TLAplusParserConstants.IDENTIFIER, heirs[0].getKind());
				parent.addField("name", AstNodeKind.IDENTIFIER.asNode());
				if (heirs.length > 1) {
					Assert.assertEquals(TLAplusParserConstants.LBR, heirs[1].getKind());
					parent.addChildren(commaSeparated(chop(heirs, 2)));
					Assert.assertEquals(TLAplusParserConstants.RBR, heirs[heirs.length-1].getKind());
				}
				return;
			} default: {
				throw new ParseException(String.format("Unhandled conversion from kind %d image %s", node.getKind(), node.getImage()), 0);
			}
		}
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
		switch (node.getKind()) {
			case SyntaxTreeConstants.N_Module: { // ---- MODULE Test ---- ... ====
				AstNode module = AstNodeKind.MODULE.asNode();
				Assert.assertEquals(4, heirs.length);
				Assert.assertEquals(SyntaxTreeConstants.N_BeginModule, heirs[0].getKind());
				SyntaxTreeNode header = heirs[0];
				SyntaxTreeNode[] headerHeirs = header.getHeirs();
				Assert.assertEquals(3, headerHeirs.length);
				int kind = headerHeirs[0].getKind();
				Assert.assertTrue(kind == TLAplusParserConstants._BM0 || kind == TLAplusParserConstants._BM1);
				module.addChild(AstNodeKind.HEADER_LINE.asNode());
				Assert.assertEquals(TLAplusParserConstants.IDENTIFIER, headerHeirs[1].getKind());
				module.addField("name", AstNodeKind.IDENTIFIER.asNode());
				Assert.assertEquals(TLAplusParserConstants.SEPARATOR, headerHeirs[2].getKind());
				module.addChild(AstNodeKind.HEADER_LINE.asNode());
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
				return AstNodeKind.DOUBLE_LINE.asNode();
			} case TLAplusParserConstants.SEPARATOR: { // ----
				return AstNodeKind.SINGLE_LINE.asNode();
			} case SyntaxTreeConstants.N_VariableDeclaration: { // VARIABLES x, y, z
				AstNode variables = AstNodeKind.VARIABLE_DECLARATION.asNode();
				Assert.assertTrue(heirs.length >= 2);
				Assert.assertEquals(TLAplusParserConstants.VARIABLE, heirs[0].getKind());
				for (int i = 1; i < heirs.length; i += 2) {
					Assert.assertEquals(TLAplusParserConstants.IDENTIFIER, heirs[i].getKind());
					variables.addChild(AstNodeKind.IDENTIFIER.asNode());
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
					AstNode localDefn = AstNodeKind.LOCAL_DEFINITION.asNode();
					Assert.assertEquals(TLAplusParserConstants.LOCAL, heirs[0].getKind());
					Assert.assertEquals(SyntaxTreeConstants.N_NonLocalInstance, heirs[1].getKind());
					localDefn.addChild(translate(heirs[1]));
					return localDefn;
				}
			} case SyntaxTreeConstants.N_NonLocalInstance: { // INSTANCE M WITH a <- b, c <- d
				AstNode instance = AstNodeKind.INSTANCE.asNode();
				Assert.assertTrue(heirs.length >= 2);
				Assert.assertEquals(TLAplusParserConstants.INSTANCE, heirs[0].getKind());
				Assert.assertEquals(TLAplusParserConstants.IDENTIFIER, heirs[1].getKind());
				instance.addChild(AstNodeKind.IDENTIFIER_REF.asNode());
				if (heirs.length > 2) {
					Assert.assertEquals(TLAplusParserConstants.WITH, heirs[2].getKind());
					instance.addChildren(commaSeparated(Arrays.copyOfRange(heirs, 3, heirs.length)));
				}
				return instance;
			} case SyntaxTreeConstants.N_ModuleDefinition: {
				AstNode moduleDefinition = AstNodeKind.MODULE_DEFINITION.asNode();
				Assert.assertEquals(3, heirs.length);
				Assert.assertEquals(SyntaxTreeConstants.N_IdentLHS, heirs[0].getKind());
				flatTranslate(moduleDefinition, heirs[0]);
				Assert.assertEquals(TLAplusParserConstants.DEF, heirs[1].getKind());
				moduleDefinition.addChild(AstNodeKind.DEF_EQ.asNode());
				Assert.assertEquals(SyntaxTreeConstants.N_NonLocalInstance, heirs[2].getKind());
				moduleDefinition.addChild(translate(heirs[2]));
				return moduleDefinition;
			} case SyntaxTreeConstants.N_Substitution: {
				AstNode substitution = AstNodeKind.SUBSTITUTION.asNode();
				Assert.assertEquals(3, heirs.length);
				// heirs[0] is some identifier or prefix/infix/postfix op
				substitution.addChild(translate(heirs[0]));
				Assert.assertEquals(TLAplusParserConstants.SUBSTITUTE, heirs[1].getKind());
				substitution.addChild(AstNodeKind.GETS.asNode());
				// heirs[2] is some operator or expression
				substitution.addChild(translate(heirs[2]));
				return substitution;
			} case SyntaxTreeConstants.N_OperatorDefinition: { // ex. op(a, b) == expr
				AstNode operatorDefinition = AstNodeKind.OPERATOR_DEFINITION.asNode();
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
					return AstNodeKind.IDENTIFIER.asNode();
				} else {
					Assert.assertTrue(heirs.length >= 4);
					AstNode opDeclaration = AstNodeKind.OPERATOR_DECLARATION.asNode();
					opDeclaration.addField("name", AstNodeKind.IDENTIFIER.asNode());
					Assert.assertEquals(TLAplusParserConstants.LBR, heirs[1].getKind());
					// TODO: test multiple placeholders
					opDeclaration.addChildren(commaSeparated(chop(heirs, 2)));
					Assert.assertEquals(TLAplusParserConstants.RBR, heirs[heirs.length-1].getKind());
					return opDeclaration;
				}
			} case SyntaxTreeConstants.N_Recursive: { // RECURSIVE F(_, _), G(_)
				AstNode recursiveDeclaration = AstNodeKind.RECURSIVE_DECLARATION.asNode();
				Assert.assertEquals(2, heirs.length);
				Assert.assertEquals(TLAplusParserConstants.RECURSIVE, heirs[0].getKind());
				Assert.assertEquals(SyntaxTreeConstants.N_IdentDecl, heirs[1].getKind());
				recursiveDeclaration.addChild(translate(heirs[1]));
				// TODO: test comma-separated recursive declarations
				return recursiveDeclaration;
			} case TLAplusParserConstants.US: {
				return AstNodeKind.PLACEHOLDER.asNode();
			} case TLAplusParserConstants.DEF: { // ==
				Assert.assertEquals(0, heirs.length);
				return AstNodeKind.DEF_EQ.asNode();
			} case SyntaxTreeConstants.N_ConjList: { // Multi-line aligned conjunction list
				AstNode conjList = AstNodeKind.CONJ_LIST.asNode();
				for (SyntaxTreeNode heir : heirs) {
					Assert.assertEquals(SyntaxTreeConstants.N_ConjItem, heir.getKind());
					conjList.addChild(translate(heir));
				}
				return conjList;
			} case SyntaxTreeConstants.N_ConjItem: { // /\ expr
				AstNode conjItem = AstNodeKind.CONJ_ITEM.asNode();
				Assert.assertEquals(2, heirs.length);
				Assert.assertEquals(TLAplusParserConstants.AND, heirs[0].getKind());
				conjItem.addChild(AstNodeKind.BULLET_CONJ.asNode());
				// heirs[1] is of indeterminate expression type
				conjItem.addChild(translate(heirs[1]));
				return conjItem;
			} case SyntaxTreeConstants.N_DisjList: { // Multi-line aligned disjunction list
				AstNode disjList = AstNodeKind.DISJ_LIST.asNode();
				for (SyntaxTreeNode heir : heirs) {
					Assert.assertEquals(SyntaxTreeConstants.N_DisjItem, heir.getKind());
					disjList.addChild(translate(heir));
				}
				return disjList;
			} case SyntaxTreeConstants.N_DisjItem: { // \/ expr
				AstNode disjItem = AstNodeKind.DISJ_ITEM.asNode();
				Assert.assertEquals(2, heirs.length);
				Assert.assertEquals(TLAplusParserConstants.OR, heirs[0].getKind());
				disjItem.addChild(AstNodeKind.BULLET_DISJ.asNode());
				// heirs[1] is of indeterminate expression type
				disjItem.addChild(translate(heirs[1]));
				return disjItem;
			} case SyntaxTreeConstants.N_GeneralId: { // foo!bar!baz!x
				Assert.assertEquals(2, heirs.length);
				// TODO: handle ID prefix
				Assert.assertEquals(SyntaxTreeConstants.N_IdPrefix, heirs[0].getKind());
				switch (heirs[1].getKind()) {
					case TLAplusParserConstants.IDENTIFIER: {
						return translate(heirs[1]);
					} case SyntaxTreeConstants.N_InfixOp: {
						AstNode infixOpSymbol = AstNodeKind.INFIX_OP_SYMBOL.asNode();
						infixOpSymbol.addChild(translate(heirs[1]));
						return infixOpSymbol;
					} default: {
						Assert.fail();
					}
				}
				if (!heirs[1].isKind(TLAplusParserConstants.IDENTIFIER)) {
					return null;
				}
				Assert.assertEquals(TLAplusParserConstants.IDENTIFIER, heirs[1].getKind());
				return translate(heirs[1]);
			} case TLAplusParserConstants.IDENTIFIER: { // ex. x
				Assert.assertEquals(0, heirs.length);
				return id(node);
			} case SyntaxTreeConstants.N_Number: { // 1, 3, 100, etc.
				Assert.assertEquals(1, heirs.length);
				Assert.assertEquals(TLAplusParserConstants.NUMBER_LITERAL, heirs[0].getKind());
				String image = heirs[0].image.toString();
				if (image.matches("\\d+")) {
					return AstNodeKind.NAT_NUMBER.asNode();
				} else if (image.matches("\\\\[bB][0|1]+")) {
					return AstNodeKind.BINARY_NUMBER.asNode()
							.addChild(AstNodeKind.FORMAT.asNode())
							.addChild(AstNodeKind.VALUE.asNode());
				} else if (image.matches("\\\\[oO][0-7]+")) {
					return AstNodeKind.OCTAL_NUMBER.asNode()
							.addChild(AstNodeKind.FORMAT.asNode())
							.addChild(AstNodeKind.VALUE.asNode());
				} else if (image.matches("\\\\[hH][0-9a-fA-F]+")) {
					return AstNodeKind.HEX_NUMBER.asNode()
							.addChild(AstNodeKind.FORMAT.asNode())
							.addChild(AstNodeKind.VALUE.asNode());
				} else {
					throw new ParseException(String.format("Invalid number literal format %s", image), 0);
				}
			} case SyntaxTreeConstants.N_Real: { // 2.178, 3.14, etc.
				Assert.assertEquals(3, heirs.length);
				Assert.assertEquals(TLAplusParserConstants.NUMBER_LITERAL, heirs[0].getKind());
				Assert.assertEquals(TLAplusParserConstants.DOT, heirs[1].getKind());
				Assert.assertEquals(TLAplusParserConstants.NUMBER_LITERAL, heirs[2].getKind());
				return AstNodeKind.REAL_NUMBER.asNode();
			} case SyntaxTreeConstants.N_String: { // ex. "foobar"
				AstNode string = AstNodeKind.STRING.asNode();
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
						string.addChild(AstNodeKind.ESCAPE_CHAR.asNode());
					}
				}
				return string;
			} case SyntaxTreeConstants.N_Tuple: { // ex. <<1, 2, 3>>
				AstNode tuple = AstNodeKind.TUPLE_LITERAL.asNode();
				Assert.assertTrue(heirs.length >= 2);
				Assert.assertEquals(TLAplusParserConstants.LAB, heirs[0].getKind());
				tuple.addChild(translate(heirs[0]));
				tuple.addChildren(commaSeparated(chop(heirs)));
				Assert.assertEquals(TLAplusParserConstants.RAB, heirs[heirs.length-1].getKind());
				tuple.addChild(translate(heirs[heirs.length-1]));
				return tuple;
			} case TLAplusParserConstants.LAB: { // <<
				Assert.assertEquals(0, heirs.length);
				return AstNodeKind.LANGLE_BRACKET.asNode();
			} case TLAplusParserConstants.RAB: { // >>
				Assert.assertEquals(0, heirs.length);
				return AstNodeKind.RANGLE_BRACKET.asNode();
			} case SyntaxTreeConstants.N_SetEnumerate: { // {1, 3, 5}
				AstNode setLiteral = AstNodeKind.FINITE_SET_LITERAL.asNode();
				Assert.assertTrue(heirs.length >= 2);
				Assert.assertEquals(TLAplusParserConstants.LBC, heirs[0].getKind());
				setLiteral.addChildren(commaSeparated(chop(heirs)));
				Assert.assertEquals(TLAplusParserConstants.RBC, heirs[heirs.length-1].getKind());
				return setLiteral;
			} case SyntaxTreeConstants.N_SubsetOf: { // {x \in S : P(x)}
				AstNode setFilter = AstNodeKind.SET_FILTER.asNode();
				Assert.assertEquals(7, heirs.length);
				Assert.assertEquals(TLAplusParserConstants.LBC, heirs[0].getKind());
				AstNode quantifierBound = AstNodeKind.QUANTIFIER_BOUND.asNode();
				setFilter.addField("generator", quantifierBound);
				Assert.assertEquals(TLAplusParserConstants.IDENTIFIER, heirs[1].getKind());
				quantifierBound.addChild(AstNodeKind.IDENTIFIER.asNode());
				Assert.assertEquals(SyntaxTreeConstants.T_IN, heirs[2].getKind());
				quantifierBound.addChild(AstNodeKind.SET_IN.asNode());
				quantifierBound.addField("set", translate(heirs[3]));
				Assert.assertEquals(TLAplusParserConstants.COLON, heirs[4].getKind());
				// heirs[5] is of indeterminate expression type
				setFilter.addField("filter", translate(heirs[5]));
				Assert.assertEquals(TLAplusParserConstants.RBC, heirs[heirs.length-1].getKind());
				return setFilter;
			} case SyntaxTreeConstants.N_SetOfFcns: {
				AstNode setOfFunctions = AstNodeKind.SET_OF_FUNCTIONS.asNode();
				Assert.assertEquals(5, heirs.length);
				Assert.assertEquals(TLAplusParserConstants.LSB, heirs[0].getKind());
				// heirs[1] is of indeterminate expression type
				setOfFunctions.addChild(translate(heirs[1]));
				Assert.assertEquals(TLAplusParserConstants.ARROW, heirs[2].getKind());
				setOfFunctions.addChild(AstNodeKind.MAPS_TO.asNode());
				// heirs[3] is of indeterminate expression type
				setOfFunctions.addChild(translate(heirs[3]));
				Assert.assertEquals(TLAplusParserConstants.RSB, heirs[4].getKind());
				return setOfFunctions;
			} case SyntaxTreeConstants.N_IfThenElse: { // IF x THEN y ELSE z
				AstNode ite = AstNodeKind.IF_THEN_ELSE.asNode();
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
				AstNode cases = AstNodeKind.CASE.asNode();
				Assert.assertTrue(heirs.length >= 2);
				Assert.assertEquals(TLAplusParserConstants.CASE, heirs[0].getKind());
				Assert.assertEquals(SyntaxTreeConstants.N_CaseArm, heirs[1].getKind());
				cases.addChild(translate(heirs[1]));
				int offset = 2;
				while (offset < heirs.length) {
					Assert.assertEquals(TLAplusParserConstants.CASESEP, heirs[offset].getKind());
					cases.addChild(AstNodeKind.CASE_BOX.asNode());
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
			} case SyntaxTreeConstants.N_CaseArm: {
				AstNode caseArm = AstNodeKind.CASE_ARM.asNode();
				Assert.assertEquals(3, heirs.length);
				// heirs[0] is of indeterminate expression type
				caseArm.addChild(translate(heirs[0]));
				Assert.assertEquals(TLAplusParserConstants.ARROW, heirs[1].getKind());
				caseArm.addChild(AstNodeKind.CASE_ARROW.asNode());
				// heirs[2] is of indeterminate expression type
				caseArm.addChild(translate(heirs[2]));
				return caseArm;
			} case SyntaxTreeConstants.N_OtherArm: {
				AstNode otherArm = AstNodeKind.OTHER_ARM.asNode();
				Assert.assertEquals(3, heirs.length);
				Assert.assertEquals(TLAplusParserConstants.OTHER, heirs[0].getKind());
				Assert.assertEquals(TLAplusParserConstants.ARROW, heirs[1].getKind());
				otherArm.addChild(AstNodeKind.CASE_ARROW.asNode());
				// heirs[2] is of indeterminate expression type
				otherArm.addChild(translate(heirs[2]));
				return otherArm;
			} case SyntaxTreeConstants.N_ActionExpr: { // [expr]_subexpr or <<expr>>_subexpr
				boolean allowStutter = heirs[0].isKind(TLAplusParserConstants.LSB);
				AstNode actionExpr = allowStutter ? AstNodeKind.STEP_EXPR_OR_STUTTER.asNode() : AstNodeKind.STEP_EXPR_NO_STUTTER.asNode();
				Assert.assertEquals(allowStutter ? TLAplusParserConstants.LSB : TLAplusParserConstants.LAB, heirs[0].getKind());
				if (!allowStutter) {
					actionExpr.addChild(AstNodeKind.LANGLE_BRACKET.asNode());
				}
				// heirs[1] is of indeterminate expression type
				actionExpr.addChild(translate(heirs[1]));
				Assert.assertEquals(allowStutter ? TLAplusParserConstants.ARSB : TLAplusParserConstants.ARAB, heirs[2].getKind());
				if (!allowStutter) {
					actionExpr.addChild(AstNodeKind.RANGLE_BRACKET_SUB.asNode());
				}
				// heirs[3] is of indeterminate subscript expression type
				actionExpr.addChild(translate(heirs[3]));
				return actionExpr;
			} case SyntaxTreeConstants.N_FairnessExpr: {
				AstNode fairness = AstNodeKind.FAIRNESS.asNode();
				Assert.assertEquals(5, heirs.length);
				Assert.assertTrue(heirs[0].isKind(TLAplusParserConstants.WF) || heirs[0].isKind(TLAplusParserConstants.SF));
				// heirs[1] is of indeterminate subscript expression type
				fairness.addChild(translate(heirs[1]));
				Assert.assertEquals(TLAplusParserConstants.LBR, heirs[2].getKind());
				// heirs[3] is of indeterminate expression type
				fairness.addChild(translate(heirs[3]));
				Assert.assertEquals(TLAplusParserConstants.RBR, heirs[4].getKind());
				return fairness;
			} case SyntaxTreeConstants.N_LetIn: {
				AstNode letIn = AstNodeKind.LET_IN.asNode();
				Assert.assertEquals(4, heirs.length);
				Assert.assertEquals(TLAplusParserConstants.LET, heirs[0].getKind());
				Assert.assertEquals(SyntaxTreeConstants.N_LetDefinitions, heirs[1].getKind());
				letIn.addChildren(repeat(heirs[1]));
				Assert.assertEquals(TLAplusParserConstants.LETIN, heirs[2].getKind());
				// heirs[3] is of indeterminate expression type
				letIn.addField("expression", translate(heirs[3]));
				return letIn;
			} case SyntaxTreeConstants.N_ParenExpr: {
				AstNode paren = AstNodeKind.PARENTHESES.asNode();
				Assert.assertEquals(3, heirs.length);
				Assert.assertEquals(TLAplusParserConstants.LBR, heirs[0].getKind());
				// heirs[1] is of indeterminate expression type
				paren.addChild(translate(heirs[1]));
				Assert.assertEquals(TLAplusParserConstants.RBR, heirs[2].getKind());
				return paren;
			} case SyntaxTreeConstants.N_OpApplication: { // ex. f(a, b, c)
				AstNode boundOp = AstNodeKind.BOUND_OP.asNode();
				Assert.assertEquals(2, heirs.length);
				Assert.assertEquals(SyntaxTreeConstants.N_GeneralId, heirs[0].getKind());
				boundOp.addField("name", translate(heirs[0]));
				Assert.assertEquals(SyntaxTreeConstants.N_OpArgs, heirs[1].getKind());
				SyntaxTreeNode parameters = heirs[1];
				SyntaxTreeNode[] parameterHeirs = parameters.getHeirs();
				Assert.assertTrue(parameterHeirs.length >= 3);
				Assert.assertEquals(TLAplusParserConstants.LBR, parameterHeirs[0].getKind());
				boundOp.addChildren(commaSeparated(chop(parameterHeirs)));
				Assert.assertEquals(TLAplusParserConstants.RBR, parameterHeirs[parameterHeirs.length-1].getKind());
				return boundOp;
			} case SyntaxTreeConstants.N_FcnAppl: {
				AstNode functionEvaluation = AstNodeKind.FUNCTION_EVALUATION.asNode();
				Assert.assertTrue(heirs.length >= 4);
				// heirs[0] is of indeterminate expression type
				functionEvaluation.addChild(translate(heirs[0]));
				Assert.assertEquals(TLAplusParserConstants.LSB, heirs[1].getKind());
				functionEvaluation.addChildren(commaSeparated(Arrays.copyOfRange(heirs, 2, heirs.length-1)));
				Assert.assertEquals(TLAplusParserConstants.RSB, heirs[heirs.length-1].getKind());
				return functionEvaluation;
			} case SyntaxTreeConstants.N_PrefixExpr: { // ex. SUBSET P
				AstNode boundPrefixOp = AstNodeKind.BOUND_PREFIX_OP.asNode();
				Assert.assertEquals(2, heirs.length);
				Assert.assertEquals(SyntaxTreeConstants.N_GenPrefixOp, heirs[0].getKind());
				boundPrefixOp.addField("symbol", translate(heirs[0]));
				// heirs[1] is of indeterminate expression type
				boundPrefixOp.addField("rhs", translate(heirs[1]));
				return boundPrefixOp;
			} case SyntaxTreeConstants.N_InfixExpr: { // ex. a + b
				AstNode boundInfixOp = AstNodeKind.BOUND_INFIX_OP.asNode();
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
				AstNode assumption = AstNodeKind.ASSUMPTION.asNode();
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
				AstNode theorem = AstNodeKind.THEOREM.asNode();
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
					theorem.addField("name", AstNodeKind.IDENTIFIER.asNode());
					Assert.assertEquals(TLAplusParserConstants.DEF, heirs[2].getKind());
					theorem.addChild(AstNodeKind.DEF_EQ.asNode());
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
				AstNode proof = AstNodeKind.TERMINAL_PROOF.asNode();
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
			} default: {
				throw new ParseException(String.format("Unhandled conversion from kind %d image %s", node.getKind(), node.getImage()), 0);
			}
		}
	}
	
	public static AstNode sanyTreeToDslTree(TLAplusParser sany) throws ParseException {
		AstNode sourceFile = AstNodeKind.SOURCE_FILE.asNode();
		sourceFile.addChild(translate(sany.ParseTree));
		return sourceFile;
	}
	
	/**
	 * Whether the expected AST matches the actual AST from SANY.
	 * 
	 * @param expected The expected AST.
	 * @param actual The actual AST generated by SANY.
	 * @return True if match was successful.
	 */
	public static boolean matchesExpectedAst(AstNode expected, TLAplusParser sanyActual) throws ParseException {
		System.out.println("expected:");
		System.out.println(expected.toString());
		System.out.println("actual:");
		AstNode actual = sanyTreeToDslTree(sanyActual);
		System.out.println(actual.toString());
		expected.testEquality(actual);
		return true;
	}
}
