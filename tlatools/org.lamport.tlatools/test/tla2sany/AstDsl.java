package tla2sany;

import tla2sany.st.TreeNode;

import java.lang.Character;
import java.text.ParseException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class AstDsl {	
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

		private final String name;
		
		private static Map<String, AstNodeKind> nameMap = new HashMap<String, AstNodeKind>();
		
		static {
			for (AstNodeKind k : AstNodeKind.values()) {
				AstNodeKind.nameMap.put(k.name, k);
			}
		}
		
		private AstNodeKind(String name) {
			this.name = name;
		}
		
		public static AstNodeKind fromString(String text) throws ParseException {
			if (AstNodeKind.nameMap.containsKey(text)) {
				return AstNodeKind.nameMap.get(text);
			} else {
				throw new ParseException(String.format("Could not find node %s", text), 0);
			}
		}
	}
	
	public static class AstNode {
		public final AstNodeKind kind;
		public final List<AstNode> children;
		public final Map<String, AstNode> fields;
		private final Map<AstNode, String> fieldNames;
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
		
		private void toString(StringBuilder sb) {
			sb.append('(');
			sb.append(this.kind.name);
			if (!this.children.isEmpty()) {
				sb.append(' ');
			}
			for (AstNode child : this.children) {
				if (this.fieldNames.containsKey(child)) {
					sb.append(this.fieldNames.get(child));
					sb.append(": ");
					child.toString(sb);
				} else {
					child.toString(sb);
				}
				sb.append(' ');
			}
			sb.append(')');
		}
		
		public String toString() {
			StringBuilder sb = new StringBuilder();
			this.toString(sb);
			return sb.toString();
		}
	}
	
	private static void treeNodeToString(TreeNode node, StringBuilder sb) {
		sb.append('(');
		sb.append(node.getImage());
		if (node.heirs().length != 0) {
			sb.append(' ');
		}
		for (TreeNode child : node.heirs()) {
			treeNodeToString(child, sb);
			sb.append(' ');
		}
		sb.append(')');
	}
	
	public static String treeNodeToString(TreeNode node) {
		StringBuilder sb = new StringBuilder();
		treeNodeToString(node, sb);
		return sb.toString();
	}
	
	private static class ParserState {
		public int i;
		public final String input;
		private final boolean log;
		public ParserState(String input, boolean log) {
			this.i = 0;
			this.input = input;
			this.log = log;
		}
		
		public boolean isEof() {
			return i >= input.length();
		}

		public void consumeWhitespace() {
			while (!this.isEof() && Character.isWhitespace(input.charAt(i))) {
				this.consume();
			}
		}
		
		public boolean matches(char c) {
			return !this.isEof() && input.charAt(i) == c;
		}
		
		public char consume() {
			char c = input.charAt(i);
			if (this.log) {
				System.out.println(c);
			}
			i++;
			return c;
		}
		
		public boolean consumeIf(char c) {
			if (this.matches(c)) {
				this.consume();
				return true;
			} else {
				return false;
			}
		}
		
		public boolean isIdentifierChar() {
			return !this.isEof() && (Character.isLetter(input.charAt(i)) || input.charAt(i) == '_');
		}
		
		public ParseException error(char expected) {
			if (this.isEof()) {
				return new ParseException(String.format("Unexpected EOF; expected %c: %s", expected, input), i);
			} else {
				return new ParseException(String.format("Unexpected char %c; expected %c: %s", input.charAt(i), expected, input), i);
			}
		}
	}
	
	private static AstNode parseAst(ParserState s) throws ParseException {
		s.consumeWhitespace();
		if (s.consumeIf('(')) {
			s.consumeWhitespace();
			StringBuilder nameBuilder = new StringBuilder();
			while (s.isIdentifierChar()) {
				nameBuilder.append(s.consume());
			}

			ArrayList<AstNode> children = new ArrayList<AstNode>();
			HashMap<String, AstNode> fields = new HashMap<String, AstNode>();
			s.consumeWhitespace();
			while (!s.matches(')')) {
				if (s.matches('(')) {
					children.add(parseAst(s));
				} else if (s.isIdentifierChar()) {
					StringBuilder fieldNameBuilder = new StringBuilder();
					while (s.isIdentifierChar()) {
						fieldNameBuilder.append(s.consume());
					}
					s.consumeWhitespace();
					if (s.consumeIf(':')) {
						s.consumeWhitespace();
						if (s.matches('(')) {
							AstNode namedChild = parseAst(s);
							fields.put(fieldNameBuilder.toString(), namedChild);
							children.add(namedChild);
						} else {
							throw s.error('(');
						}
					} else {
						throw s.error(':');
					}
				} else {
					throw s.error('(');
				}
				s.consumeWhitespace();
			}
			
			s.consumeIf(')');
			
			return new AstNode(AstNodeKind.fromString(nameBuilder.toString()), children, fields);
		} else {
			throw s.error('(');
		}
	}
	
	public static AstNode parseAst(String input) throws ParseException {
		return parseAst(new ParserState(input, false));
	}
	
	public static boolean matchesExpectedAst(AstNode expected, TreeNode actual) {
		System.out.println(expected.toString());
		System.out.println(treeNodeToString(actual));
		return true;
	}
}
