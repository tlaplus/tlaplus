package formatter.constructs;

/**
 * Enum representing SANY node kinds with metadata.
 */
@SuppressWarnings("unused")
public enum NodeKind {

    NULL_ID(327, "Null ID"),

    // Module structure
    MODULE(382, "Module declaration"),
    BEGIN_MODULE(333, "Module header"),
    END_MODULE(345, "Module footer"),
    BODY(334, "Module body"),
    MODULE_DEFINITION(383, "Module definition"),

    // Declarations
    EXTENDS(350, "Extends declaration"),
    ACT_DECL(328, "Action declaration"),
    ASSUME_DECL(330, "Assume declaration"),
    CONSTANTS(342, "Constants keyword"),
    VARIABLE_DECLARATION(426, "Variable declaration"),
    OPERATOR_DEFINITION(389, "Operator definition"),
    THEOREM(422, "Theorem declaration"),
    PARAM_DECL(391, "Parameter declaration"),
    PARAM_DECLARATION(392, "Parameter(==Constants) declaration"),
    IDENT_DECL(363, "Identifier declaration"),
    INFIX_DECL(370, "Infix declaration"),
    POSTFIX_DECL(394, "Postfix declaration"),
    PREFIX_DECL(398, "Prefix declaration"),
    TEMP_DECL(421, "Temporal declaration"),
    FUNCTION_DEFINITION(356, "Function definition"),
    FUNCTION_PARAM(357, "Function parameter"),

    // Expressions
    ACTION_EXPR(329, "Action expression"),
    ASSUME_PROVE(331, "Assume prove"),
    ASSUMPTION(332, "Assumption"),
    CASE(336, "Case expression"),
    CASE_ARM(337, "Case arm"),
    CONJ_ITEM(340, "Conjunction item"),
    CONJ_LIST(341, "Conjunction list"),
    DISJ_ITEM(343, "Disjunction item"),
    DISJ_LIST(344, "Disjunction list"),
    EXCEPT(346, "Except expression"),
    EXCEPT_COMPONENT(347, "Except component"),
    EXCEPT_SPEC(348, "Except specification"),
    TIMES(349, "Times expression"),
    FAIRNESS_EXPR(351, "Fairness expression"),
    FCN_APPL(352, "Function application"),
    FCN_CONST(353, "Function constant"),
    FIELD_SET(354, "Field set"),
    FIELD_VAL(355, "Field value"),
    GENERAL_ID(358, "General identifier"),
    GEN_INFIX_OP(359, "Generic infix operator"),
    GEN_NON_EXP_PREFIX_OP(360, "Generic non-expression prefix operator"),
    GEN_POSTFIX_OP(361, "Generic postfix operator"),
    GEN_PREFIX_OP(362, "Generic prefix operator"),
    REAL(364, "Real number"),
    IDENTIFIER_TUPLE(365, "Identifier tuple"),
    IDENT_LHS(366, "Identifier left-hand side"),
    ID_PREFIX(367, "Identifier prefix"),
    ID_PREFIX_ELEMENT(368, "Identifier prefix element"),
    IF_THEN_ELSE(369, "IF-THEN-ELSE expression"),
    INFIX_EXPR(371, "Infix expression"),
    INFIX_LHS(372, "Infix left-hand side"),
    INFIX_OP(373, "Infix operator"),
    INNER_PROOF(374, "Inner proof"),
    INSTANCE(375, "Instance"),
    NON_LOCAL_INSTANCE(376, "Non-local instance"),
    INTEGER(377, "Integer"),
    LET_DEFINITIONS(379, "Let definitions"),
    LET_IN(380, "Let in"),
    MAYBE_BOUND(381, "Maybe bound"),
    NON_EXP_PREFIX_OP(384, "Non-expression prefix operator"),
    NUMBER(385, "Number literal"),
    NUMBERED_ASSUME_PROVE(386, "Numbered assume prove"),
    OP_APPLICATION(387, "Operator application"),
    OP_ARGS(388, "Operator arguments"),
    OTHER_ARM(390, "Other arm"),
    PAREN_EXPR(393, "Parenthesized expression"),
    POSTFIX_EXPR(395, "Postfix expression"),
    POSTFIX_LHS(396, "Postfix left-hand side"),
    POSTFIX_OP(397, "Postfix operator"),
    PREFIX_EXPR(399, "Prefix expression"),
    PREFIX_LHS(400, "Prefix left-hand side"),
    PREFIX_OP(401, "Prefix operator"),
    PROOF(402, "Proof block"),
    PROOF_STEP(406, "Proof step"),
    QED_STEP(407, "QED step"),
    QUANT_BOUND(408, "Quantifier bound"),
    RCD_CONSTRUCTOR(409, "Record constructor"),
    RECORD_COMPONENT(410, "Record component"),
    SET_ENUMERATE(411, "Set enumeration"),
    SET_OF_ALL(413, "Set of all"),
    SET_OF_FCNS(414, "Set of functions"),
    SET_OF_RCDS(415, "Set of records"),
    STRING(418, "String"),
    SUBSET_OF(419, "Subset of"),
    SUBSTITUTION(420, "Substitution"),
    TUPLE(423, "Tuple expression"),
    UNBOUND_OR_BOUND_CHOOSE(424, "Unbound or bound choose"),
    UNBOUND_QUANT(425, "Unbound quantifier"),
    BOUNDED_QUANT(335, "Bounded quantifier"),

    // Tokens
    T_IN(427, "IN token"),
    T_EQUAL(428, "EQUAL token"),

    // Additional node kinds
    NEW_SYMB(429, "New symbol"),
    LAMBDA(430, "Lambda expression"),
    RECURSIVE(431, "Recursive definition"),
    LABEL(432, "Label"),
    STRUCT_OP(433, "Structure operator"),
    NUMERABLE_STEP(434, "Numerable step"),
    TERMINAL_PROOF(435, "Terminal proof"),
    USE_OR_HIDE(436, "Use or hide"),
    NON_EXPR_BODY(437, "Non-expression body"),
    DEF_STEP(438, "Definition step"),
    HAVE_STEP(439, "Have step"),
    TAKE_STEP(440, "Take step"),
    WITNESS_STEP(441, "Witness step"),
    PICK_STEP(442, "Pick step"),
    CASE_STEP(443, "Case step"),
    ASSERT_STEP(444, "Assert step");

    private final int id;
    private final String description;

    /**
     * Constructor for node kinds with a primary ID and optional alternate IDs.
     *
     * @param primaryId   The main SANY node kind ID
     * @param description Human-readable description
     */
    NodeKind(int primaryId, String description) {
        this.id = primaryId;
        this.description = description;
    }

    public int getId() {
        return id;
    }

    /**
     * Get the human-readable description.
     *
     * @return Description of this node kind
     */
    public String getDescription() {
        return description;
    }

    @Override
    public String toString() {
        return String.format("%s(%s): %s",
                name(),
                id,
                description);
    }
}