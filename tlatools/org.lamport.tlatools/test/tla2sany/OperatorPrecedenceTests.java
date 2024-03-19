package tla2sany;

import tla2sany.parser.Operators;
import tla2sany.parser.SyntaxTreeNode;
import tla2sany.parser.TLAplusParser;
import tla2sany.semantic.AbortException;
import tla2sany.configuration.Configuration;
import tla2sany.semantic.BuiltInLevel;
import tla2sany.st.SyntaxTreeConstants;
import util.ToolIO;
import util.UniqueString;

import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;

import java.io.InputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.io.ByteArrayInputStream;
import java.nio.charset.StandardCharsets;

/**
 * Performs a large number of parse tests on prefix, infix, and postfix
 * operators focusing on their interaction through precedence and
 * associativity.
 */
public class OperatorPrecedenceTests {
	
	/**
	 * Whether an operator is a prefix, infix, or postfix operator.
	 */
	private static enum FixKind {
		PREFIX,
		INFIX,
		POSTFIX
	}
	
	/**
	 * Holds data describing the properties of an operator.
	 */
	private static class Operator {

		/**
		 * Whether the operator is prefix, infix, or postfix.
		 */
		public final FixKind Fix;
		
		/**
		 * Operator symbol variants.
		 */
		public final String[] Symbols;

		/**
		 * The lower bound of the operator precedence range.
		 */
		public final int LowPrecedence;
		
		/**
		 * The upper bound of the operator precedence range.
		 */
		public final int HighPrecedence;
		
		/**
		 * Whether the operator is associative, in practice just left-
		 * associative.
		 */
		public final boolean Associative;
		
		/**
		 * Creates a new instance of the Operator class.
		 * 
		 * @param fix The operator fix kind.
		 * @param symbols The operator symbol alternatives.
		 * @param low The operator precedence lower bound.
		 * @param high The operator precedence upper bound.
		 * @param associative Whether the operator is associative.
		 */
		private Operator(FixKind fix, String[] symbols, int low, int high, boolean associative) {
			this.Fix = fix;
			this.Symbols = symbols;
			this.LowPrecedence = low;
			this.HighPrecedence = high;
			this.Associative = associative;
		}
		
		/**
		 * True if this operator is lower precedence than the given one. This
		 * means their ranges do not overlap at all and the range of this one
		 * is entirely below the range of the other one.
		 * 
		 * @param other The operator to compare against.
		 * @return Whether this operator is lower precedence.
		 */
		private boolean lowerPrecThan(Operator other) {
			return this.LowPrecedence < other.LowPrecedence
					&& this.HighPrecedence < other.HighPrecedence;
		}
		
		/**
		 * Whether this operator conflicts with the given other operator.
		 * There are a number of cases to handle, documented in-line.
		 * 
		 * @param other The operator to check against.
		 * @return Whether this operator conflicts with the other operator.
		 */
		private boolean conflictsWith(Operator other) {
			if (this.Fix == other.Fix && (FixKind.PREFIX == this.Fix || FixKind.POSTFIX == this.Fix)) {
				// Prefix & postfix ops can't really conflict with others in their class.
				return false;
			} else if (FixKind.INFIX == this.Fix && FixKind.PREFIX == other.Fix) {
				// Expressions such as A = ENABLED B are always unambiguous.
				return false;
			} else if (FixKind.POSTFIX == this.Fix && FixKind.INFIX == other.Fix) {
				// Expressions such as A' + B are always unambiguous.
				return false;
			} else if (this == other) {
				// Identical infix ops will conflict unless they are associative.
				return !this.Associative;
			} else {
				// Conflicts if precedence range overlaps.
				return (this.LowPrecedence <= other.LowPrecedence && other.LowPrecedence <= this.HighPrecedence) // overlap low
						|| (this.LowPrecedence <= other.LowPrecedence && other.HighPrecedence <= this.HighPrecedence) // enclose
						|| (other.LowPrecedence <= this.LowPrecedence && this.HighPrecedence <= other.HighPrecedence) // enclosed by
						|| (this.LowPrecedence <= other.HighPrecedence && other.HighPrecedence <= this.HighPrecedence); // overlap high
			}
		}
	}
	
	/**
	 * A basic syntactically valid module that can hold an expression.
	 */
	private static final String pattern = "---- MODULE Test ----\nASSUME %s \n====";

	/**
	 * All these operator precedence values are taken from the PDF "Summary
	 * of TLA+" (https://lamport.azurewebsites.net/tla/summary-standalone.pdf)
	 * with the exception of SUBSET, UNION, and DOMAIN which were incorrectly
	 * documented as having precedences 8-8, 8-8, and 9-9 respectively; SANY
	 * sets their precedences as 10-13. See this GitHub issue:
	 * https://github.com/tlaplus/tlaplus/issues/892
	 * 
	 * The very first string symbol in the array is the canonical symbol for
	 * that operator.
	 */
	private static final Operator[] operators = new Operator[] {
		new Operator(FixKind.PREFIX, new String[] {"\\lnot", "~", "\\neg"}, 4, 4, false),
		new Operator(FixKind.PREFIX, new String[] {"ENABLED"}, 4, 15, false),
		new Operator(FixKind.PREFIX, new String[] {"UNCHANGED"}, 4, 15, false),
		new Operator(FixKind.PREFIX, new String[] {"[]"}, 4, 15, false),
		new Operator(FixKind.PREFIX, new String[] {"<>"}, 4, 15, false),
		// https://github.com/tlaplus/tlaplus/issues/892
		new Operator(FixKind.PREFIX, new String[] {"SUBSET"}, 10, 13, false),
		new Operator(FixKind.PREFIX, new String[] {"UNION"}, 10, 13, false),
		new Operator(FixKind.PREFIX, new String[] {"DOMAIN"}, 10, 13, false),
		// https://github.com/tlaplus/tlaplus/issues/893
		//new Operator(FixKind.PREFIX, new String[] {"-"}, 12, 12, false),
		new Operator(FixKind.INFIX, new String[] {"=>"}, 1, 1, false),
		new Operator(FixKind.INFIX, new String[] {"-+->"}, 2, 2, false),
		new Operator(FixKind.INFIX, new String[] {"\\equiv", "<=>"}, 2, 2, false),
		new Operator(FixKind.INFIX, new String[] {"~>"}, 2, 2, false),
		new Operator(FixKind.INFIX, new String[] {"\\lor", "\\/"}, 3, 3, true),
		new Operator(FixKind.INFIX, new String[] {"\\land", "/\\"}, 3, 3, true),
		new Operator(FixKind.INFIX, new String[] {"/=", "#"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"-|"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"::="}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {":="}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"<"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"="}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"=|"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {">"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\approx"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\asymp"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\cong"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\doteq"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\geq", ">="}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\gg"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\in"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\notin"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\leq", "<=", "=<"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\ll"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\prec"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\preceq"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\propto"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\sim"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\simeq"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\sqsubset"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\sqsubseteq"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\sqsupset"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\sqsupseteq"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\subset"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\subseteq"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\succ"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\succeq"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\supset"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\supseteq"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"|-"}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"|="}, 5, 5, false),
		new Operator(FixKind.INFIX, new String[] {"\\cdot"}, 5, 14, true),
		new Operator(FixKind.INFIX, new String[] {"@@"}, 6, 6, true),
		new Operator(FixKind.INFIX, new String[] {":>"}, 7, 7, false),
		new Operator(FixKind.INFIX, new String[] {"<:"}, 7, 7, false),
		new Operator(FixKind.INFIX, new String[] {"\\"}, 8, 8, false),
		new Operator(FixKind.INFIX, new String[] {"\\intersect", "\\cap"}, 8, 8, true),
		new Operator(FixKind.INFIX, new String[] {"\\union", "\\cup"}, 8, 8, true),
		new Operator(FixKind.INFIX, new String[] {".."}, 9, 9, false),
		new Operator(FixKind.INFIX, new String[] {"..."}, 9, 9, false),
		new Operator(FixKind.INFIX, new String[] {"!!"}, 9, 13, false),
		new Operator(FixKind.INFIX, new String[] {"##"}, 9, 13, true),
		new Operator(FixKind.INFIX, new String[] {"$"}, 9, 13, true),
		new Operator(FixKind.INFIX, new String[] {"$$"}, 9, 13, true),
		new Operator(FixKind.INFIX, new String[] {"??"}, 9, 13, true),
		new Operator(FixKind.INFIX, new String[] {"\\sqcap"}, 9, 13, true),
		new Operator(FixKind.INFIX, new String[] {"\\sqcup"}, 9, 13, true),
		new Operator(FixKind.INFIX, new String[] {"\\uplus"}, 9, 13, true),
		new Operator(FixKind.INFIX, new String[] {"\\wr"}, 9, 14, false),
		new Operator(FixKind.INFIX, new String[] {"\\oplus", "(+)"}, 10, 10, true),
		new Operator(FixKind.INFIX, new String[] {"+"}, 10, 10, true),
		new Operator(FixKind.INFIX, new String[] {"++"}, 10, 10, true),
		new Operator(FixKind.INFIX, new String[] {"%"}, 10, 11, false),
		new Operator(FixKind.INFIX, new String[] {"%%"}, 10, 11, true),
		new Operator(FixKind.INFIX, new String[] {"|"}, 10, 11, true),
		new Operator(FixKind.INFIX, new String[] {"||"}, 10, 11, true),
		new Operator(FixKind.INFIX, new String[] {"\\ominus", "(-)"}, 11, 11, true),
		new Operator(FixKind.INFIX, new String[] {"-"}, 11, 11, true),
		new Operator(FixKind.INFIX, new String[] {"--"}, 11, 11, true),
		new Operator(FixKind.INFIX, new String[] {"&"}, 13, 13, true),
		new Operator(FixKind.INFIX, new String[] {"&&"}, 13, 13, true),
		new Operator(FixKind.INFIX, new String[] {"\\odot", "(.)"}, 13, 13, true),
		new Operator(FixKind.INFIX, new String[] {"\\oslash", "(/)"}, 13, 13, false),
		new Operator(FixKind.INFIX, new String[] {"\\otimes", "(\\X)"}, 13, 13, true),
		new Operator(FixKind.INFIX, new String[] {"*"}, 13, 13, true),
		new Operator(FixKind.INFIX, new String[] {"**"}, 13, 13, true),
		new Operator(FixKind.INFIX, new String[] {"/"}, 13, 13, false),
		new Operator(FixKind.INFIX, new String[] {"//"}, 13, 13, false),
		new Operator(FixKind.INFIX, new String[] {"\\bigcirc"}, 13, 13, true),
		new Operator(FixKind.INFIX, new String[] {"\\bullet"}, 13, 13, true),
		new Operator(FixKind.INFIX, new String[] {"\\div"}, 13, 13, false),
		new Operator(FixKind.INFIX, new String[] {"\\o", "\\circ"}, 13, 13, true),
		new Operator(FixKind.INFIX, new String[] {"\\star"}, 13, 13, true),
		new Operator(FixKind.INFIX, new String[] {"^"}, 14, 14, false),
		new Operator(FixKind.INFIX, new String[] {"^^"}, 14, 14, false),
		new Operator(FixKind.POSTFIX, new String[] {"^+"}, 15, 15, false),
		new Operator(FixKind.POSTFIX, new String[] {"^*"}, 15, 15, false),
		new Operator(FixKind.POSTFIX, new String[] {"^#"}, 15, 15, false),
		new Operator(FixKind.POSTFIX, new String[] {"'"}, 15, 15, false),
	};
	
	/**
	 * Used to silence SANY output on parse errors.
	 */
	private static class NullOutputStream extends OutputStream {
		public void write(int b) {
			// Do nothing
		}
	}
	
	/**
	 * Performs static initialization of SANY.
	 * 
	 * @throws AbortException If initialization error occurs.
	 */
	@BeforeClass
	public static void setup() throws AbortException {
		Configuration.load(null);
		BuiltInLevel.load();
		ToolIO.out = new PrintStream(new NullOutputStream());
	}
	
	/**
	 * Given two operators, derive a syntactically-plausible expression that
	 * uses them.
	 * 
	 * @param op1 The operator which should appear first.
	 * @param op1Symbol The symbol of the operator which should appear first.
	 * @param op2 The operator which should appear second.
	 * @param op2Symbol The symbol of the operator which should appear second.
	 * @return A syntactically-plausible expression.
	 */
	private static String deriveExpression(Operator op1, String op1Symbol, Operator op2, String op2Symbol) {
		switch (op1.Fix) {
			case PREFIX: switch (op2.Fix) {
				case PREFIX: return String.format("%s %s A", op1Symbol, op2Symbol);
				case INFIX: return String.format("%s A %s B", op1Symbol, op2Symbol);
				case POSTFIX: return String.format("%s A %s", op1Symbol, op2Symbol);
			}
			case INFIX: switch (op2.Fix) {
				case PREFIX: return String.format("A %s %s B", op1Symbol, op2Symbol);
				case INFIX: return String.format("A %s B %s C", op1Symbol, op2Symbol);
				case POSTFIX: return String.format("A %s B %s", op1Symbol, op2Symbol);
			}
			case POSTFIX: switch (op2.Fix) {
				case PREFIX: Assert.fail(); return "";
				case INFIX: return String.format("A %s %s B", op1Symbol, op2Symbol);
				case POSTFIX: return String.format("A %s %s", op1Symbol, op2Symbol);
			}
			default: Assert.fail(); return "";
		}
	}
	
	/**
	 * Given a SANY parse tree of a module with a single ASSUME statement,
	 * navigate to the expression node of that statement.
	 * 
	 * @param root The root node of the parse tree.
	 * @return The expression node of the ASSUME statement.
	 */
	private static SyntaxTreeNode getExpressionInModule(SyntaxTreeNode root) {
		SyntaxTreeNode[] module = root.getHeirs();
		SyntaxTreeNode body = module[2];
		SyntaxTreeNode[] units = body.getHeirs();
		SyntaxTreeNode assume = units[0];
		return assume.getHeirs()[1];
	}
	
	/**
	 * Given some sort of operator expression with a higher-precedence
	 * operator as one of its children, find & return that child.
	 * 
	 * @param lowerPrecOp The operator expression to look inside.
	 * @return The higher-prec operator child of the given expression.
	 */
	private static SyntaxTreeNode getHigherPrecOp(SyntaxTreeNode lowerPrecOp) {
		SyntaxTreeNode[] lowerPrecOpHeirs = lowerPrecOp.getHeirs();
		switch (lowerPrecOp.getKind()) {
			case SyntaxTreeConstants.N_PrefixExpr: return lowerPrecOpHeirs[1];
			case SyntaxTreeConstants.N_InfixExpr:
				return lowerPrecOpHeirs[0].isKind(SyntaxTreeConstants.N_GeneralId)
						? lowerPrecOpHeirs[2]
						: lowerPrecOpHeirs[0];
			case SyntaxTreeConstants.N_PostfixExpr: return lowerPrecOpHeirs[0];
		}
		Assert.fail();
		return null;
	}
	
	/**
	 * Given an operator expression, retrieves the string representation of
	 * the operator being used.
	 * 
	 * @param op The operator expression.
	 * @return String representation of the operator being used.
	 */
	private static String getOpImage(SyntaxTreeNode op) {
		SyntaxTreeNode[] opHeirs = op.getHeirs();
		switch (op.getKind()) {
			case SyntaxTreeConstants.N_PrefixExpr: return opHeirs[0].getHeirs()[1].getImage();
			case SyntaxTreeConstants.N_InfixExpr: return opHeirs[1].getHeirs()[1].getImage();
			case SyntaxTreeConstants.N_PostfixExpr: return opHeirs[1].getHeirs()[1].getImage();
		}
		Assert.fail();
		return null;
	}
	
	/**
	 * Checks the parse tree to ensure the operators were parsed as expected.
	 * 
	 * @param root The root of the parse tree.
	 * @param op1 The operator appearing first.
	 * @param op1Symbol The symbol of the operator appearing first.
	 * @param op2 The operator appearing second.
	 * @param op2Symbol The symbol of the operator appearing second.
	 */
	private static void checkParsePrecedence(
			SyntaxTreeNode root,
			Operator op1,
			String op1Symbol,
			Operator op2,
			String op2Symbol
	) {
		SyntaxTreeNode lowerPrecOp = getExpressionInModule(root);
		String lowerPrecOpSymbol = getOpImage(lowerPrecOp);
		SyntaxTreeNode higherPrecOp = getHigherPrecOp(lowerPrecOp);
		String higherPrecOpSymbol = getOpImage(higherPrecOp);
		if (op1 == op2) {
			if (op1.Associative) {
				Assert.assertEquals(lowerPrecOpSymbol, op2Symbol);
				Assert.assertEquals(higherPrecOpSymbol, op1Symbol);
			} else {
				Assert.assertEquals(lowerPrecOpSymbol, op1Symbol);
				Assert.assertEquals(higherPrecOpSymbol, op2Symbol);
			}
		} else if (op1.lowerPrecThan(op2) || FixKind.PREFIX == op2.Fix) {
			Assert.assertEquals(lowerPrecOpSymbol, op1Symbol);
			Assert.assertEquals(higherPrecOpSymbol, op2Symbol);
		} else {
			Assert.assertEquals(lowerPrecOpSymbol, op2Symbol);
			Assert.assertEquals(higherPrecOpSymbol, op1Symbol);
		}
	}
	
	/**
	 * Builds a TLA+ parser instance for the given string.
	 * 
	 * @param inputString The string to build a parser instance for.
	 * @return A TLA+ parser instance.
	 */
	private static TLAplusParser buildParser(String inputString) {
		byte[] inputBytes = inputString.getBytes(StandardCharsets.UTF_8);
		InputStream inputStream = new ByteArrayInputStream(inputBytes);
		return new TLAplusParser(inputStream, StandardCharsets.UTF_8.name());
	}

	/**
	 * Runs through all pairwise operator combinations to ensure SANY handles
	 * their interactions correctly. This generates on the order of 10,000
	 * inputs for SANY.
	 */
	@Test
	public void testAllOperatorCombinations() {
		for (Operator op1 : operators) {
			for (Operator op2 : operators) {
				if (FixKind.POSTFIX == op1.Fix && FixKind.PREFIX == op2.Fix) {
					// Can't construct a test case from this
					continue;
				}
				for (String op1Symbol : op1.Symbols) {
					for (String op2Symbol : op2.Symbols) {
						String expr = deriveExpression(op1, op1Symbol, op2, op2Symbol);
						String inputString = String.format(pattern, expr);
						TLAplusParser parser = buildParser(inputString);
						boolean success = !op1.conflictsWith(op2);
						Assert.assertEquals(expr, success, parser.parse());
						if (success) {
							checkParsePrecedence(parser.ParseTree, op1, op1Symbol, op2, op2Symbol);
						}
					}
				}
			}
		}
	}
	
	/**
	 * Tests to ensure associative operators associate and non-associative
	 * operators do not.
	 */
	@Test
	public void testOperatorAssociativity() {
		for (Operator op : operators) {
			for (String opSymbol1 : op.Symbols) {
				for (String opSymbol2 : op.Symbols) {
					for (String opSymbol3 : op.Symbols) {
						String expr = String.format("A %s B %s C", opSymbol1, opSymbol2, opSymbol3);
						String inputString = String.format(pattern, expr);
						TLAplusParser parser = buildParser(inputString);
						Assert.assertEquals(expr, op.Associative, parser.parse());
					}
				}
			}
		}
	}
	
	/**
	 * SANY has the concept of a "canonical" operator representation, since
	 * some operators have multiple possible symbols associated with them.
	 * This tests that the canonical operator is as expected.
	 */
	@Test
	public void testCanonicalOperators() {
		for (Operator op : operators) {
			String expected = op.Symbols[0];
			for (String symbol : op.Symbols) {
				UniqueString symbolUnique = UniqueString.uniqueStringOf(symbol);
				Assert.assertTrue(Operators.existsOperator(symbolUnique));
				Assert.assertEquals(expected, Operators.resolveSynonym(symbolUnique).toString());
			}
		}
	}
}
