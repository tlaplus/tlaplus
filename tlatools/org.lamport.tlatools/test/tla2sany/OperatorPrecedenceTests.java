package tla2sany;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.parser.TLAplusParser;
import tla2sany.semantic.AbortException;
import tla2sany.configuration.Configuration;
import tla2sany.semantic.BuiltInLevel;
import tla2sany.st.SyntaxTreeConstants;
import util.TestPrintStream;
import util.ToolIO;

import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;

import java.io.InputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.io.ByteArrayInputStream;
import java.nio.charset.StandardCharsets;

public class OperatorPrecedenceTests {
	
	private static enum FixKind {
		PREFIX,
		INFIX,
		POSTFIX
	}
	
	private static enum Operator {
		LNOT (FixKind.PREFIX, new String[] {"~", "\\lnot"}, 4, 4, true),
		IMPLIES (FixKind.INFIX, new String[] {"=>"}, 1, 1, false),
		PLUS (FixKind.INFIX, new String[] {"+"}, 10, 10, true),
		SUP_PLUS (FixKind.POSTFIX, new String[] {"^+"}, 15, 15, true);
		
		public final FixKind Fix;
		
		public final String[] Symbols;

		public final int LowPrecedence;
		
		public final int HighPrecedence;
		
		public final boolean Associative;
		
		private Operator(FixKind fix, String[] symbols, int low, int high, boolean associative) {
			this.Fix = fix;
			this.Symbols = symbols;
			this.LowPrecedence = low;
			this.HighPrecedence = high;
			this.Associative = associative;
		}
	}
	
	private static class NullOutputStream extends OutputStream {
		public void write(int b) {
			// Do nothing
		}
	}
	
	@BeforeClass
	public static void setup() throws AbortException {
		Configuration.load(null);
		BuiltInLevel.load();
		ToolIO.out = new PrintStream(new NullOutputStream());
	}
	
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
	
	private static void checkParsePrecedence(
			SyntaxTreeNode root,
			Operator op1,
			String op1Symbol,
			Operator op2,
			String op2Symbol
	) {
		SyntaxTreeNode[] module = root.getHeirs();
		SyntaxTreeNode body = module[2];
		SyntaxTreeNode[] units = body.getHeirs();
		SyntaxTreeNode assume = units[0];
		SyntaxTreeNode lowerPrecOp = assume.getHeirs()[1];
		SyntaxTreeNode[] lowerPrecOpHeirs = lowerPrecOp.getHeirs();
		String lowerPrecOpSymbol = null;
		SyntaxTreeNode higherPrecOp = null;
		switch (lowerPrecOp.getKind()) {
			case SyntaxTreeConstants.N_PrefixExpr: {
				lowerPrecOpSymbol = lowerPrecOpHeirs[0].getHeirs()[1].getImage();
				higherPrecOp = lowerPrecOpHeirs[1];
				break;
			} case SyntaxTreeConstants.N_InfixExpr: {
				lowerPrecOpSymbol = lowerPrecOpHeirs[1].getHeirs()[1].getImage();
				higherPrecOp =
						lowerPrecOpHeirs[0].isKind(SyntaxTreeConstants.N_GeneralId)
						? lowerPrecOpHeirs[2]
						: lowerPrecOpHeirs[0];
				break;
			} case SyntaxTreeConstants.N_PostfixExpr: {
				higherPrecOp = lowerPrecOpHeirs[0];
				lowerPrecOpSymbol = lowerPrecOpHeirs[1].getHeirs()[1].getImage();
				break;
			} default: {
				Assert.fail(lowerPrecOp.getImage());
			}
		}
		SyntaxTreeNode[] higherPrecOpHeirs = higherPrecOp.getHeirs();
		String higherPrecOpSymbol = null;
		switch (higherPrecOp.getKind()) {
			case SyntaxTreeConstants.N_PrefixExpr: {
				higherPrecOpSymbol = higherPrecOpHeirs[0].getHeirs()[1].getImage();
				break;
			} case SyntaxTreeConstants.N_InfixExpr: {
				higherPrecOpSymbol = higherPrecOpHeirs[1].getHeirs()[1].getImage();
				break;
			} case SyntaxTreeConstants.N_PostfixExpr: {
				higherPrecOpSymbol = higherPrecOpHeirs[1].getHeirs()[1].getImage();
				break;
			} default: {
				Assert.fail(higherPrecOp.getImage());
			}
		}
		System.out.println(String.format("Higher: %s, lower: %s", higherPrecOpSymbol, lowerPrecOpSymbol));
		switch (op1.Fix) {
			case PREFIX: switch (op2.Fix) {
				case PREFIX: {
					Assert.assertEquals(lowerPrecOpSymbol, op1Symbol);
					Assert.assertEquals(higherPrecOpSymbol, op2Symbol);
					return;
				} case INFIX: {

				} case POSTFIX: {
					
				}
			} case INFIX: switch (op2.Fix) {
				case PREFIX: {
					
				} case INFIX: {
					
				} case POSTFIX: {
					
				}
			} case POSTFIX: switch (op2.Fix) { 
				case PREFIX: {
					
				} case INFIX: {
					
				} case POSTFIX: {
					
				}
			}
		}
	}
	
	@Test
	public void testAllOperatorCombinations() {
		String pattern = "---- MODULE Test ----\nASSUME %s \n====";
		for (Operator op1 : Operator.values()) {
			for (Operator op2 : Operator.values()) {
				if (FixKind.POSTFIX == op1.Fix && FixKind.PREFIX == op2.Fix) {
					// Can't construct a test case from this
					continue;
				}
				for (String op1Symbol : op1.Symbols) {
					for (String op2Symbol : op2.Symbols) {
						String expr = deriveExpression(op1, op1Symbol, op2, op2Symbol);
						String inputString = String.format(pattern, expr);
						byte[] inputBytes = inputString.getBytes(StandardCharsets.UTF_8);
						InputStream inputStream = new ByteArrayInputStream(inputBytes);
						TLAplusParser parser = new TLAplusParser(inputStream, StandardCharsets.UTF_8.name());
						boolean expectAssociativityError = (op1 == op2 && !op1.Associative);
						System.out.println(expr);
						boolean expectPrecedenceConflict =
								op1 != op2
								&& ((op1.LowPrecedence <= op2.LowPrecedence && op2.LowPrecedence <= op1.HighPrecedence)
								|| (op1.LowPrecedence <= op2.HighPrecedence && op2.HighPrecedence <= op1.HighPrecedence));
						boolean success = !expectAssociativityError && !expectPrecedenceConflict;
						Assert.assertEquals(expr, success, parser.parse());
						if (success) {
							checkParsePrecedence(parser.ParseTree, op1, op1Symbol, op2, op2Symbol);
						}
					}
				}
			}
		}
	}
}
