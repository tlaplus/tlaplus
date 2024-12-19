package tlc2.debug;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.List;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.parser.TLAplusParser;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.Context;
import tla2sany.semantic.Errors;
import tla2sany.semantic.Generator;
import tla2sany.semantic.LevelConstants;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.st.Location;
import tlc2.tool.impl.SpecProcessor;
import util.ToolIO;

/**
 * An expression for conditionally triggering a breakpoint.
 */
public class TLCBreakpointExpression {

	/**
	 * Given a spec and an unparsed expression, build an operator that can be
	 * evaluated within the context of that spec.
	 *
	 * @param processor     Processes expression within the model context.
	 * @param semanticRoot  The root of the spec's semantic parse tree.
	 * @param location      The breakpoint location.
	 * @param conditionExpr The unparsed breakpoint expression.
	 * @return A breakpoint expression, or null if parsing failed.
	 */
	public static OpDefNode process(
			final SpecProcessor processor,
			final ModuleNode semanticRoot,
			final Location location,
			final String conditionExpr
	) {
		if (null == conditionExpr || conditionExpr.isBlank()) {
			return null;
		}
		ToolIO.out.println("BPExpr: processing expression \"" + conditionExpr + "\"");

		final String rootModName = semanticRoot.getName().toString();
		final String bpModName = generateUnusedName(semanticRoot, "__BreakpointModule__%s");
		ToolIO.out.println("BPExpr: wrapping with module \"" + bpModName + "\"");
		final String bpOpName = generateUnusedName(semanticRoot, "__BreakpointExpr__%s");
		final List<String> params = getScopedIdentifiers(semanticRoot, location);
		ToolIO.out.println("BPExpr: wrapping with op \"" + bpOpName + "\"");

		final String wrapper = "---- MODULE %s ----\nEXTENDS %s\n%s == %s\n====";
		String wrappedConditionExpr = String.format(wrapper, bpModName, rootModName, bpOpName, conditionExpr);
		byte[] wrappedConditionExprBytes = wrappedConditionExpr.getBytes(StandardCharsets.UTF_8);
		InputStream sourceCode = new ByteArrayInputStream(wrappedConditionExprBytes);
		TLAplusParser parser = new TLAplusParser(sourceCode, StandardCharsets.UTF_8.name());
		boolean syntaxParseSuccess = parser.parse();
		SyntaxTreeNode syntaxRoot = parser.ParseTree;
		if (!syntaxParseSuccess || null == syntaxRoot) {
			// Parse error is output to ToolIO.out
			return null;
		}
		ToolIO.out.println("BPExpr: success [syntactic analysis]");

		Errors semanticLog = new Errors();
		SemanticNode.setError(semanticLog); // Annoyingly static
		Generator semanticChecker = new Generator(semanticRoot.semanticChecker.moduleTable, semanticLog);
		ModuleNode bpModule = null;
		try {
			bpModule = semanticChecker.generate(syntaxRoot);
		} catch (AbortException e) {
			ToolIO.err.print(e.toString());
			return null;
		}
		if (null == bpModule || semanticLog.isFailure()) {
			ToolIO.err.print(semanticLog.toString());
			return null;
		}
		ToolIO.out.println("BPExpr: success [semantic analysis]");

		// Run level-checking. The operator should be restricted to
		// action-level or below.
		Errors levelCheckingErrors = new Errors();
		boolean levelCheckingSuccess = bpModule.levelCheck(levelCheckingErrors);
		if (!levelCheckingSuccess || levelCheckingErrors.isFailure() || !bpModule.levelCorrect) {
			ToolIO.err.println(levelCheckingErrors.toString());
			return null;
		}
		ToolIO.out.println("BPExpr: success [level analysis]");
		
		OpDefNode bpOp = bpModule.getOpDef(bpOpName);
		if (null == bpOp) {
			ToolIO.err.println("ERROR: unable to find breakpoint expression op " + bpOpName);
		}

		if (!(LevelConstants.ConstantLevel == bpOp.level || LevelConstants.VariableLevel == bpOp.level
				|| LevelConstants.ActionLevel == bpOp.level)) {
			ToolIO.err.println("ERROR: Debug expressions must be action-level or below; actual level: "
					+ SemanticNode.levelToString(bpOp.level));
			return null;
		}

		processor.myProcessConstants(bpModule);
		
		ToolIO.out.println("BPExpr: integration complete");
		return bpOp;
	}
	
	/**
	 * Generates a plausible definition name that is not already in use.
	 *
	 * @param semanticRoot The module in which to check for name collisions.
	 * @param pattern A base pattern in which a number can be interpolated.
	 * @return A name that is unique within the context of the module.
	 */
	private static String generateUnusedName(ModuleNode semanticRoot, String pattern) {
		Context definedNames = semanticRoot.getContext();
		String unusedName = null;
		do {
			long suffix = System.currentTimeMillis();
			unusedName = String.format(pattern, Long.toString(suffix));
		} while (definedNames.occurSymbol(unusedName));
		return unusedName;
	}
	
	/**
	 * The expression operator can accept parameters; for example if we want
	 * to add a breakpoint at the following location:
	 *
	 * VARIABLE i
	 * op(j) ==
	 *   \A k \in S :
	 *     F(i, j, k) (* want to add breakpoint here)
	 *
	 * It would be nice for the user to just be able to type an expression
	 * like "i + j >= k"; however, there then arises the problem of how to take
	 * that expression and make it parse-able. Thus we end up auto-generating
	 * an operator that looks like:
	 *
	 * __BreakpointExpr__0(j, k) == i + j >= k
	 *
	 * Where we put the two scoped identifiers as parameters to the operator
	 * (note that we do not put the global identifier "i" as a parameter,
	 * because SANY would raise a parse error for multiple "i" definitions).
	 * Then, when evaluating the breakpoint expression we find those named
	 * values in the stack frame and plug them in. It is tricky but possible
	 * to isolate only the variables local to the breakpoint scope; that is
	 * what this function does.
	 *
	 * However, this gives rise to another problem; what if the user writes a
	 * spec like this?
	 *
	 * op(i) ==
	 *   \A j \in S :
	 *     F(i, j) (* want to add breakpoint here *)
	 * VARIABLE i
	 *
	 * Since when we extend the module so as to define our generated op it is
	 * implicitly parsed at the end of the file, "__BreakpointExpr__0(i, j)"
	 * will result in a parse error due to multiple "i" definitions.
	 * Currently these types of specs are simply not supported. Supporting
	 * them would probably require changes to the semantic analysis and
	 * constants-resolver code enabling parsing "ghost" definitions at
	 * arbitrary points in the tree.
	 *
	 * @param semanticRoot The root node of the semantic parse tree.
	 * @param location     The breakpoint location.
	 * @return A list of local identifiers accessible at the given location.
	 */
	static List<String> getScopedIdentifiers(
			ModuleNode semanticRoot,
			Location location
	) {
		List<SemanticNode> path = semanticRoot.pathTo(location);
		return null;
	}
}