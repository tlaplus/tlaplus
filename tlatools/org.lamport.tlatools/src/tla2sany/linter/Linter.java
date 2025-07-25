/*******************************************************************************
 * Copyright (c) 2025 NVIDIA Corp. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tla2sany.linter;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import tla2sany.semantic.ErrorCode;
import tla2sany.semantic.Errors;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.ExternalModuleTable;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SemanticNode.ChildrenVisitor;
import tla2sany.semantic.StringNode;
import tla2sany.semantic.SymbolNode;
import util.UniqueString;

public class Linter {

	private static class Records {

		// Returns true if two records share the same DOMAIN.
		public static boolean sameDomain(final OpApplNode r1, final OpApplNode r2) {
			if (r1 == r2) {
				return true;
			}
			if (r1.getArgs().length != r2.getArgs().length) {
				return false;
			}
			OUTER: for (int i = 0; i < r1.getArgs().length; i++) {
				OpApplNode f1 = (OpApplNode) r1.getArgs()[i];
				StringNode s1 = (StringNode) f1.getArgs()[0];

				for (int j = 0; j < r2.getArgs().length; j++) {
					OpApplNode f2 = (OpApplNode) r2.getArgs()[j];
					StringNode s2 = (StringNode) f2.getArgs()[0];
					if (s1.getRep() == s2.getRep()) {
						continue OUTER;
					}
				}
				return false;
			}
			return true;
		}

	}

	public void lint(ModuleNode m, ExternalModuleTable moduleTable, Errors errors) {
		lintRecords(m, errors);
	}

	// Raise a warning if SANY encounters the following construct, which suggests
	// that the user expects the value of R to be [i \in {23} |-> 42], i.e. 23 :>
	// 42:
	//
	// bar == 23
	// R == [bar |-> 42]
	//
	// This may indicate a misunderstanding of the semantics of record construction.
	//
	// However, do NOT raise a warning in cases like the following, which imply that
	// she understands the semantics correctly:
	//
	// CONSTANT bar
	// R == [bar |-> bar]
	//
	// (see https://github.com/tlaplus/tlaplus/issues/1184#issuecomment-2889363740)
	private void lintRecords(ModuleNode m, Errors errors) {
		final List<OpApplNode> records = Arrays.asList(m.getRecords());

		// All records across all modules.
		final List<OpApplNode> allRecords = m.getExtendedModuleSet(true).stream()
				.flatMap(mod -> Arrays.stream(mod.getRecords())).collect(Collectors.toList());
		allRecords.addAll(records);

		for (final OpApplNode record : records) {
			final List<OpApplNode> fieldPairs = getFieldPairs(record);
			for (final OpApplNode fp : fieldPairs) {
				final StringNode lhs = (StringNode) fp.getArgs()[0];
				final ExprOrOpArgNode rhs = fp.getArgs()[1];
				final SymbolNode s = m.getContext().getSymbol(lhs.getRep());
				if (s != null) {
					if (!isBuiltFromDeclarations(rhs)
							// Suppress the warning for the current record component if the right-hand side
							// of any other component of this record is built from a CONSTANT, VARIABLE, or
							// bound variable, suggesting that the user understands the semantics.
							&& !fieldPairs.stream().anyMatch(Linter::isBuiltFromDeclarations)
							// Suppress the warning for the current record component if the right-hand side
							// of any other record with the same components is built from a CONSTANT,
							// VARIABLE, or bound variable, suggesting that the user understands the
							// semantics.
							&& !allRecords.stream().filter(r -> Records.sameDomain(r, record))
									.flatMap(r -> getFieldPairs(r).stream())
									.anyMatch(Linter::isBuiltFromDeclarations)) {
						errors.addWarning(ErrorCode.RECORD_CONSTRUCTOR_FIELD_NAME_CLASH, lhs.getLocation(), String
								.format("The field name \"%1$s\" in the record constructor is identical to the existing definition or declaration\n"
										+ "named %1$s, located at %2$s.\n"
										+ "The field in the record will not take the value of the %1$s definition or declaration.\n"
										+ "In TLA+, field names in records are strings, regardless of any similarly named declarations or definitions.\n"
										+ "Therefore, DOMAIN [%1$s |-> ...] = {\"%1$s\"} holds true.", lhs.getRep(),
										s.getLocation()));
					}
				}
			}
		}
	}

	private static List<OpApplNode> getFieldPairs(OpApplNode record) {
		return Arrays.asList(record.getArgs()).stream().filter(arg -> arg instanceof OpApplNode)
				.map(arg -> (OpApplNode) arg).collect(Collectors.toList());
	}

	// true if the ExprOrOpArgNode is (transitively) built from a parameter
	// (FormalParameterNode), CONSTANT (OpDeclNode), or a VARIABLE (OpDeclNode)
	// declaration.
	// TODO: Should this become API of SemanticNode?
	private static boolean isBuiltFromDeclarations(final ExprOrOpArgNode expr) {
		return expr.walkChildren(new ChildrenVisitor<Boolean>() {
			private boolean found;

			public void preVisit(final SemanticNode node) {
				if (node instanceof OpApplNode) {
					final SymbolNode operator = ((OpApplNode) node).getOperator();
					if (operator instanceof OpDeclNode) {
						found = true;
					}
					if (operator instanceof FormalParamNode) {
						found = true;
					}
					if (operator instanceof OpDefNode) {
						// Special cases for operator stubs in the standard modules.
						if (operator.getName() == UniqueString.of("BOOLEAN")) {
							found = true;
							return;
						}
						final ModuleNode moduleNode = ((OpDefNode) operator).getOriginallyDefinedInModuleNode();
						if (moduleNode != null && moduleNode.getName() == UniqueString.of("Integers")
								&& operator.getName() == UniqueString.of("Int")) {
							found = true;
							return;
						}
						if (moduleNode != null && moduleNode.getName() == UniqueString.of("Naturals")
								&& operator.getName() == UniqueString.of("Nat")) {
							found = true;
							return;
						}
						if (moduleNode != null && moduleNode.getName() == UniqueString.of("Reals")
								&& operator.getName() == UniqueString.of("Reals")) {
							found = true;
							return;
						}
						// Follow the operator definition to see if it is built from declarations.
						operator.walkChildren(this);
					}
				}
			}

			public boolean preempt(SemanticNode node) {
				// Stops the traversal early if a node meeting the criteria (e.g., being an
				// OpDeclNode or FormalParamNode) has been found. This improves efficiency by
				// avoiding unnecessary traversal of the remaining nodes.
				return found;
			}

			public Boolean get() {
				return found;
			}
		}).get();
	}

}
