package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.*;
import tla2sany.st.TreeNode;

import java.util.List;
import java.util.Set;

/**
 * Construct implementation for VARIABLE/VARIABLES declarations.
 */
public class VariableConstruct extends AbstractDeclarationListConstruct {
    private static final Set<String> KEYWORDS = Set.of("VARIABLE", "VARIABLES");

    @Override
    protected Set<String> getKeywords() {
        return KEYWORDS;
    }

    @Override
    public String getName() {
        return "VARIABLES";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.VARIABLE_DECLARATION.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        Doc prefix = context.buildChild(node.zero()[0]);
        List<TreeNode> variableNodes = extractItemNodes(node);

        if (variableNodes.isEmpty()) {
            return prefix;
        }

        boolean hasComments = variableNodes.stream()
                .anyMatch(n -> n.getPreComments() != null && n.getPreComments().length > 0);

        if (hasComments) {
            return formatWithComments(prefix, variableNodes);
        } else {
            List<String> variables = context.extractStringList(node);
            return new DeclarationListFormatter(context.getConfig(), "VARIABLES").format(prefix, variables);
        }
    }

    private Doc formatWithComments(Doc prefix, List<TreeNode> variableNodes) {
        Doc result = prefix;
        String indent = "  ";
        String commentIndent = "    ";

        for (int i = 0; i < variableNodes.size(); i++) {
            TreeNode varNode = variableNodes.get(i);
            String varName = getItemName(varNode);
            String[] preComments = varNode.getPreComments();

            if (i == 0) {
                if (preComments != null && preComments.length > 0) {
                    for (String comment : preComments) {
                        result = result.appendLine(Doc.text(commentIndent + normalizeComment(comment)));
                    }
                    result = result.appendLine(Doc.text(indent + varName));
                } else {
                    result = result.appendLine(Doc.text(indent + varName));
                }
            } else {
                if (preComments != null && preComments.length > 0) {
                    String normalizedFirst = normalizeComment(preComments[0]);
                    if (preComments.length == 1 && normalizedFirst.trim().startsWith("\\*")) {
                        result = result.append(Doc.text(",    " + normalizedFirst));
                        result = result.appendLine(Doc.text(indent + varName));
                    } else {
                        result = result.append(Doc.text(","));
                        for (String comment : preComments) {
                            result = result.appendLine(Doc.text(commentIndent + normalizeComment(comment)));
                        }
                        result = result.appendLine(Doc.text(indent + varName));
                    }
                } else {
                    result = result.append(Doc.text(",")).appendLine(Doc.text(indent + varName));
                }
            }
        }

        return result;
    }

    private static String normalizeComment(String s) {
        return ConstructContext.normalizeCommentWhitespace(s, false);
    }
}