package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.TlaDocBuilder;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import tla2sany.st.TreeNode;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Construct implementation for CONSTANTS declarations.
 * Handles formatting of "CONSTANTS x, y, z" constructs.
 */
public class ConstantsConstruct extends AbstractDeclarationListConstruct {
    private static final Set<String> KEYWORDS = Set.of("CONSTANT", "CONSTANTS");

    @Override
    protected Set<String> getKeywords() {
        return KEYWORDS;
    }

    @Override
    public String getName() {
        return "N_ParamDeclaration";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.PARAM_DECLARATION.getId();
    }

    @Override
    protected String getItemName(TreeNode node) {
        return buildConstantDeclaration(node);
    }

    private TreeNode getCommentNode(TreeNode node) {
        if (node.getKind() == 363 && node.zero() != null && node.zero().length > 0) {
            return node.zero()[0];
        }
        return node;
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        Doc prefix = context.buildChild(node.zero()[0]);
        List<TreeNode> constantNodes = extractItemNodes(node);

        if (constantNodes.isEmpty()) {
            return prefix;
        }

        Map<Integer, String[]> commaComments = extractCommaPreComments(node);

        boolean hasComments = !commaComments.isEmpty() || constantNodes.stream()
                .anyMatch(n -> {
                    TreeNode commentNode = getCommentNode(n);
                    return commentNode.getPreComments() != null && commentNode.getPreComments().length > 0;
                });

        if (hasComments) {
            if (!commaComments.isEmpty()) {
                return formatCommaFirstWithComments(prefix, constantNodes, commaComments);
            }
            return formatCommaLastWithComments(prefix, constantNodes);
        } else {
            List<String> constants = new ArrayList<>();
            for (TreeNode constNode : constantNodes) {
                constants.add(buildConstantDeclaration(constNode));
            }
            return new DeclarationListFormatter(context.getConfig(), "CONSTANTS").format(prefix, constants);
        }
    }

    private Doc formatCommaFirstWithComments(Doc prefix, List<TreeNode> constantNodes, Map<Integer, String[]> commaComments) {
        Doc result = prefix;
        String indent = "    ";
        String commaPrefix = ",   ";

        for (int i = 0; i < constantNodes.size(); i++) {
            TreeNode constNode = constantNodes.get(i);
            String constDecl = buildConstantDeclaration(constNode);
            TreeNode commentNode = getCommentNode(constNode);
            String[] nodePreComments = commentNode.getPreComments();

            if (i == 0) {
                if (nodePreComments != null && nodePreComments.length > 0) {
                    for (String comment : nodePreComments) {
                        result = result.appendLine(Doc.text(indent + normalizeComment(comment)));
                    }
                }
                result = result.appendLine(Doc.text(indent + constDecl));
            } else {
                if (nodePreComments != null && nodePreComments.length > 0) {
                    for (String comment : nodePreComments) {
                        result = result.appendLine(Doc.text(indent + normalizeComment(comment)));
                    }
                }
                result = result.appendLine(Doc.text(commaPrefix + constDecl));
            }

            String[] postComments = commaComments.get(i + 1);
            if (postComments != null && postComments.length > 0) {
                String normalized = normalizeComment(postComments[0]);
                if (postComments.length == 1 && normalized.trim().startsWith("\\*")) {
                    result = result.append(Doc.text("    " + normalized));
                } else {
                    for (String comment : postComments) {
                        result = result.append(Doc.text("    " + normalizeComment(comment)));
                    }
                }
            }
        }
        return result;
    }

    private Doc formatCommaLastWithComments(Doc prefix, List<TreeNode> constantNodes) {
        Doc result = prefix;
        String indent = "         "; // Align with "CONSTANT " (9 spaces)
        String commentIndent = "    ";

        for (int i = 0; i < constantNodes.size(); i++) {
            TreeNode constNode = constantNodes.get(i);
            String constDecl = buildConstantDeclaration(constNode);
            TreeNode commentNode = getCommentNode(constNode);
            String[] preComments = commentNode.getPreComments();

            if (i == 0) {
                if (preComments != null && preComments.length > 0) {
                    for (String comment : preComments) {
                        result = result.appendLine(Doc.text(commentIndent + normalizeComment(comment)));
                    }
                    result = result.appendLine(Doc.text(commentIndent + constDecl));
                } else {
                    result = result.append(Doc.text(" " + constDecl));
                }
            } else {
                if (preComments != null && preComments.length > 0) {
                    String normalizedFirst = normalizeComment(preComments[0]);
                    if (preComments.length == 1 && normalizedFirst.trim().startsWith("\\*")) {
                        result = result.append(Doc.text(",    " + normalizedFirst));
                        result = result.appendLine(Doc.text(indent + constDecl));
                    } else {
                        result = result.append(Doc.text(","));
                        for (String comment : preComments) {
                            result = result.appendLine(Doc.text(commentIndent + normalizeComment(comment)));
                        }
                        result = result.appendLine(Doc.text(indent + constDecl));
                    }
                } else {
                    result = result.append(Doc.text(",")).appendLine(Doc.text(indent + constDecl));
                }
            }
        }
        return result;
    }

    /**
     * Build the constant declaration string including operator parameters.
     */
    private String buildConstantDeclaration(TreeNode node) {
        if (node.getKind() == 363) {
            TreeNode[] children = node.zero();
            if (children != null && children.length > 1) {
                StringBuilder sb = new StringBuilder();
                for (TreeNode child : children) {
                    if (child != null && child.getImage() != null) {
                        sb.append(TlaDocBuilder.getBestImage(child));
                    }
                }
                return sb.toString();
            } else if (children != null && children.length == 1) {
                return TlaDocBuilder.getBestImage(children[0]);
            }
        }
        return TlaDocBuilder.getBestImage(node);
    }

    private static String normalizeComment(String s) {
        return ConstructContext.normalizeCommentWhitespace(s, false);
    }
}
