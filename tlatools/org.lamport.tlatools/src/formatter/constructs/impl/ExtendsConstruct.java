package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.TlaDocBuilder;
import formatter.constructs.*;
import tla2sany.st.TreeNode;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Construct implementation for EXTENDS declarations.
 * Handles formatting of module import lists with smart line breaking.
 */
public class ExtendsConstruct extends AbstractDeclarationListConstruct {
    private static final Set<String> KEYWORDS = Set.of("EXTENDS");

    @Override
    protected Set<String> getKeywords() {
        return KEYWORDS;
    }

    @Override
    protected TreeNode[] getChildren(TreeNode node) {
        // EXTENDS only uses zero() children
        return node.zero();
    }

    @Override
    public String getName() {
        return "EXTENDS";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.EXTENDS.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        Doc prefix = context.buildChild(node.zero()[0]);
        List<TreeNode> moduleNodes = extractItemNodes(node);
        Map<Integer, String[]> commaComments = extractCommaPreComments(node);

        if (moduleNodes.isEmpty()) {
            return prefix;
        }

        boolean hasComments = !commaComments.isEmpty() || moduleNodes.stream()
                .anyMatch(n -> n.getPreComments() != null && n.getPreComments().length > 0);

        if (hasComments) {
            return formatWithComments(prefix, moduleNodes, commaComments);
        }

        List<String> modules = new ArrayList<>();
        for (TreeNode moduleNode : moduleNodes) {
            modules.add(TlaDocBuilder.getBestImage(moduleNode));
        }
        return new DeclarationListFormatter(context.getConfig(), "EXTENDS").format(prefix, modules);
    }

    private Doc formatWithComments(Doc prefix, List<TreeNode> moduleNodes, Map<Integer, String[]> commaComments) {
        Doc result = prefix;
        String indent = "        "; // 8 spaces to align under first module after "EXTENDS "

        for (int i = 0; i < moduleNodes.size(); i++) {
            TreeNode moduleNode = moduleNodes.get(i);
            String moduleName = TlaDocBuilder.getBestImage(moduleNode);
            String[] preComments = moduleNode.getPreComments();
            boolean isLast = (i == moduleNodes.size() - 1);

            if (i == 0) {
                if (preComments != null && preComments.length > 0) {
                    for (String comment : preComments) {
                        result = result.appendLine(Doc.text(indent + normalizeComment(comment)));
                    }
                    result = result.appendLine(Doc.text(indent + moduleName + (isLast ? "" : ",")));
                } else {
                    result = result.append(Doc.text(" " + moduleName + (isLast ? "" : ",")));
                }
            } else {
                if (preComments != null && preComments.length > 0) {
                    String normalizedFirst = normalizeComment(preComments[0]);
                    if (preComments.length == 1 && normalizedFirst.startsWith("\\*")) {
                        result = result.append(Doc.text(" " + normalizedFirst));
                    } else {
                        for (String comment : preComments) {
                            result = result.appendLine(Doc.text(indent + normalizeComment(comment)));
                        }
                    }
                    result = result.appendLine(Doc.text(indent + moduleName + (isLast ? "" : ",")));
                } else {
                    result = result.appendLine(Doc.text(indent + moduleName + (isLast ? "" : ",")));
                }
            }

            String[] postComments = commaComments.get(i + 1);
            if (postComments != null && postComments.length > 0) {
                String normalized = normalizeComment(postComments[0]);
                if (postComments.length == 1 && normalized.startsWith("\\*")) {
                    result = result.append(Doc.text(" " + normalized));
                } else {
                    for (String comment : postComments) {
                        result = result.append(Doc.text(" " + normalizeComment(comment)));
                    }
                }
            }
        }
        return result;
    }

    private static String normalizeComment(String s) {
        return ConstructContext.stripAndNormalizeComment(s);
    }
}