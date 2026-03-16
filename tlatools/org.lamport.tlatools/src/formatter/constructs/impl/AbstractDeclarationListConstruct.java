package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.FormatConfig;
import formatter.TlaDocBuilder;
import formatter.constructs.BaseConstructFormatter;
import formatter.constructs.ListFormatStrategy;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.*;

/**
 * Base class for declaration list constructs (CONSTANTS, VARIABLES, EXTENDS).
 * Provides shared utilities for extracting item nodes, comma comments,
 * and formatting comma-separated declaration lists.
 */
public abstract class AbstractDeclarationListConstruct implements TlaConstruct {

    /**
     * Keywords to skip when extracting item nodes (e.g., "CONSTANTS", "CONSTANT").
     */
    protected abstract Set<String> getKeywords();

    /**
     * Get the children array to iterate over.
     * Default checks one() first, then zero(). Override to change (e.g., EXTENDS uses only zero()).
     */
    protected TreeNode[] getChildren(TreeNode node) {
        if (node.one() != null && node.one().length > 0) {
            return node.one();
        }
        if (node.zero() != null && node.zero().length > 0) {
            return node.zero();
        }
        return null;
    }

    /**
     * Get the display name for an item node. Override for special handling (e.g., IDENT_DECL).
     */
    protected String getItemName(TreeNode node) {
        return TlaDocBuilder.getBestImage(node);
    }

    /**
     * Extract item TreeNodes from the declaration, skipping commas and keywords.
     */
    protected List<TreeNode> extractItemNodes(TreeNode node) {
        List<TreeNode> result = new ArrayList<>();
        TreeNode[] children = getChildren(node);
        if (children == null) return result;

        Set<String> keywords = getKeywords();
        for (TreeNode child : children) {
            if (isValidNode(child) && child.getImage() != null) {
                String image = child.getHumanReadableImage();
                if (!",".equals(image) && !keywords.contains(image)) {
                    result.add(child);
                }
            }
        }
        return result;
    }

    /**
     * Extract preComments from comma separator nodes.
     * Returns a map from item index to the comma preComments that should be
     * treated as post-comments of the item at that index.
     */
    protected Map<Integer, String[]> extractCommaPreComments(TreeNode node) {
        Map<Integer, String[]> result = new HashMap<>();
        TreeNode[] children = getChildren(node);
        if (children == null) return result;

        Set<String> keywords = getKeywords();
        int itemIndex = -1;
        for (TreeNode child : children) {
            if (!isValidNode(child) || child.getImage() == null) continue;
            String image = child.getHumanReadableImage();
            if (",".equals(image)) {
                String[] comments = child.getPreComments();
                if (comments != null && comments.length > 0) {
                    result.put(itemIndex + 1, comments);
                }
            } else if (!keywords.contains(image)) {
                itemIndex++;
            }
        }
        return result;
    }

    protected static boolean isValidNode(TreeNode node) {
        return node != null &&
                node.getLocation() != null &&
                node.getLocation().beginLine() != Integer.MAX_VALUE;
    }

    /**
     * Unified formatter for declaration lists (without comments).
     * Replaces ConstantsFormatter, VariableFormatter, and ExtendsFormatter.
     */
    protected static class DeclarationListFormatter extends BaseConstructFormatter<String> {
        private final String constructName;

        public DeclarationListFormatter(FormatConfig config, String constructName) {
            super(config);
            this.constructName = constructName;
        }

        public Doc format(Doc prefix, List<String> items) {
            if (items.isEmpty()) {
                return Doc.empty();
            }
            ListFormatStrategy strategy = determineStrategy(constructName, items.size());
            return formatList(items, prefix, stringFormatter(), strategy);
        }

        private ListFormatStrategy determineStrategy(String name, int itemCount) {
            if (itemCount <= 3) {
                return ListFormatStrategy.SINGLE_LINE;
            } else {
                return config.getConstructSetting(
                        name, "breakStrategy", ListFormatStrategy.SMART_BREAK);
            }
        }
    }
}
