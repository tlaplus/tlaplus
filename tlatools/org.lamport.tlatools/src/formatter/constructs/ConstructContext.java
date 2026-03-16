package formatter.constructs;

import com.opencastsoftware.prettier4j.Doc;
import formatter.FormatConfig;
import formatter.TlaDocBuilder;
import tla2sany.st.TreeNode;

import java.util.ArrayList;
import java.util.List;

/**
 * Context object that provides access to shared services and utilities
 * for construct implementations.
 */
public final class ConstructContext {

    private final FormatConfig config;
    private final TlaDocBuilder docBuilder;
    private final NodeAnalyzer nodeAnalyzer;

    public ConstructContext(FormatConfig config, TlaDocBuilder docBuilder) {
        this.config = config.copy();
        this.docBuilder = docBuilder;
        this.nodeAnalyzer = new NodeAnalyzer();
    }

    /**
     * @return A copy of the current format configuration
     */
    public FormatConfig getConfig() {
        return config.copy();
    }

    /**
     * Build a Doc for a child node using the main document builder.
     * This allows recursive building of nested constructs.
     *
     * @param child The child tree node
     * @return Doc object for the child node
     */
    public Doc buildChild(TreeNode child) {
        var childDoc = docBuilder.build(child);
        return addComments(child, childDoc);
    }

    public static Doc addComments(TreeNode node, Doc mainDoc) {
        String[] preComments = node.getPreComments();
        if (preComments == null || preComments.length == 0) {
            return mainDoc;
        }

        // Build comments, handling continuations properly.
        // SANY splits multi-line block comments at nested (* markers.
        // Continuation preComments (those not starting with (* or \*) should be
        // appended directly without adding a line break.
        Doc result = Doc.empty();
        boolean first = true;

        for (String comment : preComments) {
            boolean isContinuation = !isCommentStart(comment);
            String normalized = normalizeCommentWhitespace(comment, isContinuation);

            if (first) {
                result = Doc.text(normalized);
                first = false;
            } else if (isContinuation) {
                // Continuation: append directly without line break
                result = result.append(Doc.text(normalized));
            } else {
                // New comment: add line break first
                result = result.appendLine(Doc.text(normalized));
            }
        }

        // Add the main doc with a line break
        return result.appendLine(mainDoc);
    }

    /**
     * Check if a preComment string starts a new comment (vs being a continuation).
     * A new comment starts with (* (block) or \* (line).
     */
    private static boolean isCommentStart(String s) {
        // Skip leading whitespace to find the actual comment start
        int i = 0;
        while (i < s.length() && Character.isWhitespace(s.charAt(i))) {
            i++;
        }
        if (i >= s.length()) {
            return false;
        }
        // Check for block comment start (*
        if (i + 1 < s.length() && s.charAt(i) == '(' && s.charAt(i + 1) == '*') {
            return true;
        }
        // Check for line comment start \*
        return i + 1 < s.length() && s.charAt(i) == '\\' && s.charAt(i + 1) == '*';
    }

    /**
     * Normalize comment whitespace.
     * For new comments (starting with (* or \*): strip leading newlines only, preserve
     * indentation spaces. SANY stores the column indentation in preComment strings
     * (e.g., '\n    (*'), and stripping it changes the AST on re-parse.
     * For continuations: only strip trailing newlines, preserve leading whitespace.
     * Always preserve trailing spaces before the newline (SANY's AST preserves them).
     */
    public static String normalizeCommentWhitespace(String s, boolean isContinuation) {
        int start = 0;
        // Strip leading newlines only (not spaces/tabs) so column indentation is preserved
        if (!isContinuation) {
            while (start < s.length() && (s.charAt(start) == '\n' || s.charAt(start) == '\r')) {
                start++;
            }
        }
        // Strip trailing newlines only (preserve trailing spaces)
        int end = s.length();
        while (end > start && (s.charAt(end - 1) == '\n' || s.charAt(end - 1) == '\r')) {
            end--;
        }
        return s.substring(start, end);
    }

    /**
     * Normalize a comment by stripping all leading whitespace and trailing newlines.
     * Use this variant when re-indenting comments (the caller supplies its own indentation).
     */
    public static String stripAndNormalizeComment(String s) {
        int start = 0;
        while (start < s.length() && Character.isWhitespace(s.charAt(start))) {
            start++;
        }
        int end = s.length();
        while (end > start && (s.charAt(end - 1) == '\n' || s.charAt(end - 1) == '\r')) {
            end--;
        }
        return s.substring(start, end);
    }

    /**
     * Extract string values from a tree node's children.
     * Common utility for constructs that work with lists of identifiers.
     *
     * @param node The parent tree node
     * @return List of non-empty string values from valid child nodes
     */
    public List<String> extractStringList(TreeNode node) {
        return nodeAnalyzer.extractStrings(node);
    }

    /**
     * Check if a tree node is valid (not a placeholder).
     *
     * @param node The tree node to check
     * @return true if the node is valid
     */
    public boolean isValidNode(TreeNode node) {
        return nodeAnalyzer.isValid(node);
    }

    /**
     * Get preserved spacing after a node based on original source.
     *
     * @param node The tree node to get spacing after
     * @return Doc object for extra spacing/newlines
     */
    public Doc getSpacingAfter(TreeNode node, TreeNode next) {
        return docBuilder.getSpacingAfter(node, next);
    }

    /**
     * Helper class for common node analysis operations.
     */
    private static class NodeAnalyzer {
        /**
         * Check if a node is valid (has a real location, not a placeholder).
         */
        boolean isValid(TreeNode node) {
            if (node == null) {
                return false;
            }

            // SANY creates placeholder nodes with MAX_VALUE coordinates
            return node.getLocation() != null &&
                    node.getLocation().beginLine() != Integer.MAX_VALUE;
        }

        /**
         * Extract string values from a tree node, checking both zero() and one() arrays.
         */
        List<String> extractStrings(TreeNode node) {
            List<String> result = new ArrayList<>();

            // Check both zero() and one() arrays for child nodes
            TreeNode[] children = null;
            if (node.one() != null && node.one().length > 0) {
                children = node.one();
            } else if (node.zero() != null && node.zero().length > 0) {
                children = node.zero();
            }

            if (children != null) {
                for (TreeNode child : children) {
                    if (isValid(child) && child.getImage() != null) {
                        String image = TlaDocBuilder.getBestImage(child);
                        // Skip common separators and keywords
                        var toSkip = List.of(",", "EXTENDS", "VARIABLES", "VARIABLE", "CONSTANT", "CONSTANTS");
                        if (toSkip.contains(image)) {
                            continue;
                        }
                        result.add(image);
                    }
                }
            }

            return result;
        }
    }
}