package formatter;

import tla2sany.st.TreeNode;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Compares two SANY parse trees for structural equivalence.
 * Used to verify that formatting preserves the AST structure.
 */
public final class AstComparator {

    private AstComparator() {}

    /**
     * Result of an AST comparison. Contains mismatch details if the trees differ.
     */
    public static final class Result {
        private final boolean match;
        private final String description;
        private final List<String> nodePath;

        private Result(boolean match, String description, List<String> nodePath) {
            this.match = match;
            this.description = description;
            this.nodePath = nodePath;
        }

        /** Creates a failure result for cases where re-parsing itself fails. */
        public Result(String description) {
            this(false, description, Collections.emptyList());
        }

        static Result ok() {
            return new Result(true, null, Collections.emptyList());
        }

        static Result mismatch(String description, List<String> path) {
            return new Result(false, description, path);
        }

        public boolean isMatch() {
            return match;
        }

        public String getDescription() {
            return description;
        }

        /** Path from root to the mismatched node, e.g. ["Module", "OpDef", "InfixExpr"]. */
        public List<String> getNodePath() {
            return Collections.unmodifiableList(nodePath);
        }

        public String formatDiagnostic() {
            if (match) return "ASTs match.";
            StringBuilder sb = new StringBuilder();
            sb.append("AST verification failed:\n");
            sb.append("  ").append(description).append("\n");
            sb.append("  Node path: ").append(String.join(" -> ", nodePath)).append("\n");
            return sb.toString();
        }
    }

    /**
     * Compare two parse trees for structural equivalence.
     * Compares node kinds, zero/one children, and pre-comments.
     */
    public static Result compare(TreeNode original, TreeNode formatted) {
        List<String> path = new ArrayList<>();
        return compareRecursive(original, formatted, path);
    }

    private static Result compareRecursive(TreeNode n1, TreeNode n2, List<String> path) {
        String nodeLabel = nodeLabel(n1);
        path.add(nodeLabel);

        // Compare zero() children
        if (n1.zero() != null) {
            if (n2.zero() == null) {
                return Result.mismatch(
                        "Node zero[] is null in formatted AST but not in original. Node: " + n1.getImage(),
                        new ArrayList<>(path));
            }
            if (n1.zero().length != n2.zero().length) {
                return Result.mismatch(
                        "Node zero[] length mismatch: expected " + n1.zero().length
                                + " but found " + n2.zero().length
                                + ". Node: " + n1.getImage(),
                        new ArrayList<>(path));
            }
            for (int i = 0; i < n1.zero().length; i++) {
                Result childResult = compareRecursive(n1.zero()[i], n2.zero()[i], path);
                if (!childResult.isMatch()) {
                    return childResult;
                }
            }
        }

        // Compare one() children
        if (n1.one() != null) {
            if (n2.one() == null) {
                return Result.mismatch(
                        "Node one[] is null in formatted AST but not in original. Node: " + n1.getImage(),
                        new ArrayList<>(path));
            }
            if (n1.one().length != n2.one().length) {
                return Result.mismatch(
                        "Node one[] length mismatch: expected " + n1.one().length
                                + " but found " + n2.one().length
                                + ". Node: " + n1.getImage(),
                        new ArrayList<>(path));
            }
            for (int i = 0; i < n1.one().length; i++) {
                Result childResult = compareRecursive(n1.one()[i], n2.one()[i], path);
                if (!childResult.isMatch()) {
                    return childResult;
                }
            }
        }

        // Compare pre-comments
        Result commentResult = compareComments(n1, n2, path);
        if (!commentResult.isMatch()) {
            return commentResult;
        }

        // Compare node kind
        if (n1.getKind() != n2.getKind()) {
            return Result.mismatch(
                    "Node kind mismatch: expected " + n1.getKind() + " (" + n1.getImage() + ")"
                            + " but found " + n2.getKind() + " (" + n2.getImage() + ")",
                    new ArrayList<>(path));
        }

        path.remove(path.size() - 1);
        return Result.ok();
    }

    private static Result compareComments(TreeNode n1, TreeNode n2, List<String> path) {
        boolean has1 = n1.getPreComments() != null && n1.getPreComments().length > 0;
        boolean has2 = n2.getPreComments() != null && n2.getPreComments().length > 0;
        if (has1 != has2) {
            return Result.mismatch(
                    "Comment presence mismatch on node: " + n1.getHumanReadableImage()
                            + ". Expected comments: " + has1 + ", found: " + has2,
                    new ArrayList<>(path));
        }
        if (has1) {
            if (n1.getPreComments().length != n2.getPreComments().length) {
                return Result.mismatch(
                        "Comment count mismatch on node: " + n1.getHumanReadableImage()
                                + ". Expected " + n1.getPreComments().length
                                + " but found " + n2.getPreComments().length,
                        new ArrayList<>(path));
            }
            for (int i = 0; i < n1.getPreComments().length; i++) {
                if (!n1.getPreComments()[i].equals(n2.getPreComments()[i])) {
                    return Result.mismatch(
                            "Comment content mismatch on node: " + n1.getHumanReadableImage()
                                    + ". Expected: \"" + n1.getPreComments()[i]
                                    + "\" but found: \"" + n2.getPreComments()[i] + "\"",
                            new ArrayList<>(path));
                }
            }
        }
        return Result.ok();
    }

    private static String nodeLabel(TreeNode node) {
        String hri = node.getHumanReadableImage();
        if (hri != null && !hri.isEmpty()) {
            return hri + " (kind=" + node.getKind() + ")";
        }
        String image = node.getImage();
        if (image != null && !image.isEmpty()) {
            return image + " (kind=" + node.getKind() + ")";
        }
        return "kind=" + node.getKind();
    }
}
