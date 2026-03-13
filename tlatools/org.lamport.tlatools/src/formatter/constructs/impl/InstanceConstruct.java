package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Construct implementation for INSTANCE declarations.
 * Handles both LOCAL INSTANCE and regular INSTANCE.
 * <p>
 * LOCAL INSTANCE has node kind 375 (N_Instance) and contains a child
 * with kind 376 (N_NonLocalInstance).
 */
public class InstanceConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "INSTANCE";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.INSTANCE.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        // N_Instance (375) for LOCAL INSTANCE
        // Structure: zero[0]=LOCAL keyword, one[0]=N_NonLocalInstance child
        Doc result = null;

        // Process zero() children (e.g., LOCAL keyword)
        TreeNode[] zero = node.zero();
        if (zero != null) {
            for (TreeNode child : zero) {
                if (context.isValidNode(child)) {
                    Doc childDoc = context.buildChild(child);
                    result = result == null ? childDoc : result.appendSpace(childDoc);
                }
            }
        }

        // Process one() children (e.g., N_NonLocalInstance)
        TreeNode[] one = node.one();
        if (one != null) {
            for (TreeNode child : one) {
                if (context.isValidNode(child)) {
                    Doc childDoc = context.buildChild(child);
                    result = result == null ? childDoc : result.appendSpace(childDoc);
                }
            }
        }

        return result != null ? result : Doc.empty();
    }

    /**
     * Handles non-local INSTANCE (kind 376).
     * This is INSTANCE ModuleName [WITH substitutions]
     */
    public static class NonLocalInstanceConstruct implements TlaConstruct {
        @Override
        public String getName() {
            return "NON_LOCAL_INSTANCE";
        }

        @Override
        public int getSupportedNodeKind() {
            return NodeKind.NON_LOCAL_INSTANCE.getId();
        }

        @Override
        public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
            // N_NonLocalInstance (376) for INSTANCE ModuleName [WITH ...]
            TreeNode[] children = node.zero();
            if (children == null || children.length == 0) {
                children = node.one();
            }

            if (children == null || children.length == 0) {
                return Doc.text(node.getHumanReadableImage());
            }

            // Build all children with comments preserved
            Doc result = null;
            for (TreeNode child : children) {
                if (context.isValidNode(child)) {
                    Doc childDoc = context.buildChild(child);
                    result = result == null ? childDoc : result.appendSpace(childDoc);
                }
            }

            return result != null ? result : Doc.empty();
        }
    }
}
