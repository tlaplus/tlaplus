package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Handles module prefixes like "R!" in "R!Nat" where R is an INSTANCE alias.
 * The prefix includes the "!" separator.
 */
public class IdPrefixConstruct implements TlaConstruct {
    @Override
    public int getSupportedNodeKind() {
        return NodeKind.ID_PREFIX.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        String image = node.getHumanReadableImage();
        if (image == null || image.isEmpty()) {
            return Doc.empty();
        }
        Doc mainDoc = Doc.text(image);
        // Check descendants for preComments that need to be preserved.
        // Comments on module prefix identifiers (e.g., "EWD998" in "EWD998!op")
        // are attached to inner identifier nodes that would be skipped by Doc.text().
        return addDescendantComments(node, mainDoc);
    }

    private static Doc addDescendantComments(TreeNode node, Doc mainDoc) {
        TreeNode[][] childArrays = {node.zero(), node.one()};
        for (TreeNode[] children : childArrays) {
            if (children == null) continue;
            for (TreeNode child : children) {
                if (child.getPreComments() != null && child.getPreComments().length > 0) {
                    return ConstructContext.addComments(child, mainDoc);
                }
                Doc result = addDescendantComments(child, mainDoc);
                if (result != mainDoc) {
                    return result;
                }
            }
        }
        return mainDoc;
    }

    @Override
    public String getName() {
        return "N_IdPrefix";
    }
}
