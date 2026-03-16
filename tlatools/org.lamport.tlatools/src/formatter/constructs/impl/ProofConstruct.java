package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.ArrayList;
import java.util.List;

/**
 * Handles TLAPS proof blocks (N_Proof and N_InnerProof).
 * Proof steps within a block must be separated by line breaks.
 */
public class ProofConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "N_Proof";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.PROOF.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        return buildStepsWithLineBreaks(node, context);
    }

    private static List<Doc> collectChildren(TreeNode node, ConstructContext context) {
        List<Doc> children = new ArrayList<>();
        if (node.zero() != null) {
            for (TreeNode child : node.zero()) {
                children.add(context.buildChild(child));
            }
        }
        if (node.one() != null) {
            for (TreeNode child : node.one()) {
                children.add(context.buildChild(child));
            }
        }
        return children;
    }

    private static Doc buildStepsWithLineBreaks(TreeNode node, ConstructContext context) {
        List<Doc> children = collectChildren(node, context);
        if (children.isEmpty()) {
            return Doc.empty();
        }
        Doc result = children.get(0);
        for (int i = 1; i < children.size(); i++) {
            result = result.appendLine(children.get(i));
        }
        return result;
    }

    /** Check if a node or its first descendant has pre-comments */
    private static boolean hasPreComments(TreeNode node) {
        if (node == null) return false;
        if (node.getPreComments() != null && node.getPreComments().length > 0) return true;
        if (node.zero() != null && node.zero().length > 0) return hasPreComments(node.zero()[0]);
        if (node.one() != null && node.one().length > 0) return hasPreComments(node.one()[0]);
        return false;
    }

    /** Handles N_InnerProof (374) - nested proof block */
    public static class InnerProofConstruct implements TlaConstruct {
        @Override
        public String getName() { return "N_InnerProof"; }

        @Override
        public int getSupportedNodeKind() { return NodeKind.INNER_PROOF.getId(); }

        @Override
        public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
            return buildStepsWithLineBreaks(node, context);
        }
    }

    /** Handles N_ProofStep (406) - wraps a step label with its content */
    public static class ProofStepConstruct implements TlaConstruct {
        @Override
        public String getName() { return "N_ProofStep"; }

        @Override
        public int getSupportedNodeKind() { return NodeKind.PROOF_STEP.getId(); }

        @Override
        public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
            List<Doc> children = collectChildren(node, context);
            if (children.isEmpty()) return Doc.empty();
            // First children are the step content (label + assertion),
            // last child is the proof (BY/OBVIOUS/inner proof).
            Doc result = children.get(0);
            for (int i = 1; i < children.size() - 1; i++) {
                result = result.appendSpace(children.get(i));
            }
            if (children.size() > 1) {
                Doc proof = children.get(children.size() - 1);
                // Get last raw child to check its kind
                TreeNode[] zero = node.zero();
                TreeNode lastChild = zero != null && zero.length > 0 ? zero[zero.length - 1] : null;
                boolean isNestedProof = lastChild != null &&
                        (lastChild.getKind() == NodeKind.INNER_PROOF.getId() ||
                         lastChild.getKind() == NodeKind.PROOF.getId());
                if (isNestedProof) {
                    // Inner proofs always go on new line indented
                    result = result.append(Doc.line().append(proof).indent(indentSize));
                } else if (hasPreComments(lastChild)) {
                    // Terminal proof has comments -- always new line to preserve them
                    result = result.append(Doc.line().append(proof).indent(indentSize));
                } else if (hasMultiLineStepContent(zero)) {
                    // Step content contains multi-line constructs (e.g. PICK with conj list)
                    result = result.append(Doc.line().append(proof).indent(indentSize));
                } else {
                    // Terminal proofs (OBVIOUS/BY) prefer same line if they fit
                    result = Doc.group(result.append(
                            Doc.lineOrSpace().append(proof).indent(indentSize)));
                }
            }
            return result;
        }

        /** Check if step content nodes produce multi-line output (e.g. PICK with conj/disj body) */
        private static boolean hasMultiLineStepContent(TreeNode[] zero) {
            if (zero == null) return false;
            for (int i = 0; i < zero.length - 1; i++) {
                if (containsConjOrDisjList(zero[i])) return true;
            }
            return false;
        }

        /** Recursively check if a node or its direct children contain a conjunction/disjunction list */
        private static boolean containsConjOrDisjList(TreeNode node) {
            if (node == null) return false;
            int kind = node.getKind();
            if (kind == NodeKind.CONJ_LIST.getId() || kind == NodeKind.DISJ_LIST.getId()) return true;
            if (node.zero() != null) {
                for (TreeNode child : node.zero()) {
                    if (containsConjOrDisjList(child)) return true;
                }
            }
            return false;
        }
    }
}
