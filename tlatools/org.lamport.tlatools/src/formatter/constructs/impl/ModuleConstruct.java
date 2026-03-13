package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.Arrays;
import java.util.stream.Collectors;

/**
 * Construct implementations for module structure elements.
 */
public class ModuleConstruct {

    /**
     * Handles the main MODULE node.
     */
    public static class ModuleMainConstruct implements TlaConstruct {

        @Override
        public String getName() {
            return "MODULE";
        }

        @Override
        public int getSupportedNodeKind() {
            return NodeKind.MODULE.getId();
        }

        @Override
        public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
            if (node.zero() == null || node.zero().length == 0) {
                return Doc.empty();
            }

            Doc p = null;
            TreeNode[] children = node.zero();

            // Process all module parts
            for (int i = 0; i < children.length; i++) {
                TreeNode child = children[i];
                if (context.isValidNode(child)) {
                    Doc childDoc = context.buildChild(child);
                    if (childDoc.equals(Doc.empty())) {
                        continue;
                    }
                    p = p == null ? childDoc : p.appendLine(childDoc);

                    if (i == children.length - 1) {
                        continue;
                    }
                    // Add preserved spacing after this node (except for the last one)
                    Doc spacing = context.getSpacingAfter(child, children[i + 1]);
                    if (spacing != null) {
                        p = p.appendLine(spacing);
                    }
                }
            }

            return p;
        }
    }

    /**
     * Handles BEGIN_MODULE (module header).
     */
    public static class BeginModuleConstruct implements TlaConstruct {

        @Override
        public String getName() {
            return "BEGIN_MODULE";
        }

        @Override
        public int getSupportedNodeKind() {
            return NodeKind.BEGIN_MODULE.getId();
        }

        @Override
        public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
            var z = node.zero();
            assert (z != null && z.length > 2);
            var zDocs = Arrays.stream(z).map(context::buildChild).collect(Collectors.toList());
            // todo: we could add a flag to rewrite this to ---- MODULE m ----
            var prefixDashes = zDocs.get(0);
            var moduleName = zDocs.get(1);
            var suffixDashes = zDocs.get(2);
            return prefixDashes.appendSpace(moduleName).appendSpace(suffixDashes);
        }
    }

    /**
     * Handles END_MODULE (module footer).
     */
    public static class EndModuleConstruct implements TlaConstruct {

        @Override
        public String getName() {
            return "END_MODULE";
        }

        @Override
        public int getSupportedNodeKind() {
            return NodeKind.END_MODULE.getId();
        }

        @Override
        public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
            return context.buildChild(node.zero()[0]);
        }
    }

    /**
     * Handles BODY (module body content).
     */
    public static class BodyConstruct extends ModuleMainConstruct {

        @Override
        public String getName() {
            return "BODY";
        }

        @Override
        public int getSupportedNodeKind() {
            return NodeKind.BODY.getId();
        }
    }
}