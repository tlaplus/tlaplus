package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Handles proof DEFINE steps (N_DefStep).
 * <p>
 * Structure: zero[] = [DEFINE keyword, def1, def2, ...]
 * Each definition after the first goes on a new line, aligned under the first.
 */
public class DefStepConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "N_DefStep";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.DEF_STEP.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        if (z == null || z.length == 0) {
            return Doc.empty();
        }

        // Implicit DEFINE: z[] = [def1, def2, ...] (no DEFINE keyword)
        // Explicit DEFINE: z[] = [DEFINE keyword, def1, def2, ...]
        boolean hasKeyword = z[0].getImage().equals("DEFINE");
        int firstDef = hasKeyword ? 1 : 0;

        if (firstDef >= z.length) {
            // DEFINE keyword with no definitions - just render keyword
            return context.buildChild(z[0]);
        }

        Doc defs = context.buildChild(z[firstDef]);
        for (int i = firstDef + 1; i < z.length; i++) {
            defs = defs.appendLine(context.buildChild(z[i]));
        }

        if (hasKeyword) {
            Doc keyword = context.buildChild(z[0]);
            return keyword.appendSpace(defs.indent(z[0].getImage().length() + 1));
        }
        return defs;
    }
}
