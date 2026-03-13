package formatter.constructs.impl;


import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Handles THEOREM declarations.
 * <p>
 * Unnamed theorem (THEOREM expr):
 * zero[] = [THEOREM keyword, expression]
 * <p>
 * Named theorem (THEOREM Name == expr):
 * zero[] = [THEOREM keyword, name, ==, expression]
 */
public class TheoremConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "THEOREM";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.THEOREM.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length >= 2);

        var theoremKeyword = context.buildChild(z[0]);
        Doc proof = Doc.empty();

        if (z.length == 2 || z.length == 3) {
            // Unnamed theorem: THEOREM expr [proof]
            var expr = context.buildChild(z[1]);
            if (z.length == 3) {
                proof = Doc.line().append(context.buildChild(z[2]));
            }
            return Doc.group(
                    theoremKeyword.appendLineOrSpace(expr)
            ).indent(z[0].getImage().length() + 1).append(proof);
        } else {
            // Named theorem: THEOREM Name == expr [proof]
            assert z.length == 4 || z.length == 5;
            var name = context.buildChild(z[1]);
            var expr = context.buildChild(z[3]);
            if (z.length == 5) {
                proof = Doc.line().append(context.buildChild(z[4]));
            }
            return theoremKeyword
                    .appendSpace(name)
                    .appendSpace(Doc.text("=="))
                    .append(Doc
                            .group(Doc.lineOrSpace().append(expr))
                            .indent(indentSize))
                    .append(proof);
        }
    }
}