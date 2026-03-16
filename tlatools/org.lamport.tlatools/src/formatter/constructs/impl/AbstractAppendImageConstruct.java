package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.TlaDocBuilder;
import formatter.constructs.ConstructContext;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.List;
import java.util.Optional;

public abstract class AbstractAppendImageConstruct implements TlaConstruct {
    public abstract int getSupportedNodeKind();

    public abstract String getName();

    @Override
    public final Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        var o = node.one();
        if ((z == null || z.length == 0) && (o == null || o.length == 0)) {
            return Doc.text(TlaDocBuilder.getBestImage(node));
        }
        return Optional.ofNullable(buildChildren(context, z)).orElse(buildChildren(context, o));
    }

    private Doc buildChildren(ConstructContext context, TreeNode[] c) {
        if (c == null) {
            return null;
        }
        var childDoc = context.buildChild(c[0]);
        for (int i = 1; i < c.length; i++) {
            var nextChildDoc = context.buildChild(c[i]);
            if (childDoc == Doc.empty()) {
                childDoc = nextChildDoc;
            } else if (nextChildDoc != null && nextChildDoc != Doc.empty()) {
                // don't add space before or after , ] ) } [ ( {
                var shouldSkipSpace = isShouldSkipSpace(c, i);
                if (shouldSkipSpace) {
                    childDoc = childDoc.append(nextChildDoc);
                } else {
                    childDoc = childDoc.appendSpace(nextChildDoc);
                }
            }
        }
        return childDoc;
    }

    private static boolean isShouldSkipSpace(TreeNode[] c, int i) {
        var skipSpace = List.of(",", "]", ")", "}", "(", "[", "{");
        var prevImage = c[i - 1].getHumanReadableImage();
        var currImage = c[i].getHumanReadableImage();
        // Skip space after module prefix (e.g., "R!" in "R!Nat")
        // module prefix like R!
        return skipSpace.contains(currImage)
                || skipSpace.contains(prevImage) // to format `f(_)`
                || (prevImage != null && prevImage.endsWith("!"));
    }
}
