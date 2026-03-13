package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import tla2sany.st.TreeNode;

import java.util.ArrayList;
import java.util.List;

/**
 * Shared utilities for constructs that format bracketed, comma-separated lists
 * (SetEnumerate, Tuple, RcdConstructor, etc.).
 */
final class BracketedListHelper {

    private BracketedListHelper() {}

    /**
     * Collect element Docs from children between the first and last nodes (brackets),
     * skipping commas.
     */
    static List<Doc> collectElements(TreeNode[] children, ConstructContext context) {
        List<Doc> elements = new ArrayList<>();
        for (int i = 1; i < children.length - 1; i++) {
            TreeNode child = children[i];
            assert (child != null);
            if (",".equals(child.getHumanReadableImage())) {
                continue;
            }
            elements.add(context.buildChild(child));
        }
        return elements;
    }

    /**
     * Join element Docs with comma + lineOrSpace separators.
     */
    static Doc joinWithComma(List<Doc> elements) {
        Doc content = elements.get(0);
        for (int i = 1; i < elements.size(); i++) {
            content = content.append(Doc.text(",")).appendLineOrSpace(elements.get(i));
        }
        return content;
    }

    /**
     * Wrap content in brackets: open + space + content (indented) + lineOrSpace + close.
     */
    static Doc wrapInBrackets(Doc openDoc, Doc content, Doc closeDoc, int indentWidth) {
        return Doc.group(
                openDoc
                        .appendSpace(content.indent(indentWidth))
                        .appendLineOrSpace(closeDoc)
        );
    }
}
