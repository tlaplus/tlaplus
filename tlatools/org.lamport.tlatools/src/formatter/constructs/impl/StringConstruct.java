package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Handles string literal nodes.
 * <p>
 * SANY stores strings with escape sequences already interpreted (e.g., "\\b" becomes "\b").
 * We need to re-escape them when outputting to produce valid TLA+ source.
 */
public class StringConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "STRING";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.STRING.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        // SANY stores the interpreted string content, so we need to re-escape it
        // to produce valid TLA+ source code
        String content = node.getImage();
        return Doc.text(escapeString(content));
    }

    /**
     * Escape a string for TLA+ output.
     * The input is a TLA+ string literal as stored by SANY (with quotes, but escape sequences interpreted).
     * The output is a valid TLA+ string literal with proper escaping.
     */
    private String escapeString(String s) {
        if (s == null || s.length() < 2) {
            return s;
        }

        // The string includes surrounding quotes, so we need to process the content
        // between them: "content"
        if (!s.startsWith("\"") || !s.endsWith("\"")) {
            return s;
        }

        String content = s.substring(1, s.length() - 1);
        StringBuilder result = new StringBuilder();
        result.append('"');

        for (int i = 0; i < content.length(); i++) {
            char c = content.charAt(i);
            switch (c) {
                case '\\':
                    result.append("\\\\");
                    break;
                case '"':
                    result.append("\\\"");
                    break;
                case '\t':
                    result.append("\\t");
                    break;
                case '\n':
                    result.append("\\n");
                    break;
                case '\r':
                    result.append("\\r");
                    break;
                case '\f':
                    result.append("\\f");
                    break;
                default:
                    result.append(c);
                    break;
            }
        }

        result.append('"');
        return result.toString();
    }
}
