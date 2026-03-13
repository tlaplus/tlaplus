package formatter.constructs;

import com.opencastsoftware.prettier4j.Doc;
import tla2sany.st.TreeNode;

/**
 * Interface for all TLA+ language constructs that can be formatted.
 * This provides a plugin-like system for handling different TLA+ syntax elements.
 */
public interface TlaConstruct {

    /**
     * @return The name of this construct (e.g., "EXTENDS", "VARIABLES", "OPERATOR")
     */
    String getName();

    /**
     * @return SANY node kind that this construct can handle
     */
    int getSupportedNodeKind();

    /**
     * Build a Doc object for formatting this construct.
     *
     * @param node    The SANY tree node representing this construct
     * @param context Context object providing access to configuration and utilities
     * @return A Doc object for pretty printing
     */
    Doc buildDoc(TreeNode node, ConstructContext context, int indentSize);

}