package formatter.constructs;

import tla2sany.st.TreeNode;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * Registry for managing TLA+ construct handlers.
 * Provides efficient lookup of construct handlers by node kind.
 */
public class ConstructRegistry {
    private final Map<Integer, TlaConstruct> handlersByNodeKind;

    public ConstructRegistry() {
        this.handlersByNodeKind = new ConcurrentHashMap<>();
    }

    /**
     * Register a construct handler.
     *
     * @param construct The construct to register
     */
    public void register(TlaConstruct construct) {
        if (construct == null) {
            throw new IllegalArgumentException("Construct cannot be null");
        }
        synchronized (this) {
            handlersByNodeKind.put(construct.getSupportedNodeKind(), construct);
        }
    }

    /**
     * Find a construct handler for the given tree node.
     *
     * @param node The tree node to find a handler for
     * @return The best matching construct handler, or null if none found
     */
    public TlaConstruct findHandler(TreeNode node) {
        if (node == null) {
            return null;
        }
        return handlersByNodeKind.get(node.getKind());
    }
}