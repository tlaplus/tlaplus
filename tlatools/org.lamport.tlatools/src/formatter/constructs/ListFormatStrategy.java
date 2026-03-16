package formatter.constructs;

/**
 * Strategies for formatting lists of items in TLA+ constructs.
 */
public enum ListFormatStrategy {
    
    /**
     * Always try to fit all items on a single line.
     * Example: "EXTENDS Naturals, TLC, Sequences"
     */
    SINGLE_LINE,
    
    /**
     * Break lines intelligently based on line width.
     * Uses prettier4j's line-or-space mechanism for optimal breaking.
     * Example: 
     * "EXTENDS Naturals, TLC, Sequences,
     *         FiniteSets, Integers"
     */
    SMART_BREAK,
    
    /**
     * Always break after each item.
     * Each item goes on its own line.
     * Example:
     * "EXTENDS 
     *  Naturals,
     *  TLC,
     *  Sequences"
     */
    ALWAYS_BREAK
}