package tla2sany.parser;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.NoSuchElementException;

/**
 * Handling vertically-aligned conjunction & disjunction lists (called
 * junction lists for short) is one of the most difficult parts of parsing
 * TLA⁺. This class keeps track of the current junction list parsing context
 * by storing a stack of the nested junction lists, their start columns, and
 * their types.
 */
class JunctionListContext {

  /**
   * Enumeration of junction list types.
   */
  private enum JunctionListType {

    /**
     * Conjunction lists, which use the /\ or ∧ bullet symbols.
     */
    CONJUNCTION,

    /**
     * Disjunction lists, which use the \/ or ∨ bullet symbols.
     */
    DISJUNCTION
  }

  /**
   * A class holding information about a junction list.
   */
  private class JunctionListInfo {

    /**
     * The type of the junction list, conjunction or disjunction.
     */
    public final JunctionListType Type;

    /**
     * The column on which the junction list starts. This counts codepoints,
     * not bytes, and is the number of codepoints before the start of the
     * bullet symbol (codepoints can be thought of as roughly corresponding
     * to the concept of "character" in the Unicode world, although even this
     * is not quite correct due to the concept of multiple modifier symbols
     * combining to form a single displayed "grapheme cluster", which TLA⁺
     * does not support). For example, if x denotes a space, then:
     *
     * xxx/\
     *
     * will have column value 3. Before Unicode support was added, this value
     * recorded the column on which the symbol *ended* (so the above example
     * would have column value 4) but this had to be changed to use the start
     * column since /\ and ∧ have different character lengths.
     *
     * Codepoints need to be counted instead of bytes, because the addition
     * of Unicode symbols means that displayed characters can require
     * multiple bytes. So for example, the ∧ symbol is Unicode codepoint
     * U+2227 (hex) which is 8743 in decimal. This is above the 128 value
     * limit to be represented in a single byte as with ASCII. In fact, it
     * takes 14 bits to represent 8743. Under variable-width UTF-8 encoding,
     * ∧ requires three bytes to store. So a nested conjunction list like:
     *
     * ∧ ∧ x
     *   ∧ y
     *
     * requires us to count codepoints, not bytes, because if you count bytes
     * then the second conjunct will appear to be two bytes below the first
     * conjunct and will thus terminate the conjunction list instead of
     * continuing it.
     */
    public final int Column;

    /**
     * Constructs a new instance of the {@link JunctionListInfo} class.
     *
     * @param type The junction list type.
     * @param column The junction list alignment column.
     */
    public JunctionListInfo(JunctionListType type, int column) {
      this.Type = type;
      this.Column = column;
    }
  }

  /**
   * A stack tracking the nested junction list context.
   */
  private final Deque<JunctionListInfo> stack = new ArrayDeque<JunctionListInfo>();

  /**
   * Creates an empty {@link JunctionListContext}.
   */
  public JunctionListContext() { }

  /**
   * Determines whether the given {@link TLAplusParserConstants} value is a
   * junction list bullet token.
   *
   * @param kind The token kind, a {@link TLAplusParserConstants} value.
   * @return Whether the given token is a junction list bullet token.
   */
  private static boolean isJunctionListBulletToken(int kind) {
    return TLAplusParserConstants.AND == kind
      || TLAplusParserConstants.OR == kind;
  }

  /**
   * Resolves the given {@link TLAplusParserConstants} token value to either
   * a conjunction or disjunction list type.
   *
   * @param kind The token kind, a {@link TLAplusParserConstants} value.
   * @return Either a conjunction or disjunction list.
   * @throws {@link IllegalArgumentException} if invalid junction list token.
   */
  private static JunctionListType asJunctionListType(int kind) throws IllegalArgumentException {
    switch (kind) {
      case TLAplusParserConstants.AND:
        return JunctionListType.CONJUNCTION;
      case TLAplusParserConstants.OR:
        return JunctionListType.DISJUNCTION;
      default:
        throw new IllegalArgumentException(Integer.toString(kind));
    }
  }

  /**
   * Pushes details of a new junction list onto the stack, indicating the
   * start of a new junction list.
   *
   * @param column The start column of the new junction list.
   * @param kind The token kind, a {@link TLAplusParserConstants} value.
   * @throws {@link IllegalArgumentException} if invalid junction list token.
   */
  public void startNewJunctionList(int column, int kind) throws IllegalArgumentException {
    this.stack.push(new JunctionListInfo(asJunctionListType(kind), column));
  }

  /**
   * Removes the topmost junction list record, indicating the end of the
   * current junction list.
   *
   * @throws {@link NoSuchElementException} if not inside a junction list.
   */
  public void terminateCurrentJunctionList() throws NoSuchElementException {
    this.stack.pop();
  }

  /**
   * Returns true if the given token start column and kind match the current
   * junction alignment and type, indicating it is another bullet in the
   * current junction list. If there are no currently active junction lists
   * then this is always false. This function is not necessarily only called
   * with valid conjunction or disjunction token kinds.
   *
   * @param column The token start column.
   * @param kind The token kind, a {@link TLAplusParserConstants} value.
   * @return True if token is another bullet in the current junction list.
   */
  public boolean isNewBullet(int column, int kind) {
    JunctionListInfo headOrNull = this.stack.peekFirst();
    return
      headOrNull != null
      && isJunctionListBulletToken(kind)
      && headOrNull.Column == column
      && headOrNull.Type == asJunctionListType(kind);
  }

  /**
   * Returns true if the given token start column is to the right of the
   * current junction list alignment, indicating it is probably contained
   * within the junction list (with the exception of several keywords or
   * definition types which terminate junction lists no matter what). If
   * there is no currently active junction list then this is always true.
   *
   * @param column The start column of some token.
   * @return True if strictly greater than current junction list alignment.
   */
  public boolean isAboveCurrent(int column) {
    JunctionListInfo headOrNull = this.stack.peekFirst();
    return headOrNull == null || headOrNull.Column < column;
  }
}
