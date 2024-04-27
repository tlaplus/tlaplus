package tla2sany.parser;

/**
 * This used to be part of ParseException.java but was extracted to restore
 * the ability to auto-generate the files with JavaCC.
 */
public class ParseExceptionExtended extends ParseException {
  /**
   *  Shorter variation of ParseException.getMessage()
   */
  public static String getShortMessage(ParseException e) {
    int maxSize = 0;
    for (int i = 0; i < e.expectedTokenSequences.length; i++) {
      if (maxSize < e.expectedTokenSequences[i].length) {
        maxSize = e.expectedTokenSequences[i].length;
      }
    }
    String retval = "Encountered \"";
    Token tok = e.currentToken.next;

    for (int i = 0; i < maxSize; i++) {
      if (i != 0) retval += " ";
      if (tok.kind == 0) {
        retval += e.tokenImage[0];
        break;
      }
      retval += tok.image;
      //      retval += add_escapes(tok.image);
      tok = tok.next;
    }
    retval += "\" at line " + e.currentToken.next.beginLine + ", column " + e.currentToken.next.beginColumn
        + " and token \"" + e.add_escapes(e.currentToken.image != null ? e.currentToken.image : "") + "\" ";
    return retval;
  }
}

