/***************************************************************************
* CLASS PcalTranslate                                                      *
* last modified on Mon 20 Mar 2006 at  9:04:28 PST by lamport              *
*      modified on Fri  9 Sep 2005 at 20:58:27 UT by keith                 *
*                                                                          *
* Given an AST, "explode" it: generate a new AST that has all Call,        *
*   Return, CallReturn, GoTo and While replaced by variable, stack and     *
*   pc manipulation; add explicit pc testing and pc setting for control    *
*   flow; replace LabelIf with LabeledStmt and control flow                *
*   implementation. The exploded AST maintains the structure except        *
*   that once down to the LabeledStmt level, it is flat. The only depth    *
*   is introduced by the If statement (since this depth is reflected in    *
*   the generated TLA+ code).                                              *
*                                                                          *
* LL comment added 25 Jan 2006.  I don't understand what the preceding     *
* sentence means.  I presume that Either should be added as a              *
* "depth-introducing" statement.  But what about a With, since Withs can   *
* also be nested?                                                          *
*                                                                          *
*      AST Explode (AST ast, PcalSymTab symtab)                            *
*                                                                          *
*   There are a few other public methods that can be used to generate      *
*   snippets of TLAExpr. I only use them here.                             *
****************************************************************************/

package pcal;
import java.util.Vector;

import pcal.exception.PcalTranslateException;

public class PcalTranslate {

    private static PcalSymTab st = null;  /* Set by invocation of Explode */
    
    /**
     *  The following field added by LL on 7 June 2010 to allow return statements
     *  to be used in macros.  It is initialized to null by Explode and is
     *  set and reset by ExplodeProcedure so it equals the name of the current
     *  procedure iff Exploding statements within a procedure.
     *  
     *  See the comments for ExplodeReturn for more details.
     *  
     */
    private static String currentProcedure;  


    /*************************************************************************
     * Routines for constructing snippets of +cal code                       *
     *************************************************************************/

    public static Vector DiscardLastElement(Vector v) {
        if (v.size() > 0) v.remove(v.size() - 1);
        return v;
    }

    public static Vector Singleton(Object obj) {
        /*********************************************************************
         * If we think of a vector as a sequence, then this returns <<obj>>. *
         *********************************************************************/
        Vector result = new Vector() ;
        result.addElement(obj) ;
        return result; 
    }
 
    public static Vector Pair(Object obj1, Object obj2) {
        /*********************************************************************
         * If we think of a vector as a sequence, then this returns          *
         * << obj1,  obj2 >>.                                                *
         *********************************************************************/
        Vector result = new Vector() ;
        result.addElement(obj1) ;
        result.addElement(obj2) ;
        return result; 
    }

    public static Vector Triple(Object obj1, Object obj2, Object obj3) {
        /*********************************************************************
         * If we think of a vector as a sequence, then this returns          *
         * << obj1,  obj2, obj3 >>.                                          *
         *********************************************************************/
        Vector result = new Vector() ;
        result.addElement(obj1) ;
        result.addElement(obj2) ;
        result.addElement(obj3) ;
        return result; 
    }

    public static Vector Singleton2(Object obj) {
        /*********************************************************************
         * If we think of a vector as a sequence, then this returns          *
         * << <<obj>> >>.                                                    *
         *********************************************************************/
        return Singleton(Singleton(obj));
    } 

    public static class BoolObj {
      /*********************************************************************
      * We need to pass a boolean as an element of a triple.  But the      *
      * brain-damaged Java language makes that impossible.  While we can   *
      * put booleans in a vector, there's no way to get them out.  We can  *
      * only extract objects from a vector.  So we define an class         *
      * BoolObj of objects containing a boolean val field.  The default    *
      * object has val field equal to true.                                *
      *********************************************************************/
      boolean val = true ; }

    public static BoolObj BO(boolean v) {
      /*********************************************************************
      * What I want to do is define a constructor for the BoolObj class    *
      * with an argument that is the value of the val field.  But I don't  *
      * remember how to do that and don't have access to any Java          *
      * documentation, so I'm defining BO to be that constructor.          *
      *********************************************************************/
      BoolObj res = new BoolObj() ;
      res.val = v ;
      return res ;
     }

    public static TLAToken StringToken(String str) {
        /*********************************************************************
         * Returns a new STRING token with string str.                       *
         *********************************************************************/
        TLAToken result = new TLAToken() ;
        result.string = str ;
        result.type   = TLAToken.STRING ;
        return result ;
      }

    public static TLAToken AddedToken(String str) {
        /*********************************************************************
         * Returns a new ADDED token with string str.                       *
         *********************************************************************/
        TLAToken result = new TLAToken() ;
        result.string = str ;
        result.type   = TLAToken.ADDED ;
        return result ;
      }

    public static TLAToken BuiltInToken(String str)
      /*********************************************************************
      * Returns a new BUILTIN token with string str.  (A token like "="    *
      * has type BUILTIN, though in the translation phase, there will      *
      * probably be no difference in how BUILTIN and IDENT tokens are      *
      * handled.)                                                          *
      *********************************************************************/
      { TLAToken result = new TLAToken() ;
        result.string = str ;
        result.type   = TLAToken.BUILTIN ;
        return result ;
      }

    public static TLAToken IdentToken(String str) {
        /*********************************************************************
         * Returns a new IDENT token for identifier str.                     *
         *********************************************************************/
        TLAToken result = new TLAToken() ;
        result.string = str ;
        result.type   = TLAToken.IDENT ;
        return result ;
    }

    public static TLAExpr MakeExpr(Vector vec) {
      /*********************************************************************
      * Makes a normalized expression exp with exp.tokens = vec.           *
      *********************************************************************/
        TLAExpr result = new TLAExpr(vec) ;
        result.normalize() ;
        return result ;
    }

    public static TLAExpr TokVectorToExpr(Vector vec, int spaces)
      /*********************************************************************
      * If vec is a vector of TLAToken objects, then this method returns   *
      * a TLAExpr describing a one-line expression composed of clones of   *
      * the tokens in vec separated by `spaces' spaces.                    *
      * Called only by PcalTranslate.CheckPC.                              *
      *********************************************************************/
      { Vector firstLine = new Vector() ;
        int nextCol = 0 ;
        int i = 0 ;
        while (i < vec.size())
          { TLAToken tok = ((TLAToken) vec.elementAt(i)).Clone() ;
            tok.column = nextCol ;
            firstLine.addElement(tok) ;
            nextCol = nextCol + tok.getWidth() + spaces ;
            i = i + 1 ;
          } ;
        
        return MakeExpr(Singleton(firstLine)) ;
      } ;

    public static void MakeNewStackTopExprPretty(TLAExpr expr) {
        /*********************************************************************
         * Sets columns so this expr looks nice.                             *
         * Assumes exprs that this module generates for Call and CallReturn. *
         * Lines up the |-> tokens with the one for [ << procedure |-> ...   *
         * (that is, at column 16) when it can. The record names all appear  *
         * in column 6.                                                      *
         *********************************************************************/
        Vector line; /* Vector of TLAToken */
        int nextCol = 0;
        for (int i = 0; i < expr.tokens.size(); i++) {
            line = (Vector) expr.tokens.elementAt(i);
            if (i == 0 || i == expr.tokens.size() - 1) nextCol = 1;
            else nextCol = 6;
            for (int j = 0; j < line.size(); j++) {
                TLAToken tok = ((TLAToken) line.elementAt(j));
                tok.column = nextCol;
                nextCol = nextCol + tok.getWidth();
                if (tok.type == TLAToken.BUILTIN && tok.string == "|->") {
                    tok.column = tok.column + 1;
                    if (tok.column < 16) tok.column = 16;
                    nextCol = tok.column + 5;
                }
                else if (tok.type == TLAToken.BUILTIN && tok.string == "[") {
                    nextCol = nextCol + 1;
                }
                else if (tok.type == TLAToken.BUILTIN && tok.string == "]") {
                    tok.column = tok.column + 1;
                    nextCol = nextCol + 1;
                }
                else if (tok.type == TLAToken.BUILTIN && tok.string == "<<") {
                    nextCol = nextCol + 1;
                }
                else if (tok.type == TLAToken.BUILTIN && tok.string == ">>") {
                    tok.column = tok.column + 1;
                    nextCol = nextCol + 1;
                }
                else if (tok.type == TLAToken.BUILTIN && tok.string == "\\o") {
                    tok.column = tok.column + 1;
                    nextCol = nextCol + 2;
                }

            }
        }
    }

    public static AST.Assign MakeAssign(String id, TLAExpr exp) {
        /*********************************************************************
         * Makes the assignment statement id := exp.                         *
         *                                                                   *
         * It is called only by UpdatePC, with id = "pc".                    *
         *********************************************************************/
        AST.SingleAssign sAss = new AST.SingleAssign() ;
        sAss.lhs.var = id ;
        sAss.lhs.sub = MakeExpr(new Vector()) ;
        sAss.rhs = exp ;
        AST.Assign result = new AST.Assign() ;
        result.ass = Singleton(sAss) ;
        return result ;
      }

        /*********************************************************************
        * true if expr is TRUE or ( TRUE )                                   *
        *********************************************************************/
    public static boolean IsTRUE(TLAExpr expr) {
        Vector tokens = expr.tokens;
        if (tokens.size() > 1) return false;
        Vector line = (Vector) tokens.elementAt(0);
        if (line.size() == 1) {
            TLAToken tok = (TLAToken) line.elementAt(0);
            return (tok.string.equals("TRUE")) ? true : false;
        }
        else if (line.size() == 3) {
            TLAToken tok1 = (TLAToken) line.elementAt(0);
            TLAToken tok2 = (TLAToken) line.elementAt(1);
            TLAToken tok3 = (TLAToken) line.elementAt(2);
            return (tok1.string.equals("(")
                    && tok2.string.equals("TRUE")
                    && tok3.string.equals(")")) ? true : false;
        }
        else return false;
    }

    private static AST.When CheckPC (String label) {
        /*********************************************************************
        * Generate when pc = label ;                                         *
        *********************************************************************/
        AST.When checkPC = new AST.When();
        Vector toks = new Vector();
        toks.addElement(AddedToken("pc"));
        toks.addElement(BuiltInToken("="));
        toks.addElement(StringToken(label));
        checkPC.exp = TokVectorToExpr(toks, 1);
        return checkPC;
    }

    private static AST.Assign UpdatePC (String next) {
        /*********************************************************************
        * Generate pc := next ;                                              *
        *********************************************************************/
        return MakeAssign("pc", MakeExpr(Singleton2(StringToken(next))));
    }

    /**
     * @deprecated method not used
     */
    private static AST.If IfForLabelIf (TLAExpr test,
                                        Vector unlabThen,
                                        String nextThen,
                                        Vector unlabElse,
                                        String nextElse) {
        /*********************************************************************
        * Generate  if test then unlabThen; pc := nextThen ;                 *
        *           else unlabElse; pc := nextElse ;                         *
        *********************************************************************/
        AST.If ifForLabelIf = new AST.If();
        ifForLabelIf.test = test;
        ifForLabelIf.Then = unlabThen;
        ifForLabelIf.Then.addElement(UpdatePC(nextThen));
        ifForLabelIf.Else = unlabElse;
        ifForLabelIf.Else.addElement(UpdatePC(nextElse));
        return ifForLabelIf;
    }

    /*************************************************************************
     * Explode                                                               
     **
     *************************************************************************/

    public static AST Explode (AST ast, PcalSymTab symtab) throws PcalTranslateException {
        /*********************************************************************
        * Expand while, labeled if, and nexted labeled with a sequence of    *
        * of flat labeled statements. Control flow is added via assignments  *
        * to pc. This expansion produces a new AST.                          *
        *********************************************************************/
        st = symtab;
        currentProcedure = null;  // added by LL on 7 June 2010
        if (ast.getClass().equals(AST.UniprocessObj.getClass()))
            return ExplodeUniprocess((AST.Uniprocess) ast);
        else if (ast.getClass().equals(AST.MultiprocessObj.getClass()))
            return ExplodeMultiprocess((AST.Multiprocess) ast);
        else {
            PcalDebug.ReportBug("Unexpected AST type.");
            return null;
        }
    }

    private static AST.Uniprocess ExplodeUniprocess (AST.Uniprocess ast) throws PcalTranslateException {
        /*********************************************************************
        * Generate new AST.Uniprocess that has exploded labeled statements.  *
        *********************************************************************/
        int i = 0;
        AST.Uniprocess newast = new AST.Uniprocess();
        newast.col = ast.col;
        newast.line = ast.line;
        newast.name = ast.name;
        newast.decls = ast.decls;
        newast.prcds = new Vector(ast.prcds.size(), 10);
        newast.defs = ast.defs ;  // added 25 Jan 2006 by LL
        newast.setOrigin(ast.getOrigin()) ;
        i = 0;
        while (i < ast.prcds.size()) {
            newast.prcds.addElement(
                                    ExplodeProcedure((AST.Procedure)
                                                     ast.prcds.elementAt(i)));
            i = i + 1;
        }
        i = 0;
        newast.body = new Vector(ast.body.size(), 10);
        AST.LabeledStmt thisLS = (ast.body.size() > 0)
            ? (AST.LabeledStmt) ast.body.elementAt(0) : null;
        AST.LabeledStmt nextLS = (ast.body.size() > 1)
            ? (AST.LabeledStmt) ast.body.elementAt(1) : null;
        while (i < ast.body.size()) {
            String next = (nextLS == null)
// Replacement of following line by LL on 3 Feb 2006, since
// label "Done" never has to be renamed, since "Done" is not
// a legal user label.
//                ? st.UseThis(PcalSymTab.LABEL, "Done", "")
                ? "Done"
                : nextLS.label;
            newast.body.addAll(ExplodeLabeledStmt(thisLS, next));
            i = i + 1;
            thisLS = nextLS;
            nextLS = (ast.body.size() > i + 1)
                ? (AST.LabeledStmt) ast.body.elementAt(i + 1) : null;
        }
        return newast;
    }
        
    private static AST.Multiprocess ExplodeMultiprocess (AST.Multiprocess ast) throws PcalTranslateException {
        /*********************************************************************
        * Generate new AST.Multiprocess with exploded labeled statements.    *
        *********************************************************************/
        int i = 0;
        AST.Multiprocess newast = new AST.Multiprocess();
        newast.col = ast.col;
        newast.line = ast.line;
        newast.name = ast.name;
        newast.decls = ast.decls;
        newast.prcds = new Vector(ast.prcds.size(), 10);
        newast.defs = ast.defs ;  // added 25 Jan 2006 by LL
        newast.setOrigin(ast.getOrigin()) ;
        while (i < ast.prcds.size()) {
            newast.prcds.addElement(ExplodeProcedure((AST.Procedure)
                                                     ast.prcds.elementAt(i)));
            i = i + 1;
        }
        i = 0;
        newast.procs = new Vector(ast.procs.size(), 10);
        while (i < ast.procs.size()) {
            newast.procs.addElement( ExplodeProcess((AST.Process)
                                                   ast.procs.elementAt(i)));
            i = i + 1;
        }
        return newast;
    }

    private static AST ExplodeProcedure (AST.Procedure ast) throws PcalTranslateException {
        /*********************************************************************
        * Generate new AST.Procedure with exploded labeled statements.       *
        *********************************************************************/
        int i = 0;
        AST.Procedure newast = new AST.Procedure();
        newast.setOrigin(ast.getOrigin()) ;
        newast.col = ast.col;
        newast.line = ast.line;
        newast.name = ast.name;
        currentProcedure = ast.name;  // Added by LL on 7 June 2010
        newast.params = ast.params;
        newast.decls = ast.decls;
        newast.body = new Vector(ast.body.size(), 10);
        AST.LabeledStmt thisLS = (ast.body.size() > 0)
            ? (AST.LabeledStmt) ast.body.elementAt(0) : null;
        AST.LabeledStmt nextLS = (ast.body.size() > 1)
            ? (AST.LabeledStmt) ast.body.elementAt(1) : null;
        while (i < ast.body.size()) {
            String next = (nextLS == null)
                ? st.UseThis(PcalSymTab.LABEL, "Error", "")
                : nextLS.label;
            newast.body.addAll(ExplodeLabeledStmt(thisLS, next));
            i = i + 1;
            thisLS = nextLS;
            nextLS = (ast.body.size() > i + 1)
                ? (AST.LabeledStmt) ast.body.elementAt(i + 1) : null;
        }
        currentProcedure = null;  // Added by LL on 7 June 2010
        return newast;
    }
        
    private static AST ExplodeProcess(AST.Process ast) throws PcalTranslateException {
        /*********************************************************************
        * Generate new AST.Process with exploded labeled statements.         *
        *********************************************************************/
        int i = 0;
        AST.Process newast = new AST.Process();
        newast.setOrigin(ast.getOrigin()) ;
        newast.col = ast.col;
        newast.line = ast.line;
        newast.name = ast.name;
        newast.isEq = ast.isEq;
        newast.id = ast.id;
        newast.decls = ast.decls;
        newast.body = new Vector();
        AST.LabeledStmt thisLS = (ast.body.size() > 0)
            ? (AST.LabeledStmt) ast.body.elementAt(0) : null;
        AST.LabeledStmt nextLS = (ast.body.size() > 1)
            ? (AST.LabeledStmt) ast.body.elementAt(1) : null;
        while (i < ast.body.size()) {
            String next = (nextLS == null)
// Replacement of following line by LL on 3 Feb 2006, since
// label "Done" never has to be renamed, since "Done" is not
// a legal user label.
//                ? st.UseThis(PcalSymTab.LABEL, "Done", "")
                ? "Done"
                : nextLS.label;
            newast.body.addAll(ExplodeLabeledStmt(thisLS, next));
            i = i + 1;
            thisLS = nextLS;
            nextLS = (ast.body.size() > i + 1)
                ? (AST.LabeledStmt) ast.body.elementAt(i + 1) : null;
        }
        return newast;
    }

    private static Vector CopyAndExplodeLastStmt(Vector stmts, String next) throws PcalTranslateException {
        /**************************************************************
        * The arguments are:                                               *
        *                                                                  *
        *    stmts : a (perhaps null) Vector of statements                 *
        *    next  : the label of the next control point following stmts.  *
        *                                                                  *
        * It returns a triple <<result1, result2, needsGoto>>, where       *
        *                                                                  *
        *   result1 : A vector equal to stmts with the last statement      *
        *             replaced if necessary by the exploded version--      *
        *             namely, if it is a goto, call, return, or            *
        *             callreturn, or if it is a statement with one of      *
        *             these statements or a labeled statement nested       *
        *             within it.                                           *
        *                                                                  *
        *   result2 : A (possibly empty) vector that is the sequence of    *
        *             labeled statements generated by exploding the last   *
        *             statement of stmts.                                  *
        *                                                                  *
        *   needsGoto : A boolean that equals true iff the sequence        *
        *               result1 of statements needs a goto at the end to   *
        *               transfer control to `next'.  In other words, it    *
        *               equals false if result1 contains the necessary     *
        *               goto statements and no goto must be added.         *
        *                                                                  *
        * Modified by LL on 25 Jan 2006 to handle the `either' statement   *
        * and to correct the following bug.  If a labeled statement ended  *
        * with an `if' statement, then gotos were added to both the then   *
        * and else clause, even if there was no transfer of control        *
        * within those clauses, so a single goto after the `if' would      *
        * work.  Similarly, if the statement ended with a `with', the      *
        * goto at the end would always be placed inside the `with' when    *
        * it logically belonged outside.                                   *
         **************************************************************/
        Vector result1 = new Vector(); /* a vector of statements */
        Vector result2 = new Vector(); /* a vector of labeled statements */
        boolean needsGoto = false ;
        if (stmts != null && stmts.size() > 0) {
            AST last = (AST) stmts.elementAt(stmts.size() - 1);
            result1 = stmts;
            if (last.getClass().equals(AST.LabelIfObj.getClass())) {
                Vector pair = ExplodeLabelIf((AST.LabelIf) last, next);
                  /*********************************************************
                  * Because a LabelIf has a label in the `then' or `else'  *
                  * clause, ExplodeLabelIf always has to add the           *
                  * necessary gotos.                                       *
                  *********************************************************/
                result1.removeElementAt(result1.size()-1);
                result1.addAll((Vector) pair.elementAt(0));
                result2 = (Vector) pair.elementAt(1);
            }
            // LabelEither added by LL on 25 Jan 2006
            else if (last.getClass().equals(AST.LabelEitherObj.getClass())) {
                Vector pair = ExplodeLabelEither((AST.LabelEither) last, next);
                  /*********************************************************
                  * Because a LabelEither has a label in some clause,      *
                  * ExplodeLabelEither always has to add the necessary     *
                  * gotos.                                                 *
                  *********************************************************/
                result1.removeElementAt(result1.size()-1);
                result1.addAll((Vector) pair.elementAt(0));
                result2 = (Vector) pair.elementAt(1);
            }
            else if (last.getClass().equals(AST.GotoObj.getClass())) {
                AST.Goto g = (AST.Goto) last;
                result1.removeElementAt(result1.size()-1);
                // Note: if there's a GotoObj, then omitPC should be false.
                result1.addElement(UpdatePC(g.to));
            }
            else if (last.getClass().equals(AST.CallObj.getClass())) {
                result1.removeElementAt(result1.size()-1);
                result1.addAll(ExplodeCall((AST.Call) last, next));
            }
            else if (last.getClass().equals(AST.ReturnObj.getClass())) {
                result1.removeElementAt(result1.size()-1);
                result1.addAll(ExplodeReturn((AST.Return) last, next));
            }
            else if (last.getClass().equals(AST.CallReturnObj.getClass())) {
                result1.removeElementAt(result1.size()-1);
                result1.addAll(ExplodeCallReturn((AST.CallReturn) last, next));
            }
            else if (last.getClass().equals(AST.IfObj.getClass())) {
                AST.If If = (AST.If) last;
                Vector p1 = CopyAndExplodeLastStmt(If.Then, next);
                Vector p2 = CopyAndExplodeLastStmt(If.Else, next);
                result2.addAll((Vector) p1.elementAt(1));
                result2.addAll((Vector) p2.elementAt(1));
                If.Then = (Vector) p1.elementAt(0);
                If.Else = (Vector) p2.elementAt(0);
                if (! ParseAlgorithm.omitPC) {
                  boolean thenNeedsGoto = ((BoolObj) p1.elementAt(2)).val ;
                  boolean elseNeedsGoto = ((BoolObj) p2.elementAt(2)).val ;
                  needsGoto = thenNeedsGoto && elseNeedsGoto ;
                  if (! needsGoto){
                    if (thenNeedsGoto) {
                       If.Then.addElement(UpdatePC(next));
                      } ;                
                    if (elseNeedsGoto) {
                       If.Else.addElement(UpdatePC(next));
                     } ;                
                  }
                }
            }
            // EitherObj added by LL on 25 Jan 2006
            else if (last.getClass().equals(AST.EitherObj.getClass())) {
                needsGoto = true ;
                Vector needsGotoVec = new Vector() ;
                AST.Either Either = (AST.Either) last;
                for (int i = 0; i < Either.ors.size(); i++) {
                  Vector thisP = CopyAndExplodeLastStmt( 
                             (Vector) Either.ors.elementAt(i), next);
                  
                  Either.ors.setElementAt(thisP.elementAt(0), i) ;
                  result2.addAll((Vector) thisP.elementAt(1));
                  needsGoto = needsGoto && ((BoolObj) thisP.elementAt(2)).val ;
                  needsGotoVec.addElement(thisP.elementAt(2)) ;
                } ;
                if (! ParseAlgorithm.omitPC) {
                  if (! needsGoto) {
                    /* Each `or' clause needs a goto. */
                    for (int i = 0; i < Either.ors.size(); i++) {
                      if ( ((BoolObj) needsGotoVec.elementAt(i)).val ) {
                        ((Vector) 
                           Either.ors.elementAt(i)).addElement(
                                UpdatePC(next));  
                      }
                     }
                  }
                };
            }
            else if (last.getClass().equals(AST.WithObj.getClass())) {
                AST.With with = (AST.With) last;
                Vector p = CopyAndExplodeLastStmt(with.Do, next);
                with.Do = (Vector) p.elementAt(0);
                result2.addAll((Vector) p.elementAt(1));
                  /*********************************************************
                  * This statement should be a no-op because a `with'      *
                  * should have no labels inside it.  Perhaps we should    *
                  * add a test for this.  (LL comment)                     *
                  *********************************************************/
                needsGoto = ((BoolObj) p.elementAt(2)).val ;
            }
            else needsGoto = true ; // result1.addElement(UpdatePC(next));
        }
        else { 
          /* This is an empty sequence of statements.  */
          needsGoto = true ;
        }  ;
//        else  result1.addElement(UpdatePC(next));
        if (ParseAlgorithm.omitPC) {
            needsGoto = false;
        }
        return Triple(result1, result2, BO(needsGoto));
    }


    private static Vector 
          CopyAndExplodeLastStmtWithGoto(Vector stmts, String next) throws PcalTranslateException {
      /*********************************************************************
      * Added by LL on 5 Feb 2011: The following comment seems to be       *
      * wrong, and the method adds a goto iff the 3rd element of the       *
      * value returned by CopyAndExplodeLastStmt equals true.              *
      *                                                                    *
      * Like CopyAndExplodeLastStmt, but it always adds a goto and         *
      * returns only a pair consisting of the first two elements of the    *
      * triple returned by CopyAndExplodeLastStmt.                         *
      *********************************************************************/
      Vector res = CopyAndExplodeLastStmt(stmts, next) ;
        if (((BoolObj) res.elementAt(2)).val) {
          ((Vector) res.elementAt(0)).addElement(UpdatePC(next)); } ;    
      return Pair(res.elementAt(0), res.elementAt(1)) ;
    }


    private static Vector ExplodeLabeledStmt (AST.LabeledStmt ast,
                                              String next) throws PcalTranslateException {
         /******************************************************************
         * label SL -->                                                    *
         * label when pc = "label" ;                                       *
         *       SL                                                        *
         *       pc := next;                                               *
         *                                                                 *
         * Comment added by LL on 30 Jan 2006.                             *
         * I have no idea what the comment above is supposed to mean, but  *
         * this seems to return a sequence of labeled statements,          *
         * consisting of the exploded version of the labeled stmt ast      *
         * followed by the exploded labeled statements contained within    *
         * it.                                                             *
         ******************************************************************/
        /* Handle case of initial while separately */
        if (ast.stmts.size() > 0 && 
            ast.stmts.elementAt(0).getClass().equals(AST.WhileObj.getClass())) {
            return ExplodeWhile(ast, next);
        }
        AST.LabeledStmt newast = new AST.LabeledStmt();
        Vector pair = 
                CopyAndExplodeLastStmtWithGoto((Vector) ast.stmts.clone(), 
                                               next);
        Vector result = new Vector();
        newast.setOrigin(ast.getOrigin()) ;
        newast.col = ast.col;
        newast.line = ast.line;
        newast.label = ast.label;
        /* add the statements with last exploded */
        newast.stmts = (Vector) pair.elementAt(0);
        if (! ParseAlgorithm.omitPC) {
           /* prepend pc check */
           newast.stmts.insertElementAt(CheckPC(newast.label), 0);
           result.addElement(newast);
        }
        /* add recursively generated labeled statements */
        result.addAll((Vector) pair.elementAt(1));
        return result;
    }

    private static Vector ExplodeLabeledStmtSeq (Vector seq,
                                                 String next) throws PcalTranslateException {
     /**********************************************************************
     * seq is a sequence of LabeledStmts, and `next' is the label that     *
     * follows them.  Returns the sequence of LabeledStmts obtained by     *
     * iteratively calling ExplodeLabeledStmt to explode the statements    *
     * in seq.                                                             *
     *                                                                     *
     * Added by LL on 30 Jan 2006.  I don't know why this method did not   *
     * already exist, since it must have been written in-line about 5      *
     * times in various other methods.                                     *
     **********************************************************************/
     Vector result = new Vector() ;     
     for (int i = 0; i < seq.size(); i++) {
       AST.LabeledStmt stmt = (AST.LabeledStmt) seq.elementAt(i) ;
       String nxt = (i < seq.size() - 1) ?
                      ((AST.LabeledStmt) seq.elementAt(i+1)).label : next ;
       result.addAll(ExplodeLabeledStmt(stmt, nxt)) ;
      };
     return result ;
     }

    /*
     * Experimentation shows that the following method is called with ast
     * equal to a LabeledStmt such that the first elementof ast.stmts 
     * is an AST.While node, and the remaining elements are the unlabeled
     * statements following the source `while' statement.
     */
    private static Vector ExplodeWhile(AST.LabeledStmt ast,
                                       String next) throws PcalTranslateException {
        /*******************************************************************
        * label test unlabDo labDo next -->                                *
        * label when pc = "label" ;                                        *
        *       if test then unlabDo; pc := ld1;                           *
        *       else rest of statements                                    *
        *            pc := next                                            *
        * ld1   ...                                                        *
        * ldk   ...                                                        *
        *       pc := "label";                                             *
        *                                                                  *
        * Returns a pair that's like the first two elements of the         *
        * triple returned by CopyAndExplodeLastStmt.  (It always adds      *
        * the necessary goto to transfer control.)                         *
        *                                                                  *
        * If the test is TRUE or (TRUE) then the exploded code is          *
        * simplified to eliminate the if statement.  Any code that would   *
        * be executed in the "else" clause is discarded.  A warning        *
        * message is generated when the exploded code is simplified.       *
        *******************************************************************/
        Vector result = new Vector();
        AST.While w = (AST.While) ast.stmts.elementAt(0);

        AST.LabeledStmt newast = new AST.LabeledStmt();
        /*
         * We set the origin of the new LabeledStatement to that of
         * ast, if there is a statement that follows the While.  Otherwise,
         * it goes from the label to the end of the If constructed from the while.
         * 
         * We set the origin of the If constructed from the while to the end 
         * its unLabDo if there is a non-empty labDo, otherwise to the end
         * of the While. 
         */
        PCalLocation newastBeginLoc = ast.getOrigin().getBegin() ;
        PCalLocation whileBeginLoc = w.getOrigin().getBegin() ;
        PCalLocation whileBeginUnlabDoLoc = 
          (w.unlabDo.size() != 0) ? 
           ((AST) w.unlabDo.elementAt(0)).getOrigin().getBegin() :
            w.test.getOrigin().getEnd();
        PCalLocation whileEndUnlabDoLoc =
          (w.unlabDo.size() != 0) ? 
            ((AST) w.unlabDo.elementAt(w.unlabDo.size()-1)).getOrigin().getEnd() :
            w.test.getOrigin().getEnd();
        PCalLocation whileEndLoc = 
           // The original code contained
           //
           //     (w.labDo.size() != 0) ? w.getOrigin().getEnd() : whileEndUnlabDoLoc ; 
           //
           // which does not implement the comment above.
                (ast.stmts.size() != 1) ? ast.getOrigin().getEnd() : whileEndUnlabDoLoc ;
        newast.setOrigin(new Region(newastBeginLoc, whileEndLoc)) ;
        newast.col = ast.col;
        newast.line = ast.line;
        newast.label = ast.label;
        newast.stmts = new Vector();

        if (! ParseAlgorithm.omitPC) {
           newast.stmts.addElement(CheckPC(ast.label));   // pc test
        }

        /* determine where control goes after unlabDo is executed */
        AST.LabeledStmt firstLS = (w.labDo.size() == 0)
            ? null : (AST.LabeledStmt) w.labDo.elementAt(0);
        /* explode unlabDo */
        String unlabDoNext = (firstLS == null) ? ast.label : firstLS.label ;
        Vector pair1 = 
                CopyAndExplodeLastStmtWithGoto((Vector) w.unlabDo.clone(),
                                                unlabDoNext);
        /* explode the rest of the statements */
        Vector rest = (Vector) ast.stmts.clone();
           // Note: experimentation shows that clone() does a shallow copy, so
           // the elements of rest are == to the elements of ast.stmts.
        rest.remove(0);
        Vector pair2 = CopyAndExplodeLastStmtWithGoto(rest, next);

        if (IsTRUE(w.test)) // Optimized translation of while TRUE do
            newast.stmts.addAll((Vector) pair1.elementAt(0));
        else {
            AST.If ifS = new AST.If();
            ifS.test = w.test;
            ifS.Then = (Vector) pair1.elementAt(0);
            ifS.Else = (Vector) pair2.elementAt(0);
            ifS.setOrigin(new Region(whileBeginLoc, whileEndLoc)) ;
            newast.stmts.addElement(ifS);
        }
        result.addElement(newast);

        /* explode the enclosed labeled statements and add to the result */
        for (int i = 0; i < w.labDo.size(); i++) {
            AST.LabeledStmt nextLS = (w.labDo.size() > i + 1)
            ? (AST.LabeledStmt) w.labDo.elementAt(i + 1) : null;
            String nextLSL = (nextLS == null) ? ast.label : nextLS.label;
            result.addAll(ExplodeLabeledStmt(firstLS, nextLSL));
            firstLS = nextLS;
        }

        result.addAll((Vector) pair1.elementAt(1));
        
        // If IsTRUE(w.test) is true and pair2.elementAt(1) is not an empty
        // list, then there are unreachable statements after the While and
        // we should probably report an error.
        if (! IsTRUE(w.test)) 
            result.addAll((Vector) pair2.elementAt(1));

        return result;
    }

    private static Vector ExplodeLabelIf(AST.LabelIf ast, String next) throws PcalTranslateException {
        /***************************************************************
         *       test unlabThen labThen unlabElse labElse next -->     *
         *       if test then                                          *
         *          unlabThen                                          *
         *          pc := lt1                                          *
         *       else                                                  *
         *          unlabElse                                          *
         *          pc := le1                                          *
         * lt1   ...                                                   *
         * ltk   ...                                                   *
         *       pc := next;                                           *
         * le1   ...                                                   *
         * lek   ...                                                   *
         *       pc := next;                                           *
         *                                                             *
         * The result is a pair: the first is a vector of statements   *
         * corresponding to the block before lt1, and the second is    *
         * is a vector of the remaining labeled statements.            *
         ***************************************************************/
        int i = 0;
        Vector result1 = new Vector(); /* If for unlabeled statements */
        Vector result2 = new Vector(); /* the labeled statements */
        AST.If newif = new AST.If();
        AST.LabeledStmt firstThen = (ast.labThen.size() > 0)
            ? (AST.LabeledStmt) ast.labThen.elementAt(0) : null;
        AST.LabeledStmt firstElse = (ast.labElse.size() > 0)
            ? (AST.LabeledStmt) ast.labElse.elementAt(0) : null;
        Vector explodedThen = 
                 CopyAndExplodeLastStmtWithGoto(ast.unlabThen,
                                                (firstThen == null)
                                                ? next : firstThen.label);
        Vector explodedElse = 
                  CopyAndExplodeLastStmtWithGoto(ast.unlabElse,
                                                 (firstElse == null)
                                                 ? next : firstElse.label);
        /* Construct if statement */
        newif.test = ast.test;
        newif.col = ast.col;
        newif.line = ast.line;
        newif.Then = (Vector) explodedThen.elementAt(0);
        newif.Else =  (Vector) explodedElse.elementAt(0);
        newif.setOrigin(ast.getOrigin()) ;
        /*
         * The LabelIf object ast has a labeled statement in its then clause iff
         * ast.labThen or explodedThen.elementAt(1) has non-zero length.
         * It has a labeled statement in its else clause iff
         * ast.labElse or explodedElse.elementAt(1) has non-zero length.
         */
        newif.setSource(
            ((ast.labThen.size() != 0 || 
            ((Vector) explodedThen.elementAt(1)).size() != 0 ) 
               ? AST.IfObj.BROKEN_THEN : 0)      
            +
            ((ast.labElse.size() != 0 || 
            ((Vector) explodedElse.elementAt(1)).size() != 0 ) 
               ? AST.IfObj.BROKEN_ELSE : 0)
          ) ;
        result1.addElement(newif);

        /* Explode the labeled then statements */
        AST.LabeledStmt nextThen = (ast.labThen.size() > 1)
            ? (AST.LabeledStmt) ast.labThen.elementAt(1) : null;
        i = 0;
        while (i < ast.labThen.size()) {
            String nextThenLabel = (nextThen == null) ? next : nextThen.label;
            result2.addAll(ExplodeLabeledStmt(firstThen, nextThenLabel));
            i = i + 1;
            firstThen = nextThen;
            nextThen = (ast.labThen.size() > i + 1)
                ? (AST.LabeledStmt) ast.labThen.elementAt(i + 1) : null;
        }
        /* Explode the labeled else statements */
        AST.LabeledStmt nextElse = (ast.labElse.size() > 1)
            ? (AST.LabeledStmt) ast.labElse.elementAt(1) : null;
        i = 0;
        while (i < ast.labElse.size()) {
            String nextElseLabel = (nextElse == null) ? next : nextElse.label;
            result2.addAll(ExplodeLabeledStmt(firstElse, nextElseLabel));
            i = i + 1;
            firstElse = nextElse;
            nextElse = (ast.labElse.size() > i + 1)
                ? (AST.LabeledStmt) ast.labElse.elementAt(i + 1) : null;
        }
        
        
        /* Add labeled statements from exploding unlabThen and unlabElse */
        result2.addAll((Vector) explodedThen.elementAt(1));
        result2.addAll((Vector) explodedElse.elementAt(1));
        return Pair(result1, result2);
    }

    private static Vector ExplodeLabelEither(AST.LabelEither ast, 
                                             String next) throws PcalTranslateException {
        /*******************************************************************
        * Analogous to ExplodeLabelIf, except it hasa sequence of clauses  *
        * rather than just the then and else clauses.                      *
        *                                                                  *
        * The result is a pair: the first is a vector of statements        *
        * corresponding to the block before lt1, and the second is         *
        * is a vector of the remaining labeled statements.                 *
        *******************************************************************/
        Vector result1 = new Vector(); /* For the Either object.           */
        Vector result2 = new Vector(); /* The internal labeled statements. */
        AST.Either newEither = new AST.Either();

        /* Construct Either object */
        newEither.col = ast.col;
        newEither.line = ast.line;
        newEither.setOrigin(ast.getOrigin()) ;
        newEither.ors = new Vector() ;
        for (int i = 0; i < ast.clauses.size(); i++) {
          AST.Clause clause = (AST.Clause) ast.clauses.elementAt(i) ;
          Vector res = 
             CopyAndExplodeLastStmtWithGoto(
               clause.unlabOr,
               (clause.labOr.size() > 0) ?
                  ((AST.LabeledStmt) clause.labOr.elementAt(0)).label : next
               ) ;
          /**
           * Set clause.broken, which should be true iff clause.labOr or
           * res.elementAt(1) is non-empty.
           */
         if (clause.labOr.size() != 0 || ((Vector) res.elementAt(1)).size() != 0) {
             clause.setBroken(true) ;
         }         
         newEither.ors.addElement((Vector) res.elementAt(0)) ;
         result2.addAll((Vector) res.elementAt(1)) ;
         result2.addAll(ExplodeLabeledStmtSeq(clause.labOr, next)) ;
        } ;
        result1.addElement(newEither);
        return Pair(result1, result2);
    }

    /***********************************************************************
    * Generate sequence of statements corresponding to call                *
    *                                                                      *
    * Modified 1 Feb 2006 by LL to put the initialization of the           *
    * procedure's local variables as a sequence of separate assignment     *
    * statements, executed after the initialization of the formal          *
    * parameters.                                                          *
    *                                                                      *
    * Modified by LL on 2 Feb 2006 to add line and column numbers to the   *
    * newly created statements for error reporting.                        
     **
    ***********************************************************************/
    private static Vector ExplodeCall(AST.Call ast, String next) throws PcalTranslateException {
        Vector result = new Vector();
        int to = st.FindProc(ast.to);
        /*******************************************************************
        * Error check added by LL on 30 Jan 2006 to fix bug_05_12_10.      *
        *******************************************************************/
        if (to == st.procs.size())
          { throw new PcalTranslateException("Call of non-existent procedure " + ast.to,
                                    ast);  } ;
        PcalSymTab.ProcedureEntry pe =
            (PcalSymTab.ProcedureEntry) st.procs.elementAt(to);
        /*******************************************************************
        * Set ass to a multiple assignment that pushes the call record on  *
        * the stack, sets the called procedure's parameters.               *
        *                                                                  *
        * The call record put on the stack is:                             *
        *   procedure |-> ast.to                                           *
        *   pc |-> next                                                    *
        *   for each procedure variable v of ast.to v |-> v                *
        *   for each parameter p of ast.to p |-> p                         *
        *******************************************************************/
        AST.Assign ass = new AST.Assign();
        ass.ass = new Vector();
        ass.line = ast.line ;
        ass.col  = ast.col ;
        AST.SingleAssign sass = new AST.SingleAssign();
        sass.line = ast.line ;
        sass.col  = ast.col ;
        sass.lhs.var = "stack";
        sass.lhs.sub = MakeExpr(new Vector());
        TLAExpr expr = new TLAExpr();
        expr.addLine();
        expr.addToken(BuiltInToken("<<"));
        expr.addToken(BuiltInToken("["));
        expr.addToken(IdentToken("procedure"));
        expr.addToken(BuiltInToken("|->"));
        expr.addToken(StringToken(ast.to));
        expr.addToken(BuiltInToken(","));
        expr.addLine();
        expr.addToken(IdentToken("pc"));
        expr.addToken(BuiltInToken("|->"));
        expr.addToken(StringToken(next));       
        for (int i = 0; i < pe.decls.size(); i++) {
            AST.PVarDecl decl =
                (AST.PVarDecl) pe.decls.elementAt(i);
            expr.addToken(BuiltInToken(","));
            expr.addLine();
            expr.addToken(IdentToken(decl.var));
            expr.addToken(BuiltInToken("|->"));
            expr.addToken(IdentToken(decl.var));
        }
        for (int i = 0; i < pe.params.size(); i++) {
            AST.PVarDecl decl =
                (AST.PVarDecl) pe.params.elementAt(i);
            expr.addToken(BuiltInToken(","));
            expr.addLine();
            expr.addToken(IdentToken(decl.var));
            expr.addToken(BuiltInToken("|->"));
            expr.addToken(IdentToken(decl.var));
        }
        expr.addToken(BuiltInToken("]"));
        expr.addToken(BuiltInToken(">>"));
        expr.addLine();
        expr.addToken(BuiltInToken("\\o"));
        expr.addToken(AddedToken("stack"));
        MakeNewStackTopExprPretty(expr);
        expr.normalize();
        sass.rhs = expr;
        ass.ass.addElement(sass);
        /*********************************************************
         * for each parameter p of ast.to                        *
         *   p := matching expr in ast.arg                       *
         *********************************************************/
        /*******************************************************************
        * Assert changed to ReportErrorAt by LL on 30 Jan 2006.            *
        *******************************************************************/
        if (pe.params.size() != ast.args.size())
            throw new PcalTranslateException(
                  "Procedure " + ast.to +
                       " called with wrong number of arguments",
                  ast) ;
        /**
         * Set the origin of the AST.Assign object ass.origin to the region occupied
         * by the parameter declarations, and set the origin of each of its SingleAssign 
         * subobjects that set the parameters to that parameter's declaration as a parameter
         * of the procedure.  (This code assumes that  the declarations appear in the params
         * list of an AST.Procedure in the order in which they appear in the PCal code.)
         * Since we're setting the origin to the entire declaration, if the declaration
         * specifies an initial value, then this will set the origin to the entire
         * declaration, rather than just the variable name.  This could be fixed easily,
         * but it's not worth the effort.
         */
        PCalLocation beginLoc = null ;
        PCalLocation endLoc = null ;
        for (int i = 0; i < pe.params.size(); i++) {
            AST.PVarDecl decl =
                (AST.PVarDecl) pe.params.elementAt(i);
            if (i == 0) {
                beginLoc = decl.getOrigin().getBegin();
            }
            if (i == pe.params.size() - 1) {
                endLoc = decl.getOrigin().getEnd();
            }
            sass = new AST.SingleAssign();
            sass.line = ast.line ;
            sass.col  = ast.col ;
            sass.setOrigin(decl.getOrigin()) ;
            sass.lhs.var = decl.var;
            sass.lhs.sub = MakeExpr(new Vector());
            sass.rhs = (TLAExpr) ast.args.elementAt(i);
            ass.ass.addElement(sass);
        }
        if (beginLoc != null) {
            ass.setOrigin(new Region(beginLoc, endLoc)) ;
        }
        result.addElement(ass);
        /*******************************************************************
        * Add a sequence of assignment statements to initialize each       *
        * procedure variable v of ast.to with                              *
        *   v := initial value                                             *
        *******************************************************************/
        for (int i = 0; i < pe.decls.size(); i++) {
            ass = new AST.Assign();
            ass.ass = new Vector() ;
            ass.line = ast.line ;
            ass.col  = ast.col ;
            AST.PVarDecl decl =
                (AST.PVarDecl) pe.decls.elementAt(i);
            sass = new AST.SingleAssign();
            sass.line = ast.line ;
            sass.col  = ast.col ;
            sass.setOrigin(decl.getOrigin()) ;
            sass.lhs.var = decl.var;
            sass.lhs.sub = MakeExpr(new Vector());
            sass.rhs = (TLAExpr) decl.val;
            ass.setOrigin(decl.getOrigin()) ;
            ass.ass.addElement(sass);
            result.addElement(ass) ;
        }
        
        /*******************************************************************
        * Add assignment to set pc:                                        *
        *   pc := entry point of ast.to                                    *
        *******************************************************************/
        // Note: omitPC must be false if there's a call statement (and hence
        // a procedure being called).
        result.addElement(UpdatePC(pe.iPC));
        return result;
    }

    /***********************************************************************
    * Modified by LL on 2 Feb 2006 to add line and column numbers to the   *
    * newly created statements for error reporting.                        
     **
    ***********************************************************************/
    private static Vector ExplodeReturn(AST.Return ast, String next) throws PcalTranslateException {
        Vector result = new Vector();
        /*******************************************************************
        * On 30 Mar 2006, added code to throw a PcalTranslateException     *
        * when ast.from equals null to raise an error if a return          *
        * statement appears outside a procedure.  That error was not       *
        * caught by the parsing phase for reasons explained in the         *
        * comments for ParseAlgorithm.GetReturn.                           *
        *                                                                  *
        * Unfortunately, that test raised an error if the return actually  *
        * was inside a procedure but was generated by macro expansion.     *
        * To allow that case, on 7 June 2010 LL added the                  *
        * currentProcedure field (see comments for that field) and         *
        * modified the test accordingly.  (This was after an incorrect     *
        * attempt to fix the problem on 6 June 2010.)                      *
        *******************************************************************/
        if (ast.from == null)
        {
            ast.from = currentProcedure;
        }
        if (ast.from == null)
        {
            throw new PcalTranslateException("`return' statement not in procedure", ast);
        }
        ;

        int from = st.FindProc(ast.from);
        // The following added by LL on 13 Jan 2011.
        if (!(from < st.procs.size())) {
        	throw new PcalTranslateException("Error in procedure (perhaps name used elsewhere)", ast);
        }
        PcalSymTab.ProcedureEntry pe =
            (PcalSymTab.ProcedureEntry) st.procs.elementAt(from);
        /*********************************************************
         * With h being the head of stack                        *
         *   pc := h.pc                                          *
         *   for each procedure variable v of ast.from v := h.v  *
         *   for each parameter p of ast.from p := h.p           *
         *********************************************************/
        AST.Assign ass = new AST.Assign();
        ass.line = ast.line ;
        ass.col  = ast.col ;
        AST.SingleAssign sass = new AST.SingleAssign();
        sass.line = ast.line ;
        sass.col  = ast.col ;
        TLAExpr expr = new TLAExpr();
        sass.lhs.var = "pc";
        sass.lhs.sub = new TLAExpr();
        expr.addLine();
        expr.addToken(IdentToken("Head"));
        expr.addToken(BuiltInToken("("));
        expr.addToken(AddedToken("stack"));
        expr.addToken(BuiltInToken(")"));
        expr.addToken(BuiltInToken("."));
        expr.addToken(IdentToken("pc"));
        expr.normalize();
        sass.rhs = expr;
        ass.ass = Singleton(sass);
        result.addElement(ass);
        for (int i = 0; i < pe.decls.size(); i++) {
            AST.PVarDecl decl =
                (AST.PVarDecl) pe.decls.elementAt(i);
            ass = new AST.Assign();
            ass.line = ast.line ;
            ass.col  = ast.col ;
            sass = new AST.SingleAssign();
            sass.line = ast.line ;
            sass.col  = ast.col ;
            expr = new TLAExpr();
            sass.lhs.var = decl.var;
            sass.lhs.sub = new TLAExpr();
            expr.addLine();
            expr.addToken(IdentToken("Head"));
            expr.addToken(BuiltInToken("("));
            expr.addToken(AddedToken("stack"));
            expr.addToken(BuiltInToken(")"));
            expr.addToken(BuiltInToken("."));
            expr.addToken(IdentToken(decl.var));
            expr.normalize();
            sass.rhs = expr;
            /**
             * For assignments that restore procedure variables, there's no
             * good origin.  I decided to set them to the origin of the return statement.
             */
            sass.setOrigin(ast.getOrigin()) ;
            ass.setOrigin(ast.getOrigin()) ;
            ass.ass = Singleton(sass);
            result.addElement(ass);
        }
        for (int i = 0; i < pe.params.size(); i++) {
            AST.PVarDecl decl =
                (AST.PVarDecl) pe.params.elementAt(i);
            ass = new AST.Assign();
            ass.line = ast.line ;
            ass.col  = ast.col ;
            sass = new AST.SingleAssign();
            sass.line = ast.line ;
            sass.col  = ast.col ;
            /** For assignments that restore procedure parameter values, there's no
             * good origin.  I decided to set them to the origin of the return statement.
             */
            sass.setOrigin(ast.getOrigin()) ;
            ass.setOrigin(ast.getOrigin()) ;
            expr = new TLAExpr();
            sass.lhs.var = decl.var;
            sass.lhs.sub = new TLAExpr();
            expr.addLine();
            expr.addToken(IdentToken("Head"));
            expr.addToken(BuiltInToken("("));
            expr.addToken(AddedToken("stack"));
            expr.addToken(BuiltInToken(")"));
            expr.addToken(BuiltInToken("."));
            expr.addToken(IdentToken(decl.var));
            expr.normalize();
            sass.rhs = expr;
            ass.ass = Singleton(sass);
            result.addElement(ass);
        }

        /*********************************************************
         * stack := Tail(stack)                                  *
         *********************************************************/
        ass = new AST.Assign();
        ass.line = ast.line ;
        ass.col  = ast.col ;
        sass = new AST.SingleAssign();
        sass.setOrigin(ast.getOrigin()) ;
        ass.setOrigin(ast.getOrigin()) ;
        sass.line = ast.line ;
        sass.col  = ast.col ;
        expr = new TLAExpr();
        sass.lhs.var = "stack";
        sass.lhs.sub = new TLAExpr();
        expr.addLine();
        expr.addToken(IdentToken("Tail"));
        expr.addToken(BuiltInToken("("));
        expr.addToken(AddedToken("stack"));
        expr.addToken(BuiltInToken(")"));
        expr.normalize();
        sass.rhs = expr;
        ass.ass = Singleton(sass);
        result.addElement(ass);
        return result;
    }

    /***********************************************************************
    * Generate sequence of statements corresponding to call followed by a  *
    * returen.                                                             *
    *                                                                      *
    * Modified 1 Feb 2006 by LL for the case of the calling and called     *
    * procedures being different to put the initialization of the          *
    * procedure's local variables as a sequence of separate assignment     *
    * statements, executed after the initialization of the formal          *
    * parameters.                                                          *
    *                                                                      *
    * Modified by LL on 2 Feb 2006 to add line and column numbers to the   *
    * newly created statements for error reporting.                        
     **
    ***********************************************************************/
    private static Vector ExplodeCallReturn(AST.CallReturn ast, String next) throws PcalTranslateException {
        Vector result = new Vector();
        /*******************************************************************
        * The following test for a return not in a procedure was added by  *
        * LL on 30 Mar 2006.  This error isn't caught by the parsing       *
        * phase for reasons explained in the comments for                  *
        * ParseAlgorithm.GetReturn.                                        *
        *******************************************************************/
        if (ast.from == null)
          { throw new PcalTranslateException(
              "`return' statement following `call' at " +
               ast.location() + " not in a procedure");
          } ;
        int from = st.FindProc(ast.from);
        PcalSymTab.ProcedureEntry peFrom =
            (PcalSymTab.ProcedureEntry) st.procs.elementAt(from);
        int to = st.FindProc(ast.to);
        /*******************************************************************
        * Assert changed to ReportErrorAt by LL on 30 Jan 2006, and moved  *
        * to where it belongs.                                             *
        *******************************************************************/
        if (to == st.procs.size())
          { throw new PcalTranslateException("Call of non-existent procedure " + ast.to,
                                    ast);  } ;
        PcalSymTab.ProcedureEntry peTo =
            (PcalSymTab.ProcedureEntry) st.procs.elementAt(to);
        PcalDebug.Assert(from < st.procs.size());
        AST.Assign ass = new AST.Assign();
        ass.ass = new Vector();
        ass.line = ast.line ;
        ass.col  = ast.col ;
        AST.SingleAssign sass = null;
        TLAExpr expr = null;
        /*******************************************************************
        * Add a single multiple assignment statement that                  *
        *   - restores the local variables of ast.from from the head of    *
        *     the stack.                                                   *
        *   - replaces the head of the stack with a record used to reset   *
        *     the local variables.                                         *
        *   - sets the parameters of ast.to.                               *
        *                                                                  *
        * First, with h being the head of the stack, restore each local    *
        * variable v of ast.from with v := h.v .                           *
        *******************************************************************/
        if (! ast.from.equals(ast.to)) {
            for (int i = 0; i < peFrom.decls.size(); i++) {
                AST.PVarDecl decl =
                    (AST.PVarDecl) peFrom.decls.elementAt(i);
                sass = new AST.SingleAssign();
                sass.line = ast.line ;
                sass.col  = ast.col ;
                expr = new TLAExpr();
                sass.lhs.var = decl.var;
                sass.lhs.sub = new TLAExpr();
                expr.addLine();
                expr.addToken(IdentToken("Head"));
                expr.addToken(BuiltInToken("("));
                expr.addToken(AddedToken("stack"));
                expr.addToken(BuiltInToken(")"));
                expr.addToken(BuiltInToken("."));
                expr.addToken(IdentToken(decl.var));
                expr.normalize();
                sass.rhs = expr;
                ass.ass.addElement(sass);
            }
            /********************************************************
             * Replace head of stack with record                    *
             *   procedure |-> ast.to                               *
             *   pc |-> h.pc (for current head h)                   *
             *   for each procedure variable v of ast.to v |-> v    *
             *   for each parameter variable p of ast.to p |-> p    *
             ********************************************************/
            sass = new AST.SingleAssign();
            sass.line = ast.line ;
            sass.col  = ast.col ;
            sass.lhs.var = "stack";
            sass.lhs.sub = MakeExpr(new Vector());
            expr = new TLAExpr();
            expr.addLine();
            expr.addToken(BuiltInToken("<<"));
            expr.addToken(BuiltInToken("["));
            expr.addToken(IdentToken("procedure"));
            expr.addToken(BuiltInToken("|->"));
            expr.addToken(StringToken(ast.to));
            expr.addToken(BuiltInToken(","));
            expr.addLine();
            expr.addToken(IdentToken("pc"));
            expr.addToken(BuiltInToken("|->"));
            expr.addToken(IdentToken("Head"));
            expr.addToken(BuiltInToken("("));
            expr.addToken(AddedToken("stack"));
            expr.addToken(BuiltInToken(")"));
            expr.addToken(BuiltInToken("."));
            expr.addToken(IdentToken("pc"));
            for (int i = 0; i < peTo.decls.size(); i++) {
                AST.PVarDecl decl =
                    (AST.PVarDecl) peTo.decls.elementAt(i);
                expr.addToken(BuiltInToken(","));
                expr.addLine();
                expr.addToken(IdentToken(decl.var));
                expr.addToken(BuiltInToken("|->"));
                expr.addToken(IdentToken(decl.var));
            }
            for (int i = 0; i < peTo.params.size(); i++) {
                AST.PVarDecl decl =
                    (AST.PVarDecl) peTo.params.elementAt(i);
                expr.addToken(BuiltInToken(","));
                expr.addLine();
                expr.addToken(IdentToken(decl.var));
                expr.addToken(BuiltInToken("|->"));
                expr.addToken(IdentToken(decl.var));
            }
            expr.addToken(BuiltInToken("]"));
            expr.addToken(BuiltInToken(">>"));
            expr.addLine();
            expr.addToken(BuiltInToken("\\o"));
            expr.addToken(IdentToken("Tail"));
            expr.addToken(BuiltInToken("("));
            expr.addToken(AddedToken("stack"));
            expr.addToken(BuiltInToken(")"));
            MakeNewStackTopExprPretty(expr);
            expr.normalize();
            sass.rhs = expr;
            ass.ass.addElement(sass);
        }
        /*********************************************************
         * for each parameter p of ast.to                        *
         *   p := matching expr in ast.arg                       *
         *********************************************************/
        /*******************************************************************
        * Assert changed to ReportErrorAt by LL on 30 Jan 2006.            *
        *******************************************************************/
        if (peTo.params.size() != ast.args.size())
            throw new PcalTranslateException(
                  "Procedure " + ast.to +
                       " called with wrong number of arguments",
                  ast) ;
        /**
         * Setting of origins of created AST.Assign and AST.SingleAssign objects
         * essentialy the same as in ExplodeCall.
         */
        PCalLocation beginLoc = null ;
        PCalLocation endLoc = null ;
        for (int i = 0; i < peTo.params.size(); i++) {
            AST.PVarDecl decl =
                (AST.PVarDecl) peTo.params.elementAt(i);
            if (i == 0) {
                beginLoc = decl.getOrigin().getBegin();
            }
            if (i == peTo.params.size() - 1) {
                endLoc = decl.getOrigin().getEnd();
            }
            sass = new AST.SingleAssign();
            sass.line = ast.line ;
            sass.col  = ast.col ;
            sass.lhs.var = decl.var;
            sass.lhs.sub = MakeExpr(new Vector());
            sass.rhs = (TLAExpr) ast.args.elementAt(i);
            ass.ass.addElement(sass);
        }
        if (beginLoc != null) {
            ass.setOrigin(new Region(beginLoc, endLoc)) ;
        }
        result.addElement(ass);
        /*******************************************************************
        * Add a sequence of assignment statements to initialize each       *
        * procedure variable v of ast.to with                              *
        *   v := initial value                                             *
        *******************************************************************/
        for (int i = 0; i < peTo.decls.size(); i++) {
            ass = new AST.Assign();
            ass.line = ast.line ;
            ass.col  = ast.col ;
            ass.ass = new Vector() ;
            AST.PVarDecl decl =
                (AST.PVarDecl) peTo.decls.elementAt(i);
            sass = new AST.SingleAssign();
            sass.line = ast.line ;
            sass.col  = ast.col ;
            sass.setOrigin(decl.getOrigin()) ;
            sass.lhs.var = decl.var;
            sass.lhs.sub = MakeExpr(new Vector());
            sass.rhs = (TLAExpr) decl.val;
            ass.setOrigin(decl.getOrigin()) ;
            ass.ass.addElement(sass);
            result.addElement(ass) ;
        }
        /*********************************************************
         * pc := entry point of ast.to                           *
         *********************************************************/
        result.addElement(UpdatePC(peTo.iPC));
        return result;
    }
}
