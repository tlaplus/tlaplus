// With a little luck, the assignment statement pc := "foo"  should be
// MakeAssign(pc, MakeExpr(Singleton2(StringToken("foo"))))

package pcal ;
import java.io.File;
import java.util.Vector;

import util.ToolIO;

class Test
  { public static Vector Singleton(Object obj) 
      /*********************************************************************
      * If we think of a vector as a sequence, then this returns <<obj>>.  *
      *********************************************************************/
      { Vector result = new Vector() ;
        result.addElement(obj) ;
        return result; 
      }
 
    public static Vector Singleton2(Object obj)
      /*********************************************************************
      * If we think of a vector as a sequence, then this returns           *
      * << <<obj>> >>.                                                     *
      *********************************************************************/
      { return Singleton(Singleton(obj));
      } 

    public static TLAToken StringToken(String str)
      /*********************************************************************
      * Returns a new STRING token with string str.                        *
      *********************************************************************/
      { TLAToken result = new TLAToken() ;
        result.string = str ;
        result.type   = TLAToken.STRING ;;
        return result ;
      }

    public static TLAToken BuiltinToken(String str)
      /*********************************************************************
      * Returns a new BUILTIN token with string str.  (A token like "="    *
      * has type BUILTIN, though in the translation phase, there will      *
      * probably be no difference in how BUILTIN and IDENT tokens are      *
      * handled.)                                                          *
      *********************************************************************/
      { TLAToken result = new TLAToken() ;
        result.string = str ;
        result.type   = TLAToken.BUILTIN ;;
        return result ;
      }

    public static TLAToken IdentToken(String str)
      /*********************************************************************
      * Returns a new IDENT token for identifier str.                      *
      *********************************************************************/
      { TLAToken result = new TLAToken() ;
        result.string = str ;
        result.type   = TLAToken.IDENT ;
        return result ;
      }

    public static TLAExpr MakeExpr(Vector vec)
      /*********************************************************************
      * Makes a normalized expression exp with exp.tokens = vec.           *
      *********************************************************************/
      { TLAExpr result = new TLAExpr(vec) ;
        result.normalize() ;
        return result ;
      }

    public static TLAExpr TokVectorToExpr(Vector vec, int spaces)
      /*********************************************************************
      * If vec is a vector of TLAToken objects, then this method returns   *
      * a TLAExpr describing a one-line expression composed of clones of   *
      * the tokens in vec separated by `spaces' spaces.                    *
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

    public static AST.Assign MakeAssign(String id, TLAExpr exp)
      /*********************************************************************
      * Makes the assignment statement id := exp.                          *
      *********************************************************************/
      { AST.SingleAssign sAss = new AST.SingleAssign() ;
        sAss.lhs.var = id ;
        sAss.lhs.sub = MakeExpr(new Vector()) ;
        sAss.rhs = exp ;
        AST.Assign result = new AST.Assign() ;
        result.ass = Singleton(sAss) ;
        return result ;
      }


/***************************************************************************
* The AST node for `when pc = "foo"'  should be produced by something like *
* Vector toks = new Vector() ;                                             *
*                                                                          *
*     toks.addElement(IdentToken("pc")) ;                                  *
*     toks.addElement(BuiltInToken("=")) ;                                 *
*     toks.addElement(StringToken("foo")) ;                                *
*     AST.When node = new AST.when() ;                                     *
*     node.exp = TokVectorToExpr(toks) ;                                   *
*                                                                          *
***************************************************************************/
   public static void main(String[] args) 
     { File f = new File("no-file.cfg") ;
       ToolIO.out.println("no-file.canRead() = " + f.canRead()) ;
       ToolIO.out.println("no-file.canWrite() = " + f.canWrite()) ;
       ToolIO.out.println("no-file.exists() = " + f.exists()) ;
       f = new File("read-only.cfg") ;
       ToolIO.out.println("read-only.canRead() = " + f.canRead()) ;
       ToolIO.out.println("read-only.canWrite() = " + f.canWrite()) ;
       ToolIO.out.println("read-only.exists() = " + f.exists()) ;
       f = new File("Bakery.cfg") ;
       ToolIO.out.println("Bakery.canRead() = " + f.canRead()) ;
       ToolIO.out.println("Bakery.canWrite() = " + f.canWrite()) ;
       ToolIO.out.println("Bakery.exists() = " + f.exists()) ;
       
     }


  }
