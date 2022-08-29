// With a little luck, the assignment statement pc := "foo"  should be
// MakeAssign(pc, MakeExpr(Singleton2(StringToken("foo"))))

package pcal;

import util.ToolIO;

import java.io.File;
import java.util.ArrayList;

class Test {
    public static <T> ArrayList<T> Singleton(final T obj)
    /*********************************************************************
     * If we think of a vector as a sequence, then this returns <<obj>>.  *
     *********************************************************************/
    {
        final ArrayList<T> result = new ArrayList<>();
        result.add(obj);
        return result;
    }

    public static <T> ArrayList<ArrayList<T>> Singleton2(final T obj)
    /*********************************************************************
     * If we think of a vector as a sequence, then this returns           *
     * << <<obj>> >>.                                                     *
     *********************************************************************/
    {
        return Singleton(Singleton(obj));
    }

    public static TLAToken StringToken(final String str)
    /*********************************************************************
     * Returns a new STRING token with string str.                        *
     *********************************************************************/
    {
        final TLAToken result = new TLAToken();
        result.string = str;
        result.type = TLAToken.STRING;
        return result;
    }

    public static TLAToken BuiltinToken(final String str)
    /*********************************************************************
     * Returns a new BUILTIN token with string str.  (A token like "="    *
     * has type BUILTIN, though in the translation phase, there will      *
     * probably be no difference in how BUILTIN and IDENT tokens are      *
     * handled.)                                                          *
     *********************************************************************/
    {
        final TLAToken result = new TLAToken();
        result.string = str;
        result.type = TLAToken.BUILTIN;
        return result;
    }

    public static TLAToken IdentToken(final String str)
    /*********************************************************************
     * Returns a new IDENT token for identifier str.                      *
     *********************************************************************/
    {
        final TLAToken result = new TLAToken();
        result.string = str;
        result.type = TLAToken.IDENT;
        return result;
    }

    public static TLAExpr MakeExpr(final ArrayList<ArrayList<TLAToken>> vec)
    /*********************************************************************
     * Makes a normalized expression exp with exp.tokens = vec.           *
     *********************************************************************/
    {
        final TLAExpr result = new TLAExpr(vec);
        result.normalize();
        return result;
    }

    public static TLAExpr TokVectorToExpr(final ArrayList<TLAToken> vec, final int spaces)
    /*********************************************************************
     * If vec is a vector of TLAToken objects, then this method returns   *
     * a TLAExpr describing a one-line expression composed of clones of   *
     * the tokens in vec separated by `spaces' spaces.                    *
     *********************************************************************/
    {
        final ArrayList<TLAToken> firstLine = new ArrayList<>();
        int nextCol = 0;
        int i = 0;
        while (i < vec.size()) {
            final TLAToken tok = vec.get(i).Clone();
            tok.column = nextCol;
            firstLine.add(tok);
            nextCol = nextCol + tok.getWidth() + spaces;
            i = i + 1;
        }

        return MakeExpr(Singleton(firstLine));
    }

    public static AST.Assign MakeAssign(final String id, final TLAExpr exp)
    /*********************************************************************
     * Makes the assignment statement id := exp.                          *
     *********************************************************************/
    {
        PcalParams pcalParams = new PcalParams();
        final AST.SingleAssign sAss = new AST.SingleAssign(pcalParams);
        sAss.lhs.var = id;
        sAss.lhs.sub = MakeExpr(new ArrayList<>());
        sAss.rhs = exp;
        final AST.Assign result = new AST.Assign(pcalParams);
        result.ass = Singleton(sAss);
        return result;
    }


    /***************************************************************************
     * The AST node for `when pc = "foo"'  should be produced by something like *
     * ArrayList toks = new ArrayList() ;                                             *
     *                                                                          *
     *     toks.add(IdentToken("pc")) ;                                  *
     *     toks.add(BuiltInToken("=")) ;                                 *
     *     toks.add(StringToken("foo")) ;                                *
     *     AST.When node = new AST.when() ;                                     *
     *     node.exp = TokVectorToExpr(toks) ;                                   *
     *                                                                          *
     ***************************************************************************/
    public static void main(final String[] args) {
        File f = new File("no-file.cfg");
        ToolIO.out.println("no-file.canRead() = " + f.canRead());
        ToolIO.out.println("no-file.canWrite() = " + f.canWrite());
        ToolIO.out.println("no-file.exists() = " + f.exists());
        f = new File("read-only.cfg");
        ToolIO.out.println("read-only.canRead() = " + f.canRead());
        ToolIO.out.println("read-only.canWrite() = " + f.canWrite());
        ToolIO.out.println("read-only.exists() = " + f.exists());
        f = new File("Bakery.cfg");
        ToolIO.out.println("Bakery.canRead() = " + f.canRead());
        ToolIO.out.println("Bakery.canWrite() = " + f.canWrite());
        ToolIO.out.println("Bakery.exists() = " + f.exists());

    }


}
