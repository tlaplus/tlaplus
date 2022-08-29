/***************************************************************************
 * CLASS AST                                                                *
 *                                                                          *
 * This class defines AST objects, which represent non-terminals of the     *
 * +CAL grammar, to be subclasses of the AST class.                         *
 *                                                                          *
 * Each subclass has a toString() method that prints the object as the      *
 * TLA+ record that represents that node in the representation of the       *
 * abstract syntax tree used in the PlusCal TLA+ specification.             *
 *                                                                          *
 * There are no explicit classes corresponding to the following             *
 * non-terminals.                                                           *
 *                                                                          *
 *    Algorithm   AlgorithmBody LabelSeq   SimpleStmt   Finalstmt  VarDecls *
 *                                                                          *
 * However, there are the following classes that do not represent explicit  *
 * non-terminals of the +CAL grammar.                                       *
 *                                                                          *
 * Uniprocess   MultiProcess   SingleAssign   CallReturn   CallGoto         *
 *                                                                          *
 * Every AST has col and line fields that contain the position of the       *
 * first character of the corresponding portion of the algorithm text (as   *
 * human ordinals, numbered starting from 1).                               *
 *                                                                          *
 *                                                                          *
 * Since the only way Java has of defining record (struct) type is by       *
 * making it a class, all the different AST node subtypes had to be         *
 * subclasses.  I didn't want to put each of them in a separate file, so I  *
 * made them all nested inner static classes in this file.  (I presume it   *
 * doesn't make sense to make them dynamic classes, since that would imply  *
 * that each instance of an AST node has its own separate instance of       *
 * those classes.  Anyway, we Java produces a runtime NoSuchMethodError     *
 * unless I make the inner classes static.)                                 *
 *                                                                          *
 * To enable a method to figure out what subclass an AST object is, I       *
 * initially gave the class a type field and tried to use that field to     *
 * determine the type.  However, this didn't work right at all.  The        *
 * problem is that when an element of the subtype gets obtained as an       *
 * object of the superclass AST--for example, when it's pulled out of a     *
 * vector of AST objects, the type field of the resulting object is set to  *
 * the value set by the supertype's constructor.  So, I need to actually    *
 * find out what Java thinks the class of the object is.  The following     *
 * hack seems to work.  To determine if the subclass of an AST object obj   *
 * is Skip, one can test                                                    *
 *                                                                          *
 *    obj.getClass().toString().equals("class pcal.AST$Skip")               *
 *                                                                          *
 * However, this seems unlikely to work for all versions of all Java        *
 * implementations.  So, for each subclass like AST.Skip, we define an      *
 * object SkipObj of that class.  We then test if obj is of class AST.Skip  *
 * by                                                                       *
 *                                                                          *
 *    obj.getClass().equals(AST.SkipObj.getClass())                         *
 *                                                                          *
 * The object SkipObj cannot be declared with an initial value, because     *
 * that leads the initialization of the AST class to go into an infinite    *
 * loop.  So, the method AST.ASTInit() assign a new AST.Skip node to        *
 * AST.SkipObj.                                                             *
 *                                                                          *
 * I'm sure there's a better way, but I can't find anything about           *
 * it in the Java Reference Manual.                                         *
 ***************************************************************************/
package pcal;

import java.util.ArrayList;


public class AST {

    /***********************************************************************
     * Constants used to describe a process's fairness assumption.          *
     ***********************************************************************/
    public static final int UNFAIR_PROC = 0;
    public static final int WF_PROC = 1;
    public static final int SF_PROC = 2;
    public static final String[] FairnessString = {"unfair", "wf", "sf"};
    /*********************************************************************
     * If this is an object that was inserted into the AST as the result  *
     * of macro expansion, then this is the column and line number of     *
     * the MacroCall object that was expanded.  The col and line values   *
     * give the position of the object in the macro definition that       *
     * yielded the current object when the macro was expanded.            *
     *                                                                    *
     * If the object was not inserted by macro expansion, then macroLine  *
     * equals -1.                                                         *
     *********************************************************************/
    public static final int[] curIndent = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    /************************************************************************
     * Methods for getting the toString() methods to indent the              *
     * representation nicely so it's readable.  They are used as follows.    *
     * Suppose we are printing a record with fields foo, foobar, elf, and    *
     * we want it to be output as:                                           *
     *                                                                       *
     *    [foo |-> XXXXXX                                                    *
     *             XXXXXX                                                    *
     *             XXXXX ,                                                   *
     *     elf    |-> "elf",                                                 *
     *     foobar |-> YYYY                                                   *
     *                YYY ]                                                  *
     *                                                                       *
     * where XX...XXX is produced by XXX.toString and YY...YYY by            *
     * YYY.toString().  We would produce the string as follows:              *
     *                                                                       *
     *    Indent("[foo |-> ") +                                              *
     *           XXX.toString() + "," +                                      *
     *    EndIndent() + NewLine() +                                          *
     *    "[elf    |-> \"elf\"," + NewLine()                                 *
     *    NewLine() +                                                        *
     *    Indent(" foobar |-> ") +                                           *
     *             XXX.toString() + "]" +                                    *
     *    EndIndent()                                                        *
     ************************************************************************/
    public static int indentDepth = 0;
    final PcalParams pcalParams;
    /*********************************************************************
     * Added by LL on 3 Mar 2006.  Used to hold a statement's label       *
     * during the parsing process, but irrelevant once the final AST has  *
     * been constructed.                                                  *
     *********************************************************************/
    public int col;
    public int line;
    /*********************************************************************
     * These are the column and line numbers of the first token in the    *
     * algorithm text that corresponds to the AST. (They are human        *
     * ordinals, counting from 1.)                                        *
     *********************************************************************/
    public int macroCol = 0;
    public int macroLine = -1;
    /**
     * If this AST is a statement that is the first statement resulting from
     * expansion of a macro call , then macroOriginBegin is set to the
     * origin.begin value of the macro call.  It is set by
     * ParseAlgorithm.ExpandMacroCall and is used by PcalTLAGen.GenLabeledStmt
     * to set the MappingObject.LeftParen that marks the beginning of the
     * labeled statement's translation.
     * <p>
     * macroOriginEnd is similarly set for the last statement resulting from
     * the expansion of a mapping call and used to set the labeled statement's
     * translation's MappingObject.RightParen.
     * <p>
     * This is a Kludge to correct a bug in the TLA+ translation to
     * PlusCal mapping.  These kludges are the result of implementing
     * that mapping on top of the existing translator, rather than rewriting
     * the translation.
     */
    public PCalLocation macroOriginBegin = null;
    public PCalLocation macroOriginEnd = null;
    public String lbl = "";
    /**
     * If the lbl field is not the empty string "", then lblLocation is
     * the location of the beginning of the label that provided the string
     * if it came from a label written by the user.  It will be null if the
     * label was added by the translator.
     */
    public PCalLocation lblLocation = null;
    /**
     * The region of the PlusCal code from which the object was created.
     */
    private Region origin = null;

    public AST(final PcalParams pcalParams) {
        this.pcalParams = pcalParams;
    }

    /**********************************************************************
     * There must be an easier way.                                        *
     **********************************************************************/

    public static String Indent(final String str) {
        curIndent[indentDepth + 1] = curIndent[indentDepth] + str.length();
        indentDepth = indentDepth + 1;
        return str;
    }

    public static String EndIndent() {
        indentDepth = indentDepth - 1;
        return "";
    }

    public static String NewLine() {
        final StringBuilder result = new StringBuilder("\n");
        int i = 0;
        while (i < curIndent[indentDepth]) {
            result.append(" ");
            i = i + 1;
        }
        return result.toString();
    }

    public static String VectorToSeqString(final ArrayList<?> vec)
    /**********************************************************************
     * Returns the TLA+ representation of vec as a sequence of its         *
     * elements, where toString() is used to produce the elements'         *
     * representation.                                                     *
     **********************************************************************/
    {
        if (vec == null) {
            return "null";
        }
        final StringBuilder result = new StringBuilder(Indent("<<"));
        int i = 0;
        while (i < vec.size()) {
            if (i > 0) {
                result.append(", ").append(NewLine());
            }
            result.append(vec.get(i).toString());
            i = i + 1;
        }
        return result + ">>" + EndIndent();
    }

    public static String VectorToSeqQuotedString(final ArrayList<?> vec)
    /**********************************************************************
     * Returns the TLA+ representation of vec as a sequence of quoted      *
     * elements, where toString() is used to produce the elements'         *
     * representation to be quoted.                                        *
     **********************************************************************/
    {
        if (vec == null) {
            return "null";
        }
        final StringBuilder result = new StringBuilder(Indent("<<"));
        int i = 0;
        while (i < vec.size()) {
            if (i > 0) {
                result.append(", ") /* + NewLine() */;
            }
            result.append("\"").append(vec.get(i).toString()).append("\"");
            i = i + 1;
        }
        return result + ">>" + EndIndent();
    }

    public static String VectorOfVectorsToSeqString(final ArrayList<?> vecvec)
    /**********************************************************************
     * Returns the TLA+ representation of vec as a sequence of its         *
     * elements, where each of its elements is a vector of objects whose   *
     * representation is obtained by calling toString().                   *
     **********************************************************************/
    {
        final StringBuilder result = new StringBuilder(Indent("<< "));
        int i = 0;
        while (i < vecvec.size()) {
            if (i > 0) {
                result.append(", ").append(NewLine());
            }
            result.append(VectorToSeqString((ArrayList<?>) vecvec.get(i)));
            i = i + 1;
        }
        return result + " >>" + EndIndent();
    }

    public Region getOrigin() {
        return origin;
    }

    public void setOrigin(final Region origin) {
        this.origin = origin;
    }

    public String location()
    /*********************************************************************
     * The string that describes the location in the algorithm of the     *
     * first token that represents the AST object.  Should be used in     *
     * error messages.                                                    *
     *********************************************************************/
    {
        if (macroLine < 0) {
            return "line " + line + ", column " + col;
        } else {
            return "line " + line + ", column " + col +
                    " of macro called at line " + macroLine +
                    ", column " + macroCol;
        }
    }

    /***************************** UTILITY METHODS ****************************/

    public String boolToEqOrIn(final boolean iseq) {
        if (iseq) {
            return "\"=\"";
        } else {
            return "\"\\\\in\"";
        }
    }

    public String lineCol()
    /**********************************************************************
     * Equals "(*line, col*)" if pcal.trans called in debugging mode,      *
     * otherwise the empty string.                                         *
     **********************************************************************/
    {
        if (pcalParams.Debug) {
            return "(*" + line + ", " + col + "*)";
        } else {
            return "";
        }
    }

    public static class Uniprocess extends AST {
        public String name = "";
        public ArrayList<AST.VarDecl> decls = null; // of VarDecl
        public TLAExpr defs = null;
        public ArrayList<Macro> macros = null; // of Macro
        public ArrayList<AST.Procedure> prcds = null; // of Procedure
        public ArrayList<AST> body = null; // of LabeledStmt

        public Uniprocess(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type     |-> \"uniprocess\", " + NewLine() +
                            " name  |-> \"" + name + "\", " + NewLine() +
                            Indent(" decls  |-> ") + VectorToSeqString(decls) + ","
                            +
                            EndIndent() + NewLine() +
                            Indent(" defs   |-> ") + defs.toString() + ","
                            +
                            EndIndent() + NewLine() +

                            /*************************************************************
                             * Uncomment the following to print the macros field.  It is  *
                             * commented out so the printed result is what PlusCal.tla    *
                             * considers a Uniprocess object to be.                       *
                             *************************************************************/
                            // Indent(" macros |-> ") + VectorToSeqString(macros) + ","
                            //                             +
                            //  EndIndent() + NewLine() +

                            Indent(" prcds  |-> ") + VectorToSeqString(prcds) + ","
                            +
                            EndIndent() + NewLine() +
                            Indent(" body  |-> ") + VectorToSeqString(body) + "]" +
                            EndIndent() +
                            EndIndent();
        }
    }

    public static class Multiprocess extends AST {
        public String name = "";
        public ArrayList<AST.VarDecl> decls = null; // of VarDecl
        public TLAExpr defs = null;
        public ArrayList<Macro> macros = null; // of Macro
        public ArrayList<AST.Procedure> prcds = null; // of Procedure
        public ArrayList<AST.Process> procs = null; // of Process

        public Multiprocess(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type    |-> \"multiprocess\", " + NewLine() +
                            " name  |-> \"" + name + "\", " + NewLine() +
                            Indent(" decls |-> ") + VectorToSeqString(decls) + ","
                            +
                            EndIndent() + NewLine() +
                            Indent(" defs  |-> ") + defs.toString() + ","
                            +
                            EndIndent() + NewLine() +
                            /*************************************************************
                             * Uncomment the following to print the macros field.  It is  *
                             * commented out so the printed result is what PlusCal.tla    *
                             * considers a Multiprocess object to be.                     *
                             *************************************************************/
                            // Indent(" macros |-> ") + VectorToSeqString(macros) + ","
                            //                             +
                            // EndIndent() + NewLine() +

                            Indent(" prcds |-> ") + VectorToSeqString(prcds) + ","
                            +
                            EndIndent() + NewLine() +
                            Indent(" procs |-> ") + VectorToSeqString(procs) + "]" +
                            EndIndent() +
                            EndIndent();
        }
    }

    /**
     * The minusLabels and plusLabels fields were added by LL in
     * January 2011 to implement the Version 1.5 enhancement that allows
     * fairness modifiers on labels.  These Vectors contain the labels
     * in the process that have the indicated modifier.  They are initially
     * set in the GetProcedure method of ParseAlgorithm, with the help of
     * the GetLabel method.  They are then fixed to correct for label
     * conflicts by the FixProcedure method of PcalFixIDs.
     * <p>
     * The proceduresCalled field was added later in Jan 2011 by LL because,
     * since procedures can call other procedures, a transitive closure
     * is required to compute the procedures called by a process.  (Those
     * procedures need to be known to compute the fairness conditions, since
     * a fairness requirement on a process implies a fairness requirement on
     * all the procedures that the process calls.)
     * <p>
     * Note added 2 Apr 2013 by LL.  Also, it should be noted
     * that the transitive closure is computed by the call to PcalFixIDs.Fix,
     * not during the initial parsing phase.
     *
     * @author lamport
     */
    public static class Procedure extends AST {
        public String name = "";
        public ArrayList<String> minusLabels = new ArrayList<>();
        public ArrayList<String> plusLabels = new ArrayList<>();
        public ArrayList<String> proceduresCalled = new ArrayList<>();
        public ArrayList<AST.PVarDecl> params = null; // of PVarDecl
        public ArrayList<AST.PVarDecl> decls = null; // of PVarDecl
        public ArrayList<AST> body = null; // of LabeledStmt

        public Procedure(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            // For versions earlier than 1.5 need to return those versions'
            // value since toString() is used to generate the AST module
            // used when TLC is doing the translation.
            if (pcalParams.inputVersionNumber < PcalParams.VersionToNumber("1.5")) {
                return
                        Indent(lineCol()) +
                                "[name   |-> \"" + name + "\", " + NewLine() +
                                Indent(" params |-> ") + VectorToSeqString(params) + "," +
                                EndIndent() + NewLine() +
                                Indent(" decls  |-> ") + VectorToSeqString(decls) + "," +
                                EndIndent() + NewLine() +
                                Indent(" body   |-> ") + VectorToSeqString(body) + "]" +
                                EndIndent() +
                                EndIndent();
            }
            return
                    Indent(lineCol()) +
                            "[name   |-> \"" + name + "\", " + NewLine() +
                            "minusLabels |-> "
                            + VectorToSeqQuotedString(minusLabels) + ", plusLabels |->"
                            + VectorToSeqQuotedString(plusLabels) + ", proceduresCalled |->"
                            + VectorToSeqQuotedString(proceduresCalled) + ","
                            + NewLine() +
                            Indent(" params |-> ") + VectorToSeqString(params) + "," +
                            EndIndent() + NewLine() +
                            Indent(" decls  |-> ") + VectorToSeqString(decls) + "," +
                            EndIndent() + NewLine() +
                            Indent(" body   |-> ") + VectorToSeqString(body) + "]" +
                            EndIndent() +
                            EndIndent();
        }
    }

    /**
     * The minusLabels and plusLabels fields were added by LL in
     * January 2011 to implement the Version 1.5 enhancement that allows
     * fairness modifiers on labels.  They are set much like the corresponding
     * fields of an AST.Procedure object, as described above.
     * The proceduresCalled field was also added then.
     * <p>
     * Note added by LL on 2 April 2013.  The genius LL never noticed that
     * the proceduresCalled field only contains the procedures directly called,
     * and he used that in generating the fairness conditions without finding
     * the procedures that are called indirectly.
     *
     * @author lamport
     */
    public static class Process extends AST {
        public String name = "";
        public int fairness = UNFAIR_PROC;
        public ArrayList<String> minusLabels = new ArrayList<>();
        public ArrayList<String> plusLabels = new ArrayList<>();
        public ArrayList<String> proceduresCalled = new ArrayList<>();
        public boolean isEq = true; // true means "=", false means "\\in"
        public TLAExpr id = null;
        public ArrayList<AST.VarDecl> decls = null; // of VarDecl
        public ArrayList<AST> body = null; // of LabeledStmt

        public Process(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            // For versions earlier than 1.5 need to return those versions'
            // value since toString() is used to generate the AST module
            // used when TLC is doing the translation.
            if (pcalParams.inputVersionNumber < PcalParams.VersionToNumber("1.5")) {
                return
                        Indent(lineCol()) +
                                "[name   |-> \"" + name + "\", " + NewLine() +
                                " eqOrIn |-> " + boolToEqOrIn(isEq) + "," + NewLine() +
                                " id     |-> " + id.toString() + "," + NewLine() +
                                Indent(" decls  |-> ") +
                                VectorToSeqString(decls) + "," +
                                EndIndent() + NewLine() +
                                Indent(" body   |-> ") +
                                VectorToSeqString(body) + "]" +
                                EndIndent() +
                                EndIndent();
            }

            return
                    Indent(lineCol()) +
                            "[name   |-> \"" + name + "\","
                            + NewLine() +
                            " fairness |-> \""
                            + FairnessString[fairness] + "\", minusLabels |-> "
                            + VectorToSeqQuotedString(minusLabels) + ", plusLabels |->"
                            + VectorToSeqQuotedString(plusLabels) + ", proceduresCalled |->"
                            + VectorToSeqQuotedString(proceduresCalled) + ","
                            + NewLine() +
                            " eqOrIn |-> " + boolToEqOrIn(isEq) + "," + NewLine() +
                            " id     |-> " + id.toString() + "," + NewLine() +
                            Indent(" decls  |-> ") +
                            VectorToSeqString(decls) + "," +
                            EndIndent() + NewLine() +
                            Indent(" body   |-> ") +
                            VectorToSeqString(body) + "]" +
                            EndIndent() +
                            EndIndent();
        }
    }

    public static class VarDecl extends AST {
        public String var = null;
        public boolean isEq = true; // true means "=", false means "\\in"
        public TLAExpr val = PcalParams.DefaultVarInit();

        public VarDecl(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[var |-> \"" + var + "\", " +
                            "eqOrIn |-> " + boolToEqOrIn(isEq) + ", " +
                            "val |-> " + val.toString() + "]" +
                            EndIndent();
        }
    }

    public static class PVarDecl extends AST {
        public final boolean isEq = true;  // true means "="
        public String var = null;
        public TLAExpr val = PcalParams.DefaultVarInit();

        public PVarDecl(final PcalParams pcalParams) {
            super(pcalParams);
        }

        /**
         * Converts the PVarDecl object to an equivalent VarDecl
         * object.  (I don't know why I bothered introducing a separate
         * PVarDecl object in the first place.)
         */
        public VarDecl toVarDecl() {
            final VarDecl result = new VarDecl(pcalParams);
            result.var = this.var;
            result.val = this.val;
            result.setOrigin(this.getOrigin());
            result.isEq = true;
            return result;
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[var |-> \"" + var + "\", " +
                            "eqOrIn |-> \"=\", " +
                            "val |-> " + val.toString() + "]" +
                            EndIndent();
        }
    }

    public static class LabeledStmt extends AST {
        public String label = null;
        public ArrayList<AST> stmts = null;

        /*****************************************************************
         * An optional While prepended to a LabelSeq.                     *
         *****************************************************************/

        public LabeledStmt(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[label |-> \"" + label + "\"," + NewLine() +
                            Indent(" stmts |-> ") +
                            VectorToSeqString(stmts) + "]" +
                            EndIndent() +
                            EndIndent();
        }
    }

    public static class While extends AST {
        public TLAExpr test = null;
        public ArrayList<AST> unlabDo = null; // a LabelSeq
        public ArrayList<AST> labDo = null; // of LabeledStmt

        public While(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type    |-> \"while\", " + NewLine() +
                            " test    |-> " + test.toString() + "," + NewLine() +
                            Indent(" labDo   |-> ") +
                            VectorToSeqString(labDo) + "," +
                            EndIndent() + NewLine() +

                            Indent(" unlabDo |-> ") +
                            VectorToSeqString(unlabDo) + "]" +
                            EndIndent() +
                            EndIndent();
        }
    }

    public static class Assign extends AST {
        public ArrayList<AST.SingleAssign> ass = null; // of SingleAssign

        public Assign(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type |-> \"assignment\"," + NewLine() +
                            Indent(" ass  |-> ") +
                            VectorToSeqString(ass) + "]" +
                            EndIndent() +
                            EndIndent();
        }
    }

    public static class SingleAssign extends AST {
        public Lhs lhs = new Lhs(pcalParams);
        public TLAExpr rhs = null;

        public SingleAssign(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[lhs |-> " + lhs.toString() + "," + NewLine() +
                            " rhs |-> " + rhs.toString() + "]" +
                            EndIndent();
        }
    }

    public static class Lhs extends AST
            /*********************************************************************
             * Note use of Lhs as name rather than LHS, which is the type         *
             * constant.                                                          *
             *********************************************************************/
    {
        public String var = "";
        public TLAExpr sub = null;

        public Lhs(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            return lineCol() +
                    "[var |-> \"" + var + "\", sub |-> "
                    + sub.toString() + "]";
        }
    }

    /**
     * An AST.If object is created from an AST.LabelIf or AST.While object.
     * For a LabelIf containing no labeled statements, it is created inside
     * the CheckLabeledStmtSeq method when executing ParseAlgorithm.runMe(String[]).
     * Otherwise, it is created by exploding the original AST inside the
     * call of  PcalFixIDs.Fix.  Its origin is set to that of the original AST.
     *
     * @author lamport
     */
    public static class If extends AST {
        /*****************************************************************
         * Can't use "else" because that's a Java keyword.                *
         *****************************************************************/

        public static final int UNBROKEN = 0;
        public static final int BROKEN_WHILE = 1;
        public static final int BROKEN_THEN = 2;
        public static final int BROKEN_ELSE = 4;
        public TLAExpr test = null;
        public ArrayList<AST> Then = null; // of SimpleStmt
        /*****************************************************************
         * Could use "then", but use "Then" to avoid confusion since we   *
         * can't use "else".                                              *
         *****************************************************************/
        public ArrayList<AST> Else = null; // of SimpleStmt
        /**
         * The source field records the information about where the If came
         * from that is useful for the TLA+ to PlusCal translation.  The values
         * are:
         * <p>
         * UNBROKEN : Contains the entire contents of the original AST.
         * BROKEN_WHILE : Came from a While containing a labeled statement.
         * BROKEN_THEN : Came from an IfThen that contained a labeled statement
         * in the Then clause, but not the Else clausew.
         * BROKEN_ELSE : Came from an IfThen that contained a labeled statement
         * in the Else clause but not the Then clause.
         * BROKEN_THEN + BROKEN_ELSE : Came from an IfThen with labeled statements
         * in both clauses.
         */
        private int source = UNBROKEN;

        public If(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public int getSource() {
            return source;
        }

        public void setSource(final int source) {
            this.source = source;
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type    |-> \"if\", " + NewLine() +
                            " test    |-> " + test.toString() + "," + NewLine() +
                            Indent(" then |-> ") + VectorToSeqString(Then) + ","
                            +
                            EndIndent() + NewLine() +
                            Indent(" else |-> ") + VectorToSeqString(Else) + "]" +
                            EndIndent() +
                            EndIndent();
        }
    }

    public static class Either extends AST {
        public ArrayList<Object> ors = null; // of Seq(SimpleStmt)

        public Either(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type |-> \"either\", " + NewLine() +
                            Indent(" ors  |-> ") + VectorOfVectorsToSeqString(ors) + "]" +
                            EndIndent() +
                            EndIndent();
        }
    }

    public static class With extends AST {
        public String var = "";
        public boolean isEq = true; // true means "=", false "\\in"
        public TLAExpr exp = null;
        public ArrayList<AST> Do = null; // of SimpleStmt

        /*****************************************************************
         * Can't use "do" because that's a Java keyword.                  *
         *****************************************************************/
        public With(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type   |-> \"with\", " + NewLine() +
                            " var    |-> \"" + var + "\"," + NewLine() +
                            " eqOrIn |-> " + boolToEqOrIn(isEq) + "," + NewLine() +
                            " exp    |-> " + exp.toString() + "," + NewLine() +
                            Indent(" do     |-> ") + VectorToSeqString(Do) + "]" +
                            EndIndent() +
                            EndIndent();
        }
    }

    public static class When extends AST {
        public TLAExpr exp = null;

        public When(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type |-> \"when\", " + NewLine() +
                            " exp |-> " + exp.toString() + "]" +
                            EndIndent();
        }
    }

    public static class PrintS extends AST {
        public TLAExpr exp = null;

        public PrintS(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type |-> \"print\", " + NewLine() +
                            " exp |-> " + exp.toString() + "]" +
                            EndIndent();
        }
    }

    public static class Assert extends AST {
        public TLAExpr exp = null;

        public Assert(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type |-> \"assert\", " + NewLine() +
                            " exp |-> " + exp.toString() + "]" +
                            EndIndent();
        }
    }

    public static class Skip extends AST {
        public Skip(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            return lineCol() + "[type |-> \"skip\"]";
        }
    }

    /**
     * A LabelIf represents an if statement whose then and/or
     * else clause has a label.
     *
     * @author lamport
     */
    public static class LabelIf extends AST {
        public TLAExpr test = null;
        public ArrayList<AST> unlabThen = null; // a LabelSeq
        public ArrayList<AST> labThen = null; // of LabeledStmt
        public ArrayList<AST> unlabElse = null; // a LabelSeq
        public ArrayList<AST> labElse = null; // of LabeledStmt

        public LabelIf(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type      |-> \"labelIf\"," + NewLine() +
                            " test      |-> " + test.toString() + "," + NewLine() +
                            Indent(" unlabThen |-> ") + VectorToSeqString(unlabThen)
                            + "," +
                            EndIndent() + NewLine() +
                            Indent(" labThen   |-> ") + VectorToSeqString(labThen)
                            + "," +
                            EndIndent() + NewLine() +
                            Indent(" unlabElse |-> ") + VectorToSeqString(unlabElse)
                            + "," +
                            EndIndent() + NewLine() +
                            Indent(" labElse   |-> ") + VectorToSeqString(labElse)
                            + "]" +
                            EndIndent() + NewLine() +
                            EndIndent();
        }
    }

    public static class LabelEither extends AST {
        public ArrayList<AST.Clause> clauses = null; // of Clause

        public LabelEither(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type    |-> \"labelEither\"," + NewLine() +
                            Indent(" clauses |-> ") + VectorToSeqString(clauses)
                            + "]" +
                            EndIndent() + NewLine() +
                            EndIndent();
        }
    }

    public static class Clause extends AST {
        public ArrayList<AST> unlabOr = null; // a LabelSeq
        public ArrayList<AST> labOr = null; // LabeledStmt
        /**
         * The broken field is true iff the Clause object came from
         * a LabelEither object for which the corresponding clause
         * contained a labeled statement.
         */
        private boolean broken = false;

        public Clause(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public boolean isBroken() {
            return broken;
        }

        public void setBroken(final boolean broken) {
            this.broken = broken;
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            Indent("[unlabOr |-> ") + VectorToSeqString(unlabOr)
                            + "," +
                            EndIndent() + NewLine() +
                            Indent(" labOr   |-> ") + VectorToSeqString(labOr)
                            + "]" +
                            EndIndent() + NewLine() +
                            EndIndent();
        }
    }

    public static class Call extends AST {
        public String returnTo = "";
        public String to = "";
        public ArrayList<TLAExpr> args = null; // of TLAExpr

        public Call(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type     |-> \"call\"," + NewLine() +
                            " returnTo |-> \"" + returnTo + "\"," + NewLine() +
                            " to       |-> \"" + to + "\"," + NewLine() +
                            Indent(" args     |-> ") + VectorToSeqString(args) + "]" +
                            EndIndent() +
                            EndIndent();
        }
    }

    public static class Return extends AST {
        public String from = "";

        public Return(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            return
                    lineCol() +
                            "[type |-> \"return\", from |-> \"" + from + "\"]";
        }
    }

    /**
     * A CallReturn object represents a call immediately followed
     * by a return.
     *
     * @author lamport
     */
    public static class CallReturn extends AST {
        public String from = "";
        public String to = "";
        public ArrayList<TLAExpr> args = null; // of TLAExpr

        public CallReturn(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type     |-> \"callReturn\"," + NewLine() +
                            " from     |-> \"" + from + "\"," + NewLine() +
                            " to       |-> \"" + to + "\"," + NewLine() +
                            Indent("args     |-> ") + VectorToSeqString(args)
                            + "]" + NewLine() +
                            EndIndent() +
                            EndIndent();
        }
    }

    public static class CallGoto extends AST {
        public String after = "";
        public String to = "";
        public ArrayList<TLAExpr> args = null; // of TLAExpr

        public CallGoto(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type     |-> \"callGoto\"," + NewLine() +
                            " after    |-> \"" + after + "\"," + NewLine() +
                            " to       |-> \"" + to + "\"," + NewLine() +
                            Indent("args     |-> ") + VectorToSeqString(args)
                            + "]" + NewLine() +
                            EndIndent() +
                            EndIndent();
        }
    }

    public static class Goto extends AST {
        public String to = "";

        public Goto(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            return
                    lineCol() +
                            "[type |-> \"goto\", " +
                            " to |-> \"" + to + "\"]";
        }
    }

    public static class Macro extends AST {
        public String name = "";
        public ArrayList<String> params = null; // of Strings
        public ArrayList<AST> body = null; // of Stmt

        public Macro(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[name   |-> \"" + name + "\", " + NewLine() +
                            Indent(" params |-> ") + VectorToSeqString(params) + "," +
                            EndIndent() + NewLine() +
                            Indent(" body   |-> ") + VectorToSeqString(body) + "]" +
                            EndIndent() +
                            EndIndent();
        }
    }

    public static class MacroCall extends AST {
        public String name = "";
        public ArrayList<TLAExpr> args = null; // of TLAExpr

        public MacroCall(final PcalParams pcalParams) {
            super(pcalParams);
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type |-> \"macrocall\"," + NewLine() +
                            " name |-> \"" + name + "\"," + NewLine() +
                            Indent(" args     |-> ") + VectorToSeqString(args) + "]" +
                            EndIndent() +
                            EndIndent();
        }
    }

}
