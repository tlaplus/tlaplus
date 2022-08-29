/***************************************************************************
 * CLASS PcalSymTab                                                         *
 * last modified on Fri 31 Aug 2007 at 15:44:54 PST by lamport               *
 *      modified on Tue 30 Aug 2005 at 18:30:10 UT by keith                 *
 *                                                                          *
 * This class implements the symbol table corresponding with an AST object. *
 *                                                                          *
 * symtab is the generated symbol table and is a vector of SymTableEntry.   *
 * procs is the generated vector of ProcedureEntry (which includes the      *
 *   entry point label),  and processes is the generated vector of          *
 *   ProcessEntry.                                                          *
 * If the algorithm is a uniprocess, then iPC is the initial label.         *
 *                                                                          *
 * The string disambiguateReport are TLA comments that describe how         *
 * variables and labels were renamed.                                       *
 *                                                                          *
 * The string errorreport are errors that were generated while creating     *
 * the symbol table.                                                        *
 *                                                                          *
 * The public methods of this class are the following.  Except as noted,    *
 * they are not called from outside this file.                              *
 *                                                                          *
 *     boolean InsertSym (char type, String id, String context, int line,   *
 *                             int col)                                     *
 *          Inserts the values into the symbol table. Returns true if the   *
 *          value was not in the symbol table before the insert.            *
 *                                                                          *
 *     int FindSym (char type, String id, String context)                   *
 *          Returns the index of this symbol in the symbol table.           *
 *                                                                          *
 *     boolean InsertProc (AST.Procedure ast)                               *
 *          Inserts ast.params and ast.decls into the procedure table.      *
 *          Returns true if value was not in  table before the insert.      *
 *                                                                          *
 *     boolean InsertProcess (AST.Process p)                                *
 *          Inserts an entry into the process table vector. Returns true    *
 *          is the value was not in the  table before the insert.           *
 *                                                                          *
 *     int FindSym (char type, String id, String context)                   *
 *          Returns the index of this symbol in the symbol table.           *
 *     (there are other versions of this method too).                       *
 *                                                                          *
 *     String UseThis (char type, String id, String context)                *
 *          Returns the disambiguated id of this symbol.                    *
 *     (there are other versions of this method too).                       *
 *          Called from PcalFixIDs and PcalTranslate.                       *
 *                                                                          *
 *     void Disambiguate ( )                                                *
 *          Generates the disambiguated names in the symbol table.          *
 *          Called from NotYetImplemented                                   *
 *                                                                          *
 *     String toString ( )                                                  *
 *          The symbol table represented as a string; useful for debugging  *
 *          Impossible to figure out which of the zillions of invocations   *
 *          of toString are calling this method.                            *
 *                                                                          *
 *     void CheckForDefaultInitValue ( )                                    *
 *          Reports an error if "defaultInitValue" appears in the symbol    *
 *          table.  Added by LL on 31 Aug 2007.                             *
 *                                                                          *
 * This method does not save the complete AST of the algorithm, which gives *
 * some clue to what the methods do.                                        *
 *                                                                          *
 * TO REVISE: The mapping of id to symbol, via UseThis, is sloppy.          *
 ****************************************************************************/

package pcal;

import pcal.exception.PcalSymTabException;

import java.util.ArrayList;

public class PcalSymTab {
    // Symbol types. The order  determines priority in terms of constructing a
    // disambiguous name.
    public static final int num_vtypes = 7;
    public static final int GLOBAL = 0;
    public static final int LABEL = 1;
    public static final int PROCEDURE = 2;
    public static final int PROCESS = 3;
    public static final int PROCESSVAR = 4;
    public static final int PROCEDUREVAR = 5;
    public static final int PARAMETER = 6;
    // For toString method.
    public static final String[] vtypeName = {
            "Global variable", "Label", "Procedure", "Process",
            "Process variable", "Procedure variable", "Parameter"};
    // Prepend this type-specific string to name before disambiguation.
    private static final String[] typePrefix = {"", "", "", "", "", "", ""};
    public final ArrayList<SymTabEntry> symtab;             // ArrayList of SymTabEntry
    public final ArrayList<ProcedureEntry> procs;              // ArrayList of ProcedureEntry
    public final ArrayList<ProcessEntry> processes;          // ArrayList of ProcessEntry
    public final ArrayList<String> disambiguateReport; // ArrayList of String (comments)

    // The following two arrays need to be ordered wrt the constants above.
    public String errorReport;        // Accumulated errors
    public String iPC;                // initial pc value for unip algorithm

    /**
     * As should be perfectly obvious from the name, this method constructs
     * the symbol table for the AST ast, which I presume contains all things
     * whose name must be looked up, which includes labels, variables, and
     * probably process and procedure names.
     */
    public PcalSymTab(final AST ast) throws PcalSymTabException {

        symtab = new ArrayList<>();
        iPC = null;
        disambiguateReport = new ArrayList<>();
        procs = new ArrayList<>();
        processes = new ArrayList<>();
        errorReport = "";
// Following line removed by LL on 3 Feb 2006
//        InsertSym(LABEL, "Done", "", "", 0, 0);

        InsertSym(GLOBAL, "pc", "", "", 0, 0);
        ExtractSym(ast, "");
        if (errorReport.length() > 0) throw new PcalSymTabException(errorReport);
    }

    /***************************************************
     * TRUE if inserted; false if was already in table *
     * Can not insert a variable of name x if there is *
     * a global with name x or another variable in the *
     * same context with name x.                       *
     /***************************************************/
    public boolean InsertSym(final int type,
                             final String id,
                             final String context,
                             final String cType,
                             final int line, final int col) {
        int i;
        if (type == PROCEDUREVAR || type == PROCESSVAR || type == PARAMETER) {
            i = FindSym(GLOBAL, id, "");
            if (i < symtab.size()) return false; /* GLOBAL with same id exists */
            i = FindSym(id, context);
        } else {
            i = FindSym(type, id, context);
        }
        if (i < symtab.size()) return false; /* id in same context exists */
        final SymTabEntry se = new SymTabEntry(type, id, context, cType, line, col);
        symtab.add(se);
        return true;
    }

    /***************************************************
     * Insert procedure table entry.                   *
     * TRUE if inserted; false if was already in table *
     ***************************************************/
    public boolean InsertProc(final AST.Procedure proc) {
        final int i = FindProc(proc.name);
        if (i < procs.size()) return false;
        final ProcedureEntry pe = new ProcedureEntry(proc);
        procs.add(pe);
        return true;
    }

    /***************************************************
     * Insert process table entry.                     *
     * TRUE if inserted; false if was already in table *
     ***************************************************/
    public boolean InsertProcess(final AST.Process p) {
        final int i = FindProcess(p.name);
        if (i < processes.size()) return false;
        final ProcessEntry pe = new ProcessEntry(p);
        processes.add(pe);
        return true;
    }

    /*********************************************************
     * Various ways to look up something in the symbol table.*
     * Returns the index in the table. If the index equals   *
     * symtab.size() (which makes no sense), then it isn't   *
     * in the symbol table.                                  *
     *********************************************************/
    public int FindSym(final int type, final String id, final String context) {
        int i = 0;
        while (i < symtab.size()) {
            final SymTabEntry se = symtab.get(i);
            if (se.id.equals(id) && se.context.equals(context)
                    && se.type == type) return i;
            i = i + 1;
        }
        return i;
    }

    /*********************************************************
     * Returns first it finds with id and context, no matter *
     * what type it is.                                      *
     *********************************************************/
    public int FindSym(final String id, final String context) {
        int i = 0;
        while (i < symtab.size()) {
            final SymTabEntry se = symtab.get(i);
            if (se.id.equals(id) && se.context.equals(context))
                return i;
            i = i + 1;
        }
        return i;
    }

    /*********************************************************
     * Returns index of entry in procedure table. If it isn't*
     * in the table, then returns procs.size().              *
     *********************************************************/
    public int FindProc(final String id) {
        int i = 0;
        while (i < procs.size()) {
            final ProcedureEntry pe = procs.get(i);
            if (pe.name.equals(id)) return i;
            i = i + 1;
        }
        return i;
    }

    /*********************************************************
     * Returns index of entry in process table. If it isn't  *
     * in the table, then returns procs.size().              *
     *********************************************************/
    public int FindProcess(final String id) {
        int i = 0;
        while (i < processes.size()) {
            final ProcessEntry pe = processes.get(i);
            if (pe.name.equals(id)) return i;
            i = i + 1;
        }
        return i;
    }

    /*********************************************************
     * Routines for returning disambiguated names.           *
     *********************************************************/

    /* Return the disambiguated name for a type X id X context */
    public String UseThis(final int type, final String id, final String context) {
        final int i = FindSym(type, id, context);
        if (i == symtab.size()) return id;
        else return symtab.get(i).useThis;
    }

    /*********************************************************
     * Given a variable referenced in a context. First get   *
     * the entry in the context. If no such variable, then   *
     * see if a global one exists. If not, then use it       *
     * undisambiguated.                                      *
     * NOTE: Stop using FindSym; it's a bad hack.            *
     *********************************************************/
    public String UseThisVar(final String id, final String context) {
        SymTabEntry se;
        int i = FindSym(id, context);
        if (i == symtab.size()) return id;
        se = symtab.get(i);
        if (se.type == GLOBAL || se.type == PROCESSVAR
                || se.type == PROCEDUREVAR || se.type == PARAMETER)
            return se.useThis;
        i = FindSym(id, "");
        if (se.type == GLOBAL) return se.useThis;
        return id;
    }

    /*********************************************************
     * TRUE if id is ambiguous.                              *
     *********************************************************/
    private boolean Ambiguous(final String id) {
        int i = 0;
        boolean found = false;
        while (i < symtab.size()) {
            final SymTabEntry se = symtab.get(i);
            if (se.useThis.equals(id)) {
                if (!found) found = true;
                else return true;
            }
            i = i + 1;
        }
        return false;
    }

    /**************************************************************************
     * Disambiguating names. First, names are prepended with a type specific  *
     * string, defined in the array typePrefix. Then, the names are           *
     * considered in increasing type order. The first type in this order      *
     * are left unchanged. Then, each other order has a suffix appended to it *
     * until it is unique from all the current symbol names (both renamed and *
     * not yet renamed). The suffix is a prefix of "_context" where "context" *
     * is the context in which the name is defined (which is the empty string *
     * for the global context). If it is still not unique after all of the    *
     * context is appended, then the decimal representation of the name type  *
     * is added repeatedly until it is unambiguous.                           *
     **************************************************************************/
    public void Disambiguate() {
        for (int vtype = 0; vtype <= num_vtypes; vtype++)
            for (final SymTabEntry se : symtab) {
                if (se.type == vtype) {
                    se.useThis = typePrefix[vtype] + se.id;
                    int suffixLength = 0;
                    while (vtype > 0 && Ambiguous(se.useThis)) {
                        suffixLength = suffixLength + 1;
                        if (suffixLength == 1) se.useThis = se.useThis + "_";
                        else if (suffixLength > se.context.length() + 1)
                            se.useThis = se.useThis + vtype;
                        else se.useThis = se.useThis
                                    + se.context.charAt(suffixLength - 2);
                    }
                    if (!se.id.equals(se.useThis))
                        disambiguateReport.add(
                                "\\* " +
                                        vtypeName[se.type] +
                                        " " +
                                        se.id +
                                        ((se.context.length() == 0)
                                                ? ""
                                                : (" of " + se.cType + " " + se.context)) +
                                        " at line " + se.line + " col " + se.col +
                                        " changed to " +
                                        se.useThis);
                }
            }
    }

    public String toString() {
        int i = 0;
        final StringBuilder result = new StringBuilder("[");
        while (i < symtab.size()) {
            final SymTabEntry se = symtab.get(i);
            if (i > 0) result.append(", ");
            result.append(vtypeName[se.type]).append(" ").append(se.context).append(':').append(se.id).append(" line ").append(se.line).append(" col ").append(se.col).append(" (").append(se.useThis).append(")");
            i = i + 1;
        }
        return result + "]";
    }

    /********************************
     * Type generic extract routine *
     ********************************/
    private void ExtractSym(final AST ast, final String context) {
        if (ast instanceof AST.Uniprocess u)
            ExtractUniprocess(u, context);
        else if (ast instanceof AST.Multiprocess m)
            ExtractMultiprocess(m, context);
        else PcalDebug.ReportBug("Unexpected AST type.");
    }

    private void ExtractStmt(final AST ast, final String context, final String cType) {
        if (ast instanceof AST.While w)
            ExtractWhile(w, context, cType);
        else if (ast instanceof AST.Assign assign)
            ExtractAssign(assign, context, cType);
        else if (ast instanceof AST.If ifObj)
            ExtractIf(ifObj, context, cType);
        else if (ast instanceof AST.With withObj)
            ExtractWith(withObj, context, cType);
        else if (ast instanceof AST.When whenObj)
            ExtractWhen(whenObj, context, cType);
        else if (ast instanceof AST.PrintS printS)
            ExtractPrintS(printS, context, cType);
        else if (ast instanceof AST.Assert assertObj)
            ExtractAssert(assertObj, context, cType);
        else if (ast instanceof AST.Skip skipObj)
            ExtractSkip(skipObj, context, cType);
        else if (ast instanceof AST.LabelIf labelIf)
            ExtractLabelIf(labelIf, context, cType);
        else if (ast instanceof AST.Call callObj)
            ExtractCall(callObj, context, cType);
        else if (ast instanceof AST.Return returnObj)
            ExtractReturn(returnObj, context, cType);
        else if (ast instanceof AST.CallReturn cr)
            ExtractCallReturn(cr, context, cType);
        else if (ast instanceof AST.CallGoto callGoto)
            ExtractCallGoto(callGoto, context, cType);
        else if (ast instanceof AST.Goto gotoObj)
            ExtractGoto(gotoObj, context, cType);

        /*******************************************************************
         * Handling of Either and LabelEither added by LL on 24 Jan 2006.   *
         *******************************************************************/
        else if (ast instanceof AST.Either either)
            ExtractEither(either, context, cType);
        else if (ast instanceof AST.LabelEither labelEither)
            ExtractLabelEither(labelEither, context, cType);
        else PcalDebug.ReportBug("Unexpected AST type " + ast);
    }

    /**********************************************
     * Type specific extraction routines.         *
     **********************************************/

    private void ExtractUniprocess(final AST.Uniprocess ast, final String context) {
// On 3 Feb 2006, LL moved insertion of "stack" before extraction of
// global variable decls, so use of "stack" as a global variable would be
// detected.
        if (ast.prcds.size() > 0) InsertSym(GLOBAL, "stack", "", "", 0, 0);
        for (int i = 0; i < ast.decls.size(); i++)
            ExtractVarDecl(ast.decls.get(i), "");
        for (int i = 0; i < ast.prcds.size(); i++)
            ExtractProcedure(ast.prcds.get(i), "");
        if (ast.body.size() > 0) {
            final AST.LabeledStmt ls = (AST.LabeledStmt) ast.body.get(0);
            iPC = ls.label;
        }
        for (int i = 0; i < ast.body.size(); i++) {
            ExtractLabeledStmt((AST.LabeledStmt) ast.body.get(i), "", "");
        }
    }

    private void ExtractMultiprocess(final AST.Multiprocess ast, final String context) {
// On 3 Feb 2006, LL moved insertion of "stack" before extraction of
// global variable decls, so use of "stack" as a global variable would be
// detected.
        if (ast.prcds.size() > 0) InsertSym(GLOBAL, "stack", "", "", 0, 0);
        for (int i = 0; i < ast.decls.size(); i++)
            ExtractVarDecl(ast.decls.get(i), "");
        for (int i = 0; i < ast.prcds.size(); i++)
            ExtractProcedure(ast.prcds.get(i), "");
        for (int i = 0; i < ast.procs.size(); i++)
            ExtractProcess(ast.procs.get(i), "");
    }

    private void ExtractProcedure(final AST.Procedure ast, final String context) {

        if (!InsertProc(ast))
            errorReport = errorReport + "\nProcedure " + ast.name +
                    " redefined at line " + ast.line + ", column " + ast.col;
        @SuppressWarnings("unused") final boolean b = InsertSym(PROCEDURE,
                ast.name,
                context,
                "procedure",
                ast.line,
                ast.col);
        for (int i = 0; i < ast.decls.size(); i++)
            ExtractPVarDecl(ast.decls.get(i), ast.name);
        for (int i = 0; i < ast.params.size(); i++)
            ExtractParamDecl(ast.params.get(i), ast.name);
        for (int i = 0; i < ast.body.size(); i++)
            ExtractLabeledStmt((AST.LabeledStmt) ast.body.get(i),
                    ast.name,
                    "procedure");
    }

    private void ExtractProcess(final AST.Process ast, final String context) {
        @SuppressWarnings("unused") final boolean b;
        if (!InsertProcess(ast))
            errorReport = errorReport + "\nProcess " + ast.name +
                    " redefined at line " + ast.line + ", column " + ast.col;
        b = InsertSym(PROCESS, ast.name, context, "process", ast.line, ast.col);
        for (int i = 0; i < ast.decls.size(); i++)
            ExtractVarDecl(ast.decls.get(i), ast.name);
        for (int i = 0; i < ast.body.size(); i++)
            ExtractLabeledStmt((AST.LabeledStmt) ast.body.get(i),
                    ast.name,
                    "process");
    }

    private void ExtractVarDecl(final AST.VarDecl ast, final String context) {
        final int vtype = (context.equals("")) ? GLOBAL : PROCESSVAR;
        if (!InsertSym(vtype, ast.var, context, "process", ast.line, ast.col))
            errorReport = errorReport + "\n" + vtypeName[vtype] + " " + ast.var +
                    " redefined at line " + ast.line + ", column " + ast.col;
    }

    private void ExtractPVarDecl(final AST.PVarDecl ast, final String context) {
        if (!InsertSym(PROCEDUREVAR,
                ast.var,
                context,
                "procedure",
                ast.line,
                ast.col))
            errorReport = errorReport + "\nProcedure variable " + ast.var +
                    " redefined at line " + ast.line + ", column " + ast.col;
    }

    private void ExtractParamDecl(final AST.PVarDecl ast, final String context) {
        if (!InsertSym(PARAMETER,
                ast.var,
                context,
                "procedure",
                ast.line,
                ast.col))
            errorReport = errorReport + "\nParameter " + ast.var +
                    " redefined at line " + ast.line + ", column " + ast.col;
    }

    private void ExtractLabeledStmt(final AST.LabeledStmt ast,
                                    final String context,
                                    final String cType) {
        if (!InsertSym(LABEL, ast.label, context, cType, ast.line, ast.col))
            errorReport = errorReport + "\nLabel " + ast.label +
                    " redefined at line " + ast.line + ", column " + ast.col;
        for (int i = 0; i < ast.stmts.size(); i++)
            ExtractStmt(ast.stmts.get(i), context, cType);
    }

    private void ExtractWhile(final AST.While ast, final String context, final String cType) {
        for (int i = 0; i < ast.unlabDo.size(); i++)
            ExtractStmt(ast.unlabDo.get(i), context, cType);
        for (int i = 0; i < ast.labDo.size(); i++)
            ExtractLabeledStmt((AST.LabeledStmt) ast.labDo.get(i),
                    context,
                    cType);
    }

    private void ExtractAssign(final AST.Assign ast, final String context, final String cType) {
    }

    private void ExtractIf(final AST.If ast, final String context, final String cType) {
        for (int i = 0; i < ast.Then.size(); i++)
            ExtractStmt(ast.Then.get(i), context, cType);
        for (int i = 0; i < ast.Else.size(); i++)
            ExtractStmt(ast.Else.get(i), context, cType);
    }

    private void ExtractWith(final AST.With ast, final String context, final String cType) {
        for (int i = 0; i < ast.Do.size(); i++)
            ExtractStmt(ast.Do.get(i), context, cType);
    }

    private void ExtractWhen(final AST.When ast, final String context, final String cType) {
    }

    private void ExtractPrintS(final AST.PrintS ast, final String context, final String cType) {
    }

    private void ExtractAssert(final AST.Assert ast, final String context, final String cType) {
    }

    private void ExtractSkip(final AST.Skip ast, final String context, final String cType) {
    }

    private void ExtractLabelIf(final AST.LabelIf ast, final String context, final String cType) {
        for (int i = 0; i < ast.unlabThen.size(); i++)
            ExtractStmt(ast.unlabThen.get(i), context, cType);
        for (int i = 0; i < ast.labThen.size(); i++)
            ExtractLabeledStmt((AST.LabeledStmt) ast.labThen.get(i),
                    context,
                    cType);
        for (int i = 0; i < ast.unlabElse.size(); i++)
            ExtractStmt(ast.unlabElse.get(i), context, cType);
        for (int i = 0; i < ast.labElse.size(); i++)
            ExtractLabeledStmt((AST.LabeledStmt) ast.labElse.get(i),
                    context,
                    cType);
    }

    private void ExtractCall(final AST.Call ast, final String context, final String cType) {
    }

    private void ExtractReturn(final AST.Return ast, final String context, final String cType) {
    }

    private void ExtractCallReturn(final AST.CallReturn ast,
                                   final String context,
                                   final String cType) {
    }

    private void ExtractCallGoto(final AST.CallGoto ast,
                                 final String context,
                                 final String cType) {
    }

    private void ExtractGoto(final AST.Goto ast, final String context, final String cType) {
    }

    /***********************************************************************
     * Handling of Either and LabelEither added by LL on 24 Jan 2006.       *
     ***********************************************************************/
    private void ExtractEither(final AST.Either ast, final String context, final String cType) {
        for (int i = 0; i < ast.ors.size(); i++) {
            @SuppressWarnings("unchecked") final ArrayList<AST> orClause = (ArrayList<AST>) ast.ors.get(i);
            for (AST value : orClause) ExtractStmt(value, context, cType);
        }
    }

    private void ExtractLabelEither(final AST.LabelEither ast, final String context,
                                    final String cType) {
        for (int i = 0; i < ast.clauses.size(); i++) {
            final AST.Clause orClause = ast.clauses.get(i);
            for (int j = 0; j < orClause.unlabOr.size(); j++)
                ExtractStmt(orClause.unlabOr.get(j),
                        context, cType);
            for (int j = 0; j < orClause.labOr.size(); j++)
                ExtractLabeledStmt((AST.LabeledStmt)
                                orClause.labOr.get(j),
                        context, cType);
        }
    }

    /************************************************************************
     * Reports an error if "defaultInitValue" appears in the symbol table.   *
     * Added by LL on 31 Aug 2007.                                           *
     ************************************************************************/
    public void CheckForDefaultInitValue() throws PcalSymTabException {
        StringBuilder errors = new StringBuilder();
        for (final SymTabEntry se : symtab) {
            if (se.id.equals("defaultInitValue")) {
                if (errors.toString().equals("")) {
                    errors = new StringBuilder("Cannot use `defaultInitValue' as ");
                } else {
                    errors.append(" or ");
                }
                errors.append(vtypeName[se.type]).append(" name");
            }
        }
        if (!errors.toString().equals("")) {
            throw new PcalSymTabException(errors.toString());
        }
    }

    /* NESTED CLASS: Symbol table entries */
    public static class SymTabEntry {
        public final int type;       // variable type
        // can be GLOBAL, LABEL, PROCEDURE, PROCESS, PROCESSVAR,
        // PROCEDUREVAR, or PARAMETER, declared above.
        public final String id;      // original name
        public final String context; // where defined
        // experimentation shows that context is:
        //    "" if cType = ""
        //    the name of a process if cType = "process"
        //    the name of a procedure if cType = "procedure"
        public final String cType;   // procedure, process or empty
        public final int line;       // line where defined
        public final int col;        // column where defined
        public String useThis; // Disambiguated name

        public SymTabEntry(final int type,
                           final String id,
                           final String context,
                           final String cType,
                           final int line,
                           final int col) {
            this.type = type;
            this.id = id;
            this.context = context;
            this.cType = cType;
            this.line = line;
            this.col = col;
            this.useThis = id;
        }

        /**
         * For debugging:
         */
        public String toString() {
            return "[id: " + this.id + ", usethis: " + this.useThis +
                    ", line: " + this.line + ", col:" + this.col +
                    ", type: " + this.type + ", context: " + this.context + "]";
        }
    } /* End of SymTabEntry */

    /* NESTED CLASS: Procedure table entries */
    public static class ProcedureEntry {
        public final ArrayList<AST.PVarDecl> params;  // of PVarDecl
        public final ArrayList<AST.PVarDecl> decls;   // of PVarDecl
        public final AST.Procedure ast; // AST of the procedure
        public String name;    // Procedure name
        public String iPC;     // initial label of procedure
        // Added 13 Jan 2011 by LL

        public ProcedureEntry(final AST.Procedure p) {
            this.name = p.name;
            this.params = p.params;
            this.decls = p.decls;
            this.ast = p;
            if (p.body.size() == 0) this.iPC = null;
            else {
                final AST.LabeledStmt ls = (AST.LabeledStmt) p.body.get(0);
                this.iPC = ls.label;
            }
        }
    } /* End of ProcedureEntry */

    /* NESTED CLASS: Process table entries */
    public static class ProcessEntry {
        public final boolean isEq;     // true means "=", false means "\\in"
        public final TLAExpr id;       // set of identifiers or identifier
        public final ArrayList<?> decls;     // of ParDecl
        public final AST.Process ast; // AST of the procedure
        public String name;      // Process name
        public String iPC;       // Initial pc of this process
        // Added 13 Jan 2011 by LL

        public ProcessEntry(final AST.Process p) {
            this.name = p.name;
            this.isEq = p.isEq;
            this.id = p.id;
            this.decls = p.decls;
            this.ast = p;
            if (p.body.isEmpty()) this.iPC = null;
            else {
                final AST.LabeledStmt ls = (AST.LabeledStmt) p.body.get(0);
                this.iPC = ls.label;
            }
        }
    } /* End of ProcessEntry */

}
