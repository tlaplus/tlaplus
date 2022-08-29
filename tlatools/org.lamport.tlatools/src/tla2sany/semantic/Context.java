// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

// Last modified on Tue 15 May 2007 at  9:35:56 PST by lamport
/***************************************************************************
 * 2 Mar 2007: enum <- Enum                                                 *
 ***************************************************************************/

package tla2sany.semantic;

import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.st.Location;
import tla2sany.utilities.Strings;
import util.UniqueString;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Enumeration;
import java.util.Hashtable;

// A context contains def/declNodes only.
// Implements a simple context for symbol decls and defs. Also
// supports the intial (or global) context of built-in operators.

// The pair construct is used to maintain a linked list of
// definitions.  This in turn will allow the extraction of a full
// context from anywhere in the tree, from the englobing definition.

// Merging: different forms of merging should be offered, depending
// what is being merged.  We always start with a clone of the
// initialContext.  Alterwards, we can Extend or Instantiate.  In one
// case, we import defs and decls; in the other, only defs; but we
// need to keep track of substitutions.

/**
 * A Context is an assignment of meanings to module names and to
 * symbol names, where a meaning is a SemNode.  At the moment, there
 * seems to be no need to provide methods to manipulate or do anything
 * with contexts except pass them to the Front End.
 */
public class Context implements ExploreNode {

    private final ExternalModuleTable exMT;   // The external ModuleTable that this context's SymbolTable
    private final Errors errors;      // Object in which to register errors
    private final Hashtable<Object, Pair> table;       // Mapping from symbol name to Pair's that include SymbolNode's
    // belongs to is null for global contex shared by all modules.
    private Pair lastPair;    // Pair added last to the this.table
    /**
     * exMT is the ExternalModuleTable containing the module whose
     * SymbolTable this Context is part of (or null).
     */
    public Context(final ExternalModuleTable mt, final Errors errs) {
        table = new Hashtable<>();
        this.exMT = mt;
        this.errors = errs;
        this.lastPair = null;
    }

    private static String kindOfNode(final SymbolNode symbol) {
        if (symbol instanceof OpDefNode) {
            return "definition";
        }
        if (symbol instanceof FormalParamNode) {
            return "definition";
        }
        return "declaration";
    }

    public boolean isBuiltIn(final ExploreNode exploreNode) {
        final Collection<Pair> pairs = table.values();
        for (final Pair p : pairs) {
            if (exploreNode == p.info) {
                return true;
            }
        }
        return false;
    }

    public Errors getErrors() {
        return errors;
    }

    // Adds a symbol to the (unique) initialContext; aborts if already there
    public void addGlobalSymbol(final UniqueString name, final SymbolNode sn, final Errors errors)
            throws AbortException {
        if (getSymbol(name) != null) {
            errors.addAbort(Location.nullLoc,
                    "Error building initial context: Multiply-defined builtin operator " +
                            name + " at " + sn, false);
        } else {
            addSymbolToContext(name, sn);
        }
    }

    /**
     * Returns symbol node associated with "name" in this Context, if
     * one exists; else returns null
     */
    public SymbolNode getSymbol(final Object name) {
        final Pair r = table.get(name);
        if (r != null) {
            return r.info;
        }
        return null;
    }

    /**
     * Adds a (UniqueString, SymbolNode) pair to this context; no-op if
     * already present
     *
     * @param name the UniqueString representing the string, see {@link UniqueString#uniqueStringOf(String)}
     * @param s    the symbol node to be put in
     */
    public void addSymbolToContext(final Object name, final SymbolNode s) {
        table.put(name, new Pair(s));    // Links to & updates lastPair
    }

    /**
     * Returns Enumeration of the elements of the Hashtable "Table",
     * which are pair of the form (Pair link, SymbolNode sn)
     */
    public Enumeration<Pair> content() {
        return table.elements();
    }

    /**
     * Returns a new ContextSymbolEnumeration object, which enumerates
     * the SymbolNodes of THIS context
     */
    public ContextSymbolEnumeration getContextSymbolEnumeration() {
        return new ContextSymbolEnumeration();
    }

    /**
     * Returns a ArrayList of those SymbolNodes in this Context that are
     * instances of class "template" (or one of its subclasses)
     */
    @SuppressWarnings("unchecked")
    public <T> ArrayList<T> getByClass(final Class<T> template) {
        final ArrayList<T> result = new ArrayList<>();
        final Enumeration<Pair> list = table.elements();
        while (list.hasMoreElements()) {
            final Pair elt = list.nextElement();
            if (template.isInstance(elt.info)) {
                result.add((T) elt.info);
            }
        }
        return result;
    }

    /**
     * Returns a ArrayList of those SymbolNodes in this Context that are
     * instances of class OpDefNode and that are NOT of kind BuiltInKind
     * or ModuleInstanceKind
     */
    public ArrayList<OpDefNode> getOpDefs() {
        // SZ Apr 21, 2009: not used instance
        // Class template = OpDefNode.class;
        Pair nextPair = lastPair;

        final ArrayList<OpDefNode> result = new ArrayList<>();
        while (nextPair != null) {
            if (nextPair.info instanceof OpDefNode &&     // true for superclasses too.
                    nextPair.info.getKind() != ASTConstants.ModuleInstanceKind &&
                    nextPair.info.getKind() != ASTConstants.BuiltInKind)
                result.add((OpDefNode) (nextPair.info));
            nextPair = nextPair.link;
        }
        return result;
    }

    /*************************************************************************
     * Returns a ArrayList of those SymbolNodes in this Context that are         *
     * instances of class ThmOrAssumpDefNode or ModuleInstanceKind            *
     * Code copied from getOpDefs().                                          *
     *************************************************************************/
    public ArrayList<ThmOrAssumpDefNode> getThmOrAssDefs() {
        // SZ Apr 21, 2009: not used instance
        // Class template = ThmOrAssumpDefNode.class;
        Pair nextPair = lastPair;

        final ArrayList<ThmOrAssumpDefNode> result = new ArrayList<>();
        while (nextPair != null) {
            if (nextPair.info instanceof ThmOrAssumpDefNode) {
                result.add((ThmOrAssumpDefNode) (nextPair.info));
            }
            nextPair = nextPair.link;
        }
        return result;
    }

    /**
     * Returns ArrayList of OpDeclNodes that represent CONSTANT declarations
     */
    public ArrayList<SemanticNode> getConstantDecls() {
        final Class<? extends SemanticNode> templateClass = OpDeclNode.class;
        final Enumeration<Pair> list = table.elements();

        final ArrayList<SemanticNode> result = new ArrayList<>();
        while (list.hasMoreElements()) {
            final Pair elt = list.nextElement();
            if (templateClass.isInstance(elt.info) &&     // true for superclasses too.
                    elt.info.getKind() == ASTConstants.ConstantDeclKind)
                result.add(elt.info);

        }
        return result;
    }

    /* Returns ArrayList of OpDeclNodes that represent CONSTANT declarations  */
    public ArrayList<SemanticNode> getVariableDecls() {
        final Class<? extends SemanticNode> templateClass = OpDeclNode.class;
        final Enumeration<Pair> list = table.elements();

        final ArrayList<SemanticNode> result = new ArrayList<>();
        while (list.hasMoreElements()) {
            final Pair elt = list.nextElement();
            if (templateClass.isInstance(elt.info) &&     // true for superclasses too.
                    elt.info.getKind() == ASTConstants.VariableDeclKind)
                result.add(elt.info);
        }
        return result;
    }

    /**
     * Returns a ArrayList of those SymbolNodes in this Context that are
     * instances of class ModuleNode
     */
    public ArrayList<SemanticNode> getModDefs() {
        final Class<? extends SemanticNode> template = ModuleNode.class;
        final Enumeration<Pair> list = table.elements();

        final ArrayList<SemanticNode> result = new ArrayList<>();
        while (list.hasMoreElements()) {
            final Pair elt = list.nextElement();
            if (template.isInstance(elt.info))    // true for superclasses too.
                result.add(elt.info);
        }
        return result;
    }

    /**
     * Restricted Context merge.  Invoked once in Generator class.
     * Merges Context "ct" into THIS Context, except for local symbols
     * in "ct" Two symbols clash if they have the same name AND a different
     * class; that is an error.  If they have the same name and class, they
     * are considered to be two inheritances of the same (or at least
     * compatible) declarations, and there is only a warning.  Returns
     * true if there is no error or there are only warnings; returns
     * false if there is an error.
     * <p>
     * The original implementation added the elements of Context ct to
     * this context in the inverse order as they appear in ct.  It was
     * changed on 12 Mar 2013 by LL to add them in the same order.
     * <p>
     * Note that the return value is never used in our code base. (2020.03.06)
     */
    public boolean mergeExtendContext(final Context ct) {
        if (ct.lastPair == null) {
            // If the context represents an inner module that defines no EXTENDS, ct.lastPair will be null
            return true;
        }

        boolean erc = true;
        // check locality, and multiplicity
        // the .reversePairList was added to the following statement
        // by LL on 12 Mar 2013
        Pair p = ct.lastPair.reversePairList();
        while (p != null) {
            // Walk back along the list of pairs added to Context "ct"
            final SymbolNode sn = p.info;

            // Ignore local symbols in Context "ct"
            if (!sn.isLocal()) {
                final Object sName;
                if (sn instanceof ModuleNode) {
                    sName = new SymbolTable.ModuleName(sn.getName());
                } else {
                    sName = sn.getName();
                }

                if (!table.containsKey(sName)) {
                    // If this context DOES NOT contain this name, add it:
                    table.put(sName, new Pair(sn));
                } else {
                    // If this Context DOES contain this name
                    final SymbolNode symbol = table.get(sName).info;
                    if (symbol != sn) {
                        // if the two SymbolNodes with the same name are distinct nodes,
                        // We issue a warning or do nothing if they are instances of the same Java
                        // class--i.e. FormalParamNode, OpDeclNode, OpDefNode, or ModuleNode--doing
                        // nothing if they are both definitions coming from the same module.
                        // otherwise, it is considered to be an error.
                        // Option of doing nothing if from same module added by LL on 31 Oct 2012 to
                        // fix problem caused by the same module being both EXTENDed and imported with
                        // a LOCAL INSTANCE. Previously, it always added the warning.
                        if (symbol.getClass() == sn.getClass()) {
                            if (!symbol.sameOriginallyDefinedInModule(sn)) {
                                errors.addWarning(sn.getTreeNode().getLocation(),
                                        "Warning: the " + kindOfNode(symbol) + " of '" + sName.toString()
                                                + "' conflicts with \nits " + kindOfNode(symbol) + " at "
                                                + symbol.getTreeNode().getLocation() + ".");
                            }
                        } else {
                            errors.addError(sn.getTreeNode().getLocation(),
                                    "The " + kindOfNode(symbol) + " of '" + sName.toString() + "' conflicts with \nits "
                                            + kindOfNode(symbol) + " at " + symbol.getTreeNode().getLocation() + ".");

//                               "Incompatible multiple definitions of symbol '" +
//                               sName.toString() +
//                               "'; \nthe conflicting declaration is at " +
//                               symbol.getTreeNode().getLocation()+ ".");
                            erc = false;
                        } // end else
                    } // end if
                } // end else
            }
            p = p.link;
        }
        return erc;
    }

    // The following is a revised version of mergeExendContext that
    // fixes an apparent bug in the original in which elements of
    // Context ct are added to this context in the inverse order.
    // Corrected version written by LL on 12 Mar 2013

    /**
     * Returns a duplicate of this Context.  Called once from
     * SymbolTable class.  The tricky part is duplicating the
     * linked-list of Pairs starting from this.lastpair.
     */
    public Context duplicate(final ExternalModuleTable exMT) {    // Added argument exMT (DRJ)
        final Context dup = new Context(exMT, errors);
        Pair p = this.lastPair;
        Pair current = null;
        boolean firstTime = true;

        while (p != null) {
            if (firstTime) {
                current = new Pair(null, p.info);     // Does NOT link to or update this.lastPair
                dup.lastPair = current;
                firstTime = false;
            } else {
                current.link = new Pair(null, p.info); // Note: causes sharing of reference in link.info
                current = current.link;
            }
            dup.table.put(current.info.getName(), current);
            p = p.link;
        }
        return dup;
    }

    /**
     * toString, levelDataToString, and walkGraph methods to implement
     * ExploreNode interface
     */
    @Override
    public String levelDataToString() {
        return "Dummy level string";
    }

    @Override
    public String toString(final int depth) {
        return "Please use Context.getContextEntryStringArrayList()" +
                " instead of Context.toString()";
    }

    /*************************************************************************
     * When trying to use SANY's -d (debug) option, this method throws a      *
     * NullPointerException if the spec has an inner module.  See the         *
     * comment in the walkGraph method of this file for a bit more            *
     * information.                                                           *
     *************************************************************************/
    public ArrayList<String> getContextEntryStringArrayList(final int depth, final boolean b) {
        final ArrayList<String> ctxtEntries = new ArrayList<>(100);  // ArrayList of Strings
        final Context naturalsContext =
                exMT.getContext(UniqueString.uniqueStringOf("Naturals"));

        if (depth <= 0) return ctxtEntries;

        Pair p = lastPair;
        while (p != null) {
            final UniqueString key = p.info.getName();

            // If b is false, don't bother printing the initialContext--too long--
            // and, don't bother printing elements of the Naturals module either
            if (b || (!table.containsKey(key) &&
                    (naturalsContext == null ||
                            !naturalsContext.table.containsKey(key)))) {
                final SymbolNode symbNode = (table.get(key)).info;
                ctxtEntries.add("\nContext Entry: " + key.toString() + "  "
                        + symbNode.myUID + " "
                        + Strings.indentSB(2, (symbNode.toString(depth - 1))));
            }
            p = p.link;
        }

        // Reverse the order of elements in the ArrayList so they print properly
        String obj;
        final int n = ctxtEntries.size();
        for (int i = 0; i < n / 2; i++) {
            obj = ctxtEntries.get(i);
            ctxtEntries.set(i, ctxtEntries.get(n - 1 - i));
            ctxtEntries.set(n - 1 - i, obj);
        }
        return ctxtEntries;
    }

    @Override
    public void walkGraph(final Hashtable<Integer, ExploreNode> semNodesTable, final ExplorerVisitor visitor) {
        visitor.preVisit(this);
        UniqueString key;
        final Enumeration<?> e = table.keys();

        while (e.hasMoreElements()) {
            /*********************************************************************
             * Bug fix attempted by LL on 19 Apr 2007.                            *
             *                                                                    *
             * The original code expected Enum.nextElement() to be a              *
             * UniqueString.  However, it can also be a SymbolTable.ModuleName    *
             * for an inner module.  I attempted to fix that by just getting key  *
             * from the right place in the object.  However, that caused a        *
             * NullPointerException because table.get(key) equaled null.  So, I   *
             * just had the code print a warning and ignore the entry for the     *
             * inner module.  However, this caused a NullPointerException in      *
             * getContextEntryStringArrayList later on.  I decided to stop wasting   *
             * time on this.                                                      *
             *********************************************************************/
            final Object next = e.nextElement();
            if (next instanceof SymbolTable.ModuleName) {
                key = ((SymbolTable.ModuleName) next).name;
                System.out.println("Bug in debugging caused by inner module " +
                        key.toString());
                System.out.println("SANY will throw a null pointer exception.");
            } else {
                key = (UniqueString) next;
                table.get(key).info.walkGraph(semNodesTable, visitor);
            }
            visitor.postVisit(this);
        }

    }

    /* Returns a ArrayList of strings */

    class Pair {
        final SymbolNode info;
        Pair link;

        // Note: Does not set lastPair
        Pair(final Pair lnk, final SymbolNode inf) {
            this.link = lnk;
            this.info = inf;
        }

        // Note: Does set lastPair
        Pair(final SymbolNode inf) {
            this.link = lastPair;
            this.info = inf;
            lastPair = this;
        }

        public SymbolNode getSymbol() {
            return this.info;
        }

        /**
         * For a Pair node pr, let List(pr) be the sequence of
         * Pair nodes of length n defined by
         * <p>
         * List(pr)[1] = pr
         * List(pr)[n].link = null
         * \A i \in 1..(n-1) : List(pr)[i+1] = List(pr)[i].link
         * <p>
         * Then reversePairList() is a Pair node such that
         * List(reversePairList()) has the same length n as
         * List(this), and whose elements are new Pair nodes such
         * that
         * <p>
         * \A i \in 1..n : List(reversePairList())[i].info =
         * List(this)[n-i+1].info
         */
        public Pair reversePairList() {
            Pair curResult = new Pair(null, this.info);
            Pair nextOriginal = this.link;
            while (nextOriginal != null) {
                curResult = new Pair(curResult, nextOriginal.info);
                nextOriginal = nextOriginal.link;
            }
            return curResult;
        }
    } // class Pair

    public class ContextSymbolEnumeration {

        final Enumeration<Pair> e = Context.this.content();

        public boolean hasMoreElements() {
            return e.hasMoreElements();
        }

        public SymbolNode nextElement() {
            return e.nextElement().getSymbol();
        }

    }

}
