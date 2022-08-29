// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:29:56 PST by lamport
//      modified on Thu Aug 23 17:46:39 PDT 2001 by yuanyu

package tlc2.tool.impl;

import tla2sany.parser.*;
import tlc2.output.EC;
import tlc2.tool.ConfigFileException;
import tlc2.value.IValue;
import tlc2.value.ValueConstants;
import tlc2.value.impl.*;
import util.*;

import java.io.IOException;
import java.io.InputStream;
import java.io.Serializable;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Stores information from user's model configuration file.
 * <p>
 * TODO we should move from Hashtable to HashMap (we should probably also stop using our own collection implmentations
 * 			like {@link ArrayList}.)
 * TODO we're storing a heterogeneous mishmash in the values of configTbl - sometimes a ArrayList, sometimes a String, sometime
 * 			that ArrayList has only String instances, sometimes is has a String instance and Value subclasses, ... it would
 * 			be nice were the design cleaner.
 *
 * @author Yuan Yu, Leslie Lamport
 */
public class ModelConfig implements ValueConstants, Serializable {
    public static final String CheckDeadlock = "CHECK_DEADLOCK";
    // keywords of the configuration file.
    // CAREFUL: HAVE TO BE IN CONFIGTBL FOR PARSING TO WORK!
    private static final String Constant = TLAConstants.KeyWords.CONSTANT;
    private static final String Constants = TLAConstants.KeyWords.CONSTANTS;
    private static final String Constraint = "CONSTRAINT";
    private static final String Constraints = "CONSTRAINTS";
    private static final String ActionConstraint = TLAConstants.KeyWords.ACTION_CONSTRAINT;
    private static final String ActionConstraints = ActionConstraint + 'S';
    private static final String Invariant = TLAConstants.KeyWords.INVARIANT;
    private static final String Invariants = Invariant + 'S';
    private static final String Init = TLAConstants.KeyWords.INIT;
    private static final String Next = TLAConstants.KeyWords.NEXT;
    private static final String View = "VIEW";
    private static final String Symmetry = TLAConstants.KeyWords.SYMMETRY;
    private static final String Spec = TLAConstants.KeyWords.SPECIFICATION;
    private static final String Prop = TLAConstants.KeyWords.PROPERTY;
    private static final String Props = "PROPERTIES";
    private static final String Alias = "ALIAS";
    private static final String PostCondition = "POSTCONDITION";
    /**
     * All keywords used in the configuration file
     */
    public static final String[] ALL_KEYWORDS = {Constant, Constants, Constraint, Constraints, ActionConstraint,
            ActionConstraints, Invariant, Invariants, Init, Next, View, Symmetry, Spec, Prop, Props, Alias,
            PostCondition, CheckDeadlock};
    private static final long serialVersionUID = 1L;
    private final Hashtable<String, Object> configTbl;
    private final Hashtable<String, String> overrides;
    private final Hashtable<String, String> overridesReverseMap;
    private final Hashtable<String, ArrayList<ArrayList<Comparable<?>>>> modConstants;
    private final Hashtable<String, Hashtable<Comparable<?>, Object>> modOverrides;
    private final String configFileName;
    private final FilenameToStream resolver; // resolver for the file
    private List<String> rawConstants;

    /**
     * Creates a new model config handle
     *
     * @param configFileName name of the model configuration file
     * @param resolver       the name to stream resolver or <code>null</code>
     *                       is the standard one should be used
     */
    public ModelConfig(final String configFileName, final FilenameToStream resolver) {
        // SZ Feb 20, 2009: added name resolver support, to be able to run from a toolbox
        // standard resolver
        this.resolver = Objects.requireNonNullElseGet(resolver, SimpleFilenameToStream::new);
        // SZ Mar 12, 2009: reset the model values
        ModelValue.init();

        this.configFileName = configFileName;
        this.configTbl = new Hashtable<>();
        ArrayList<Comparable<?>> temp = new ArrayList<>();
        this.configTbl.put(Constant, temp);
        this.configTbl.put(Constants, temp);
        temp = new ArrayList<>();
        this.configTbl.put(Constraint, temp);
        this.configTbl.put(Constraints, temp);
        temp = new ArrayList<>();
        this.configTbl.put(ActionConstraint, temp);
        this.configTbl.put(ActionConstraints, temp);
        temp = new ArrayList<>();
        this.configTbl.put(Invariant, temp);
        this.configTbl.put(Invariants, temp);
        this.configTbl.put(Init, "");
        this.configTbl.put(Next, "");
        this.configTbl.put(View, "");
        this.configTbl.put(Symmetry, "");
        this.configTbl.put(Spec, "");
        temp = new ArrayList<>();
        this.configTbl.put(Prop, temp);
        this.configTbl.put(Props, temp);
        this.configTbl.put(Alias, "");
        this.configTbl.put(PostCondition, "");
        this.configTbl.put(CheckDeadlock, "undef");

        this.modConstants = new Hashtable<>();
        this.modOverrides = new Hashtable<>();
        this.overrides = new Hashtable<>();
        this.overridesReverseMap = new Hashtable<>();
        this.rawConstants = new ArrayList<>();
    }

    /**
     * Retrieves the next token from the token manager
     */
    private static Token getNextToken(final TLAplusParserTokenManager tmgr) {
        try {
            return tmgr.getNextToken();
        } catch (final TokenMgrError e) {
            final Token tt = new Token();
            tt.kind = TLAplusParserConstants.EOF;
            return tt;
        }
    }

    private static Token getNextToken(final TLAplusParserTokenManager tmgr, final StringBuilder buf) {
        try {
            final Token nextToken = tmgr.getNextToken();
            buf.append(nextToken.image).append(" ");
            return nextToken;
        } catch (final TokenMgrError e) {
            final Token tt = new Token();
            tt.kind = TLAplusParserConstants.EOF;
            return tt;
        }
    }

    /**
     * Parse the configuration file
     */
    public final void parse() {
        final ArrayList<ArrayList<Comparable<?>>> constants = this.getConstants();
        final ArrayList<Comparable<?>> constraints = this.getConstraints();
        final ArrayList<Comparable<?>> actionConstraints = this.getActionConstraints();
        final ArrayList<Comparable<?>> invariants = this.getInvariants();
        final ArrayList<Comparable<?>> props = this.getProperties();

        try {
            // SZ 23.02.2009: separated file resolution from stream retrieval
            InputStream fis = FileUtil.newFIS(resolver.resolve(this.configFileName, false));
            if (fis == null) {
                throw new ConfigFileException(EC.CFG_ERROR_READING_FILE, new String[]{this.configFileName,
                        "File not found."});
            }
            if (this.configFileName.endsWith(TLAConstants.Files.TLA_EXTENSION)) {
                fis = MonolithSpecExtractor.config(fis,
                        // strip ".tla" from this.configFileName.
                        Paths
                                .get(this.configFileName).getFileName()
                                .toString()
                                .replace(TLAConstants.Files.TLA_EXTENSION, ""));
            }
            final SimpleCharStream scs = new SimpleCharStream(fis, 1, 1);
            final TLAplusParserTokenManager tmgr = new TLAplusParserTokenManager(scs, 2);

            final List<StringBuilder> rawConstants = new ArrayList<>();
            Token tt = getNextToken(tmgr);
            while (tt.kind != TLAplusParserConstants.EOF) {
                final String tval = tt.image;
                final int loc = scs.getBeginLine();
                switch (tval) {
                    case Init: {
                        tt = getNextToken(tmgr);
                        if (tt.kind == TLAplusParserConstants.EOF) {
                            throw new ConfigFileException(EC.CFG_MISSING_ID, new String[]{String.valueOf(loc), Init});
                        }
                        final String old = (String) this.configTbl.put(Init, tt.image);
                        if (Objects.requireNonNull(old).length() != 0) {
                            throw new ConfigFileException(EC.CFG_TWICE_KEYWORD, new String[]{String.valueOf(loc), Init});
                        }
                        tt = getNextToken(tmgr);
                        break;
                    }
                    case Next: {
                        tt = getNextToken(tmgr);
                        if (tt.kind == TLAplusParserConstants.EOF) {
                            throw new ConfigFileException(EC.CFG_MISSING_ID, new String[]{String.valueOf(loc), Next});
                        }
                        final String old = (String) this.configTbl.put(Next, tt.image);
                        if (Objects.requireNonNull(old).length() != 0) {
                            throw new ConfigFileException(EC.CFG_TWICE_KEYWORD, new String[]{String.valueOf(loc), Next});
                        }
                        tt = getNextToken(tmgr);
                        break;
                    }
                    case Spec: {
                        tt = getNextToken(tmgr);
                        if (tt.kind == TLAplusParserConstants.EOF) {
                            throw new ConfigFileException(EC.CFG_MISSING_ID, new String[]{String.valueOf(loc), Spec});
                        }
                        final String old = (String) this.configTbl.put(Spec, tt.image);
                        if (Objects.requireNonNull(old).length() != 0) {
                            throw new ConfigFileException(EC.CFG_TWICE_KEYWORD, new String[]{String.valueOf(loc), Spec});
                        }
                        tt = getNextToken(tmgr);
                        break;
                    }
                    case View: {
                        tt = getNextToken(tmgr);
                        if (tt.kind == TLAplusParserConstants.EOF) {
                            throw new ConfigFileException(EC.CFG_MISSING_ID, new String[]{String.valueOf(loc), View});
                        }
                        final String old = (String) this.configTbl.put(View, tt.image);
                        if (Objects.requireNonNull(old).length() != 0) {
                            throw new ConfigFileException(EC.CFG_TWICE_KEYWORD, new String[]{String.valueOf(loc), View});
                        }
                        tt = getNextToken(tmgr);
                        break;
                    }
                    case Symmetry: {
                        tt = getNextToken(tmgr);
                        if (tt.kind == TLAplusParserConstants.EOF) {
                            throw new ConfigFileException(EC.CFG_MISSING_ID, new String[]{String.valueOf(loc), Symmetry});
                        }
                        final String old = (String) this.configTbl.put(Symmetry, tt.image);
                        if (Objects.requireNonNull(old).length() != 0) {
                            throw new ConfigFileException(EC.CFG_TWICE_KEYWORD, new String[]{String.valueOf(loc),
                                    Symmetry});
                        }
                        tt = getNextToken(tmgr);
                        break;
                    }
                    case Alias: {
                        tt = getNextToken(tmgr);
                        if (tt.kind == TLAplusParserConstants.EOF) {
                            throw new ConfigFileException(EC.CFG_MISSING_ID, new String[]{String.valueOf(loc), Alias});
                        }
                        final String old = (String) this.configTbl.put(Alias, tt.image);
                        if (Objects.requireNonNull(old).length() != 0) {
                            throw new ConfigFileException(EC.CFG_TWICE_KEYWORD, new String[]{String.valueOf(loc), Alias});
                        }
                        tt = getNextToken(tmgr);
                        break;
                    }
                    case PostCondition: {
                        tt = getNextToken(tmgr);
                        if (tt.kind == TLAplusParserConstants.EOF) {
                            throw new ConfigFileException(EC.CFG_MISSING_ID, new String[]{String.valueOf(loc),
                                    PostCondition});
                        }
                        final String old = (String) this.configTbl.put(PostCondition, tt.image);
                        if (Objects.requireNonNull(old).length() != 0) {
                            throw new ConfigFileException(EC.CFG_TWICE_KEYWORD, new String[]{String.valueOf(loc),
                                    PostCondition});
                        }
                        tt = getNextToken(tmgr);
                        break;
                    }
                    case Constant:
                    case Constants:
                        final StringBuilder buf = new StringBuilder(tval);
                        rawConstants.add(buf);
                        while ((tt = getNextToken(tmgr)).kind != TLAplusParserConstants.EOF) {
                            /* Exit this while loop if the next token is something like "CONSTANT"
                             * that starts a new section of the configuration file.
                             */
                            if (this.configTbl.get(tt.image) != null)
                                break;

                            buf.append("\n").append(tt.image).append(" ");
                            /* Token tt should be the first token in an expression of the form
                             * id <- ...  or id = ... .  In the current implementation, id is the
                             * token tt.  The following code was modified on 30 July 2009
                             * to allow id to be something like frob!bar!glitch, fixing Bug44.
                             */
                            final StringBuilder lhs = new StringBuilder(tt.image);
                            tt = getNextToken(tmgr, buf);
                            while (tt.image.equals("!")) {
                                tt = getNextToken(tmgr, buf);
                                lhs.append("!").append(tt.image);
                                tt = getNextToken(tmgr, buf);
                            }
                            final ArrayList<Comparable<?>> line = new ArrayList<>();
                            line.add(lhs.toString());
                            // Following code replaced on 30 July 2009.
                            if (tt.image.equals("<-")) {
                                tt = getNextToken(tmgr, buf);
                                if (tt.image.equals("[")) {
                                    // This is a module override:
                                    tt = getNextToken(tmgr, buf);
                                    if (tt.kind == TLAplusParserConstants.EOF) {
                                        throw new ConfigFileException(EC.CFG_EXPECT_ID, new String[]{
                                                String.valueOf(scs.getBeginLine()), "<-["});
                                    }
                                    final String modName = tt.image;
                                    tt = getNextToken(tmgr, buf);
                                    if (!tt.image.equals("]")) {
                                        throw new ConfigFileException(EC.CFG_EXPECTED_SYMBOL, new String[]{
                                                String.valueOf(scs.getBeginLine()), "]"});
                                    }
                                    tt = getNextToken(tmgr, buf);
                                    if (tt.kind == TLAplusParserConstants.EOF) {
                                        throw new ConfigFileException(EC.CFG_EXPECT_ID, new String[]{
                                                String.valueOf(scs.getBeginLine()), "<-[mod]"});
                                    }
                                    final Hashtable<Comparable<?>, Object> defs = this.modOverrides.computeIfAbsent(modName, k -> new Hashtable<>());
                                    defs.put(line.get(0), tt.image);
                                } else {
                                    // This is a main module override:
                                    if (tt.kind == TLAplusParserConstants.EOF) {
                                        throw new ConfigFileException(EC.CFG_EXPECT_ID, new String[]{
                                                String.valueOf(scs.getBeginLine()), "<-"});
                                    }
                                    final String string = (String) line.get(0);
                                    this.overrides.put(string, tt.image);
                                    this.overridesReverseMap.put(tt.image, string);
                                }
                            } else {
                                if (tt.image.equals("(")) {
                                    do {
                                        tt = getNextToken(tmgr, buf);
                                        final IValue arg = this.parseValue(tt, scs, tmgr, buf);
                                        line.add(arg);
                                        tt = getNextToken(tmgr, buf);
                                    } while (tt.image.equals(","));
                                    if (!tt.image.equals(")")) {
                                        throw new ConfigFileException(EC.CFG_GENERAL, new String[]{String.valueOf(loc)});
                                    }
                                    tt = getNextToken(tmgr, buf);
                                }
                                if (!tt.image.equals("=")) {
                                    throw new ConfigFileException(EC.CFG_EXPECTED_SYMBOL, new String[]{
                                            String.valueOf(scs.getBeginLine()), "= or <-"});
                                }
                                tt = getNextToken(tmgr, buf);
                                if (tt.image.equals("[")) {
                                    // This is a module specific override:
                                    tt = getNextToken(tmgr, buf);
                                    if (tt.kind == TLAplusParserConstants.EOF) {
                                        throw new ConfigFileException(EC.CFG_EXPECT_ID, new String[]{
                                                String.valueOf(scs.getBeginLine()), "=["});
                                    }
                                    final String modName = tt.image;
                                    tt = getNextToken(tmgr, buf);
                                    if (!tt.image.equals("]")) {
                                        throw new ConfigFileException(EC.CFG_EXPECTED_SYMBOL, new String[]{
                                                String.valueOf(scs.getBeginLine()), "]"});
                                    }
                                    tt = getNextToken(tmgr, buf);
                                    line.add(this.parseValue(tt, scs, tmgr, buf));
                                    ArrayList<ArrayList<Comparable<?>>> mConsts = this.modConstants.computeIfAbsent(modName, k -> new ArrayList<>());
                                    mConsts.add(line);
                                } else {
                                    // This is a main module override:
                                    line.add(this.parseValue(tt, scs, tmgr, buf));
                                    constants.add(line);
                                }
                            }
                        }
                        break;
                    case Invariant:
                    case Invariants:
                        while ((tt = getNextToken(tmgr)).kind != TLAplusParserConstants.EOF) {
                            if (this.configTbl.get(tt.image) != null)
                                break;
                            invariants.add(tt.image);
                        }
                        break;
                    case Prop:
                    case Props:
                        while ((tt = getNextToken(tmgr)).kind != TLAplusParserConstants.EOF) {
                            if (this.configTbl.get(tt.image) != null)
                                break;
                            props.add(tt.image);
                        }
                        break;
                    case Constraint:
                    case Constraints:
                        while ((tt = getNextToken(tmgr)).kind != TLAplusParserConstants.EOF) {
                            if (this.configTbl.get(tt.image) != null)
                                break;
                            constraints.add(tt.image);
                        }
                        break;
                    case ActionConstraint:
                    case ActionConstraints:
                        while ((tt = getNextToken(tmgr)).kind != TLAplusParserConstants.EOF) {
                            if (this.configTbl.get(tt.image) != null)
                                break;
                            actionConstraints.add(tt.image);
                        }
                        break;
                    case CheckDeadlock:
                        tt = getNextToken(tmgr);
                        if (tt.kind == TLAplusParserConstants.EOF) {
                            throw new ConfigFileException(EC.CFG_MISSING_ID, new String[]{String.valueOf(loc), CheckDeadlock});
                        }
                        final Object previous;
                        if (tt.image.equals("TRUE")) {
                            previous = this.configTbl.put(CheckDeadlock, true);
                        } else if (tt.image.equals("FALSE")) {
                            previous = this.configTbl.put(CheckDeadlock, false);
                        } else {
                            throw new ConfigFileException(EC.CFG_EXPECTED_SYMBOL, new String[]{
                                    String.valueOf(scs.getBeginLine()), "TRUE or FALSE"});
                        }
                        if (previous != "undef") {
                            throw new ConfigFileException(EC.CFG_TWICE_KEYWORD, new String[]{String.valueOf(loc), CheckDeadlock});
                        }
                        tt = getNextToken(tmgr);
                        break;
                    default:
                        throw new ConfigFileException(EC.CFG_EXPECTED_SYMBOL, new String[]{
                                String.valueOf(scs.getBeginLine()), "a keyword"});
                }
            }
            this.rawConstants = rawConstants.stream().map(StringBuilder::toString).collect(Collectors.toList());
        } catch (final IOException e) {
            throw new ConfigFileException(EC.CFG_ERROR_READING_FILE,
                    new String[]{this.configFileName, e.getMessage()}, e);
        }
    }

    /**
     * Parses a value (number, string, boolean and set)
     */
    private Value parseValue(Token tt, final SimpleCharStream scs, final TLAplusParserTokenManager tmgr, final StringBuilder buf) {
        if (tt.kind == TLAplusParserConstants.NUMBER_LITERAL) {
            final int val = Integer.parseInt(tt.image);
            return IntValue.gen(val);
        } else if (tt.kind == TLAplusParserConstants.STRING_LITERAL) {
            final String tval = tt.image;
            return new StringValue(tval.substring(1, tval.length() - 1));
        } else if (tt.image.equals("TRUE")) {
            return BoolValue.ValTrue;
        } else if (tt.image.equals("FALSE")) {
            return BoolValue.ValFalse;
        } else if (tt.image.equals("{")) {
            final ValueVec elems = new ValueVec();
            tt = getNextToken(tmgr, buf);
            if (!tt.image.equals("}")) {
                while (true) {
                    final Value elem = this.parseValue(tt, scs, tmgr, buf);
                    elems.add(elem);
                    tt = getNextToken(tmgr, buf);
                    if (!tt.image.equals(","))
                        break;
                    tt = getNextToken(tmgr, buf);
                }
            }
            if (!tt.image.equals("}")) {
                throw new ConfigFileException(EC.CFG_EXPECTED_SYMBOL, new String[]{
                        String.valueOf(scs.getBeginLine()), "}"});
            }
            return new SetEnumValue(elems, false);
        } else if (tt.kind != TLAplusParserConstants.EOF) {
            return ModelValue.make(tt.image);
        }
        throw new ConfigFileException(EC.CFG_EXPECTED_SYMBOL, new String[]{String.valueOf(scs.getBeginLine()),
                "a value"});
    }

    /**
     * @return All CONSTANT or CONSTANTS statements as they appear in the config file.
     */
    public final synchronized  List<String> getRawConstants() {
        return this.rawConstants;
    }

    /**
     * Like `getRawConstants`, but it returns the constants as a list where each
     * element of the list is also a list of one or two elements (instead of raw strings).
     * If one element, it has the form `["field->value"]`, which is a replacement, otherwise
     * it has the form `["field", "value"]`, which is an assignment (which are the lines in a
     * config file for the CONSTANT(s) section where you have `field = value`).
     */
    public final synchronized  List<List<String>> getConstantsAsList() {
        /**
         * `getRawConstants` returns a list of strings where each element has the
         * following form (fields and values are example letters):
         *
         * CONSTANT
         * a = b
         * c = d
         * e <- f
         * CONSTANTS
         * g <- h
         * i = j
         *
         * We will use the example above to document the stream below (we are only showing
         * one element, but ).
         */
        return this.getRawConstants()
                // Convert the list a stream so we can transform the input raw strings.
                .stream()
                /**
                 * Split by lines so each element will have the following form ([] represents a list):
                 *
                 * ["CONSTANT",
                 *  "a = b",
                 *  "c = d",
                 *  "e <- f",
                 *  "CONSTANTS",
                 *  "g <- h",
                 *  "i = j"]
                 */
                .map(s -> s.split("\n"))
                /**
                 * Flatten both lists, so `[["CONSTANT", "a = b"], ["g <- h"]]` becomes
                 * `["CONSTANT", "a = b", "g <- h"]`.
                 */
                .flatMap(Stream::of)
                /**
                 * Then we trim just to make sure we don't have whitespaces surrounding any element.
                 */
                .map(String::trim)
                /**
                 * Ignore `CONSTANT` or `CONSTANTS`:
                 *
                 * ["a = b",
                 *  "c = d",
                 *  "e <- f",
                 *  "g <- h",
                 *  "i = j"]
                 */
                .filter(s -> !(s.equals(Constant) || s.equals(Constants)))
                /**
                 * We split only `=` as `<-` means a replacement and we don't need to analyze
                 * its field separately.
                 *
                 * [["a", "b"],
                 *  ["c", "d"],
                 *  ["e <- f"],
                 *  ["g <- h"],
                 *  ["i", "j"]]
                 */
                .map(s -> Arrays.asList(s.split(" = ")))
                /**
                 * Convert the stream to a java List, we are finished processing it.
                 */
                .collect(Collectors.toList());
    }

    @SuppressWarnings("unchecked")
    public final synchronized  ArrayList<ArrayList<Comparable<?>>> getConstants() {
        return (ArrayList<ArrayList<Comparable<?>>>) this.configTbl.get(Constant);
    }

    public final synchronized  Hashtable<String, ArrayList<ArrayList<Comparable<?>>>> getModConstants() {
        return this.modConstants;
    }

    public final synchronized  Hashtable<String, String> getOverrides() {
        return this.overrides;
    }

    public final synchronized  String getOverridenSpecNameForConfigName(final String configName) {
        return this.overridesReverseMap.get(configName);
    }

    public final synchronized  Hashtable<String, Hashtable<Comparable<?>, Object>> getModOverrides() {
        return this.modOverrides;
    }

    @SuppressWarnings("unchecked")
    public final synchronized  ArrayList<Comparable<?>> getConstraints() {
        return (ArrayList<Comparable<?>>) this.configTbl.get(Constraint);
    }

    @SuppressWarnings("unchecked")
    public final synchronized  ArrayList<Comparable<?>> getActionConstraints() {
        return (ArrayList<Comparable<?>>) this.configTbl.get(ActionConstraint);
    }

    public final synchronized  String getInit() {
        return (String) this.configTbl.get(Init);
    }

    public final synchronized  String getNext() {
        return (String) this.configTbl.get(Next);
    }

    public final synchronized  String getView() {
        return (String) this.configTbl.get(View);
    }

    public final synchronized  boolean configDefinesSpecification() {
        final String spec = getSpec();

        return ((spec != null) && (spec.trim().length() > 0));
    }

    public final synchronized  String getSymmetry() {
        return (String) this.configTbl.get(Symmetry);
    }

    @SuppressWarnings("unchecked")
    public final synchronized  ArrayList<Comparable<?>> getInvariants() {
        return (ArrayList<Comparable<?>>) this.configTbl.get(Invariant);
    }

    public final synchronized  String getSpec() {
        return (String) this.configTbl.get(Spec);
    }

    @SuppressWarnings("unchecked")
    public final synchronized ArrayList<Comparable<?>> getProperties() {
        return (ArrayList<Comparable<?>>) this.configTbl.get(Prop);
    }

    public final synchronized String getAlias() {
        return (String) this.configTbl.get(Alias);
    }

    public final synchronized String getPostCondition() {
        return (String) this.configTbl.get(PostCondition);
    }

    public final synchronized boolean getCheckDeadlock() {
        final Object object = this.configTbl.get(CheckDeadlock);
        if (object instanceof Boolean b) {
            return b;
        }
        return true;
    }
}
