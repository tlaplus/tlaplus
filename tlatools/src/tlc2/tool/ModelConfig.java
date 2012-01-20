// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:29:56 PST by lamport
//      modified on Thu Aug 23 17:46:39 PDT 2001 by yuanyu

package tlc2.tool;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.Serializable;
import java.util.Hashtable;

import tla2sany.parser.SimpleCharStream;
import tla2sany.parser.TLAplusParserConstants;
import tla2sany.parser.TLAplusParserTokenManager;
import tla2sany.parser.Token;
import tla2sany.parser.TokenMgrError;
import tlc2.output.EC;
import tlc2.util.Vect;
import tlc2.value.IntValue;
import tlc2.value.ModelValue;
import tlc2.value.SetEnumValue;
import tlc2.value.StringValue;
import tlc2.value.Value;
import tlc2.value.ValueConstants;
import tlc2.value.ValueVec;
import util.FileUtil;
import util.FilenameToStream;
import util.SimpleFilenameToStream;

/** 
 * Stores information from user's model configuration file.
 * @author Yuan Yu, Leslie Lamport
 * @version $Id$
 */
public class ModelConfig implements ValueConstants, Serializable
{
    // keywords of the configuration file
    private static final String Constant = "CONSTANT";
    private static final String Constants = "CONSTANTS";
    private static final String Constraint = "CONSTRAINT";
    private static final String Constraints = "CONSTRAINTS";
    private static final String ActionConstraint = "ACTION_CONSTRAINT";
    private static final String ActionConstraints = "ACTION_CONSTRAINTS";
    private static final String Invariant = "INVARIANT";
    private static final String Invariants = "INVARIANTS";
    private static final String Init = "INIT";
    private static final String Next = "NEXT";
    private static final String View = "VIEW";
    private static final String Symmetry = "SYMMETRY";
    private static final String Spec = "SPECIFICATION";
    private static final String Prop = "PROPERTY";
    private static final String Props = "PROPERTIES";
    private static final String Type = "TYPE";
    private static final String TypeConstraint = "TYPE_CONSTRAINT";

    /**
     * All keywords used in the configuration file
     */
    public final static String[] ALL_KEYWORDS = { Constant, Constants, Constraint, Constraints, ActionConstraint,
            ActionConstraints, Invariant, Invariants, Init, Next, View, Symmetry, Spec, Prop, Props, Type,
            TypeConstraint };

    private Hashtable configTbl;
    private Hashtable overrides;
    private Hashtable modConstants;
    private Hashtable modOverrides;
    private String configFileName;
    private FilenameToStream resolver; // resolver for the file

    /**
     * Creates a new model config handle
     * @param configFileName name of the model configuration file
     * @param resolver the name to stream resolver or <code>null</code> 
     * is the standard one should be used
     */
    public ModelConfig(String configFileName, FilenameToStream resolver)
    {
        // SZ Feb 20, 2009: added name resolver support, to be able to run from a toolbox
        if (resolver != null)
        {
            this.resolver = resolver;
        } else
        {
            // standard resolver
            this.resolver = new SimpleFilenameToStream();
        }
        // SZ Mar 12, 2009: reset the model values
        ModelValue.init();

        this.configFileName = configFileName;
        this.configTbl = new Hashtable();
        Vect temp = new Vect();
        this.configTbl.put(Constant, temp);
        this.configTbl.put(Constants, temp);
        temp = new Vect();
        this.configTbl.put(Constraint, temp);
        this.configTbl.put(Constraints, temp);
        temp = new Vect();
        this.configTbl.put(ActionConstraint, temp);
        this.configTbl.put(ActionConstraints, temp);
        temp = new Vect();
        this.configTbl.put(Invariant, temp);
        this.configTbl.put(Invariants, temp);
        this.configTbl.put(Init, "");
        this.configTbl.put(Next, "");
        this.configTbl.put(View, "");
        this.configTbl.put(Symmetry, "");
        this.configTbl.put(Spec, "");
        temp = new Vect();
        this.configTbl.put(Prop, temp);
        this.configTbl.put(Props, temp);
        this.configTbl.put(Type, "");
        this.configTbl.put(TypeConstraint, "");

        this.modConstants = new Hashtable();
        this.modOverrides = new Hashtable();
        this.overrides = new Hashtable();
    }

    /**
     * Parse the configuration file
     */
    public final void parse()
    {
        Vect constants = (Vect) this.configTbl.get(Constant);
        Vect constraints = (Vect) this.configTbl.get(Constraint);
        Vect actionConstraints = (Vect) this.configTbl.get(ActionConstraint);
        Vect invariants = (Vect) this.configTbl.get(Invariant);
        Vect props = (Vect) this.configTbl.get(Prop);
        try
        {
            // SZ 23.02.2009: separated file resolution from stream retrieval
            FileInputStream fis = FileUtil.newFIS(resolver.resolve(this.configFileName, false));
            if (fis == null)
            {
                throw new ConfigFileException(EC.CFG_ERROR_READING_FILE, new String[] { this.configFileName,
                        "File not found." });
            }
            SimpleCharStream scs = new SimpleCharStream(fis, 1, 1);
            TLAplusParserTokenManager tmgr = new TLAplusParserTokenManager(scs, 2);

            Token tt = getNextToken(tmgr);
            while (tt.kind != TLAplusParserConstants.EOF)
            {
                String tval = tt.image;
                int loc = scs.getBeginLine();
                if (tval.equals(Init))
                {
                    tt = getNextToken(tmgr);
                    if (tt.kind == TLAplusParserConstants.EOF)
                    {
                        throw new ConfigFileException(EC.CFG_MISSING_ID, new String[] { String.valueOf(loc), Init });
                    }
                    String old = (String) this.configTbl.put(Init, tt.image);
                    if (old.length() != 0)
                    {
                        throw new ConfigFileException(EC.CFG_TWICE_KEYWORD, new String[] { String.valueOf(loc), Spec });
                    }
                    tt = getNextToken(tmgr);
                } else if (tval.equals(Next))
                {
                    tt = getNextToken(tmgr);
                    if (tt.kind == TLAplusParserConstants.EOF)
                    {
                        throw new ConfigFileException(EC.CFG_MISSING_ID, new String[] { String.valueOf(loc), Next });
                    }
                    String old = (String) this.configTbl.put(Next, tt.image);
                    if (old.length() != 0)
                    {
                        throw new ConfigFileException(EC.CFG_TWICE_KEYWORD, new String[] { String.valueOf(loc), Next });
                    }
                    tt = getNextToken(tmgr);
                } else if (tval.equals(Spec))
                {
                    tt = getNextToken(tmgr);
                    if (tt.kind == TLAplusParserConstants.EOF)
                    {
                        throw new ConfigFileException(EC.CFG_MISSING_ID, new String[] { String.valueOf(loc), Spec });
                    }
                    String old = (String) this.configTbl.put(Spec, tt.image);
                    if (old.length() != 0)
                    {
                        throw new ConfigFileException(EC.CFG_TWICE_KEYWORD, new String[] { String.valueOf(loc), Spec });
                    }
                    tt = getNextToken(tmgr);
                } else if (tval.equals(View))
                {
                    tt = getNextToken(tmgr);
                    if (tt.kind == TLAplusParserConstants.EOF)
                    {
                        throw new ConfigFileException(EC.CFG_MISSING_ID, new String[] { String.valueOf(loc), View });
                    }
                    String old = (String) this.configTbl.put(View, tt.image);
                    if (old.length() != 0)
                    {
                        throw new ConfigFileException(EC.CFG_TWICE_KEYWORD, new String[] { String.valueOf(loc), View });
                    }
                    tt = getNextToken(tmgr);
                } else if (tval.equals(Symmetry))
                {
                    tt = getNextToken(tmgr);
                    if (tt.kind == TLAplusParserConstants.EOF)
                    {
                        throw new ConfigFileException(EC.CFG_MISSING_ID, new String[] { String.valueOf(loc), Symmetry });
                    }
                    String old = (String) this.configTbl.put(Symmetry, tt.image);
                    if (old.length() != 0)
                    {
                        throw new ConfigFileException(EC.CFG_TWICE_KEYWORD, new String[] { String.valueOf(loc),
                                Symmetry });
                    }
                    tt = getNextToken(tmgr);
                } else if (tval.equals(Type))
                {
                    tt = getNextToken(tmgr);
                    if (tt.kind == TLAplusParserConstants.EOF)
                    {
                        throw new ConfigFileException(EC.CFG_MISSING_ID, new String[] { String.valueOf(loc), Type });
                    }
                    String old = (String) this.configTbl.put(Type, tt.image);
                    if (old.length() != 0)
                    {
                        throw new ConfigFileException(EC.CFG_TWICE_KEYWORD, new String[] { String.valueOf(loc), Type });
                    }
                    tt = getNextToken(tmgr);
                } else if (tval.equals(TypeConstraint))
                {
                    tt = getNextToken(tmgr);
                    if (tt.kind == TLAplusParserConstants.EOF)
                    {
                        throw new ConfigFileException(EC.CFG_MISSING_ID, new String[] { String.valueOf(loc),
                                TypeConstraint });
                    }
                    String old = (String) this.configTbl.put(TypeConstraint, tt.image);
                    if (old.length() != 0)
                    {
                        throw new ConfigFileException(EC.CFG_TWICE_KEYWORD, new String[] { String.valueOf(loc),
                                TypeConstraint });
                    }
                    tt = getNextToken(tmgr);
                } else if (tval.equals(Constant) || tval.equals(Constants))
                {
                    while ((tt = getNextToken(tmgr)).kind != TLAplusParserConstants.EOF)
                    {
                        /* Exit this while loop if the next token is something like "CONSTANT"
                         * that starts a new section of the configuration file.
                         */
                        if (this.configTbl.get(tt.image) != null)
                            break;
                        /* Token tt should be the first token in an expression of the form
                         * id <- ...  or id = ... .  In the current implementation, id is the
                         * token tt.  The following code was modified on 30 July 2009
                         * to allow id to be something like frob!bar!glitch, fixing Bug44.
                         */
                        String lhs = tt.image;
                        tt = getNextToken(tmgr);
                        while (tt.image.equals("!"))
                        {
                            tt = getNextToken(tmgr);
                            lhs = lhs + "!" + tt.image;
                            tt = getNextToken(tmgr);
                        }
                        Vect line = new Vect();
                        line.addElement(lhs);
                        // Following code replaced on 30 July 2009.
                        // line.addElement(tt.image);
                        // tt = getNextToken(tmgr);
                        if (tt.image.equals("<-"))
                        {
                            tt = getNextToken(tmgr);
                            if (tt.image.equals("["))
                            {
                                // This is a module override:
                                tt = getNextToken(tmgr);
                                if (tt.kind == TLAplusParserConstants.EOF)
                                {
                                    throw new ConfigFileException(EC.CFG_EXPECT_ID, new String[] {
                                            String.valueOf(scs.getBeginLine()), "<-[" });
                                }
                                String modName = tt.image;
                                tt = getNextToken(tmgr);
                                if (!tt.image.equals("]"))
                                {
                                    throw new ConfigFileException(EC.CFG_EXPECTED_SYMBOL, new String[] {
                                            String.valueOf(scs.getBeginLine()), "]" });
                                }
                                tt = getNextToken(tmgr);
                                if (tt.kind == TLAplusParserConstants.EOF)
                                {
                                    throw new ConfigFileException(EC.CFG_EXPECT_ID, new String[] {
                                            String.valueOf(scs.getBeginLine()), "<-[mod]" });
                                }
                                Hashtable defs = (Hashtable) this.modOverrides.get(modName);
                                if (defs == null)
                                {
                                    defs = new Hashtable();
                                    this.modOverrides.put(modName, defs);
                                }
                                defs.put(line.elementAt(0), tt.image);
                            } else
                            {
                                // This is a main module override:
                                if (tt.kind == TLAplusParserConstants.EOF)
                                {
                                    throw new ConfigFileException(EC.CFG_EXPECT_ID, new String[] {
                                            String.valueOf(scs.getBeginLine()), "<-" });
                                }
                                this.overrides.put(line.elementAt(0), tt.image);
                            }
                        } else
                        {
                            if (tt.image.equals("("))
                            {
                                while (true)
                                {
                                    tt = getNextToken(tmgr);
                                    Value arg = this.parseValue(tt, scs, tmgr);
                                    line.addElement(arg);
                                    tt = getNextToken(tmgr);
                                    if (!tt.image.equals(","))
                                        break;
                                }
                                if (!tt.image.equals(")"))
                                {
                                    throw new ConfigFileException(EC.CFG_GENERAL, new String[] { String.valueOf(loc) });
                                }
                                tt = getNextToken(tmgr);
                            }
                            if (!tt.image.equals("="))
                            {
                                throw new ConfigFileException(EC.CFG_EXPECTED_SYMBOL, new String[] {
                                        String.valueOf(scs.getBeginLine()), "= or <-" });
                            }
                            tt = getNextToken(tmgr);
                            if (tt.image.equals("["))
                            {
                                // This is a module specific override:
                                tt = getNextToken(tmgr);
                                if (tt.kind == TLAplusParserConstants.EOF)
                                {
                                    throw new ConfigFileException(EC.CFG_EXPECT_ID, new String[] {
                                            String.valueOf(scs.getBeginLine()), "=[" });
                                }
                                String modName = tt.image;
                                tt = getNextToken(tmgr);
                                if (!tt.image.equals("]"))
                                {
                                    throw new ConfigFileException(EC.CFG_EXPECTED_SYMBOL, new String[] {
                                            String.valueOf(scs.getBeginLine()), "]" });
                                }
                                tt = getNextToken(tmgr);
                                line.addElement(this.parseValue(tt, scs, tmgr));
                                Vect mConsts = (Vect) this.modConstants.get(modName);
                                if (mConsts == null)
                                {
                                    mConsts = new Vect();
                                    this.modConstants.put(modName, mConsts);
                                }
                                mConsts.addElement(line);
                            } else
                            {
                                // This is a main module override:
                                line.addElement(this.parseValue(tt, scs, tmgr));
                                constants.addElement(line);
                            }
                        }
                    }
                } else if (tval.equals(Invariant) || tval.equals(Invariants))
                {
                    while ((tt = getNextToken(tmgr)).kind != TLAplusParserConstants.EOF)
                    {
                        if (this.configTbl.get(tt.image) != null)
                            break;
                        invariants.addElement(tt.image);
                    }
                } else if (tval.equals(Prop) || tval.equals(Props))
                {
                    while ((tt = getNextToken(tmgr)).kind != TLAplusParserConstants.EOF)
                    {
                        if (this.configTbl.get(tt.image) != null)
                            break;
                        props.addElement(tt.image);
                    }
                } else if (tval.equals(Constraint) || tval.equals(Constraints))
                {
                    while ((tt = getNextToken(tmgr)).kind != TLAplusParserConstants.EOF)
                    {
                        if (this.configTbl.get(tt.image) != null)
                            break;
                        constraints.addElement(tt.image);
                    }
                } else if (tval.equals(ActionConstraint) || tval.equals(ActionConstraints))
                {
                    while ((tt = getNextToken(tmgr)).kind != TLAplusParserConstants.EOF)
                    {
                        if (this.configTbl.get(tt.image) != null)
                            break;
                        actionConstraints.addElement(tt.image);
                    }
                } else
                {
                    throw new ConfigFileException(EC.CFG_EXPECTED_SYMBOL, new String[] {
                            String.valueOf(scs.getBeginLine()), "a keyword" });
                }
            }
        } catch (IOException e)
        {
            throw new ConfigFileException(EC.CFG_ERROR_READING_FILE,
                    new String[] { this.configFileName, e.getMessage() }, e);
        }
    }

    /**
     * Parses a value (number, string, boolean and set)
     */
    private Value parseValue(Token tt, SimpleCharStream scs, TLAplusParserTokenManager tmgr) throws IOException
    {
        if (tt.kind == TLAplusParserConstants.NUMBER_LITERAL)
        {
            int val = Integer.parseInt(tt.image);
            return IntValue.gen(val);
        } else if (tt.kind == TLAplusParserConstants.STRING_LITERAL)
        {
            String tval = tt.image;
            return new StringValue(tval.substring(1, tval.length() - 1));
        } else if (tt.image.equals("TRUE"))
        {
            return ValTrue;
        } else if (tt.image.equals("FALSE"))
        {
            return ValFalse;
        } else if (tt.image.equals("{"))
        {
            ValueVec elems = new ValueVec();
            tt = getNextToken(tmgr);
            if (!tt.image.equals("}"))
            {
                while (true)
                {
                    Value elem = this.parseValue(tt, scs, tmgr);
                    elems.addElement(elem);
                    tt = getNextToken(tmgr);
                    if (!tt.image.equals(","))
                        break;
                    tt = getNextToken(tmgr);
                }
            }
            if (!tt.image.equals("}"))
            {
                throw new ConfigFileException(EC.CFG_EXPECTED_SYMBOL, new String[] {
                        String.valueOf(scs.getBeginLine()), "}" });
            }
            return new SetEnumValue(elems, false);
        } else if (tt.kind != TLAplusParserConstants.EOF)
        {
            return ModelValue.make(tt.image);
        }
        throw new ConfigFileException(EC.CFG_EXPECTED_SYMBOL, new String[] { String.valueOf(scs.getBeginLine()),
                "a value" });
    }

    /**
     * Retrieves the next token from the token manager
     * @param tmgr
     * @return
     */
    public static Token getNextToken(TLAplusParserTokenManager tmgr)
    {
        try
        {
            return tmgr.getNextToken();
        } catch (TokenMgrError e)
        {
            Token tt = new Token();
            tt.kind = TLAplusParserConstants.EOF;
            return tt;
        }
    }

    public synchronized final Vect getConstants()
    {
        return (Vect) this.configTbl.get(Constant);
    }

    public synchronized final Hashtable getModConstants()
    {
        return this.modConstants;
    }

    public synchronized final Hashtable getOverrides()
    {
        return this.overrides;
    }

    public synchronized final Hashtable getModOverrides()
    {
        return this.modOverrides;
    }

    public synchronized final Vect getConstraints()
    {
        return (Vect) this.configTbl.get(Constraint);
    }

    public synchronized final Vect getActionConstraints()
    {
        return (Vect) this.configTbl.get(ActionConstraint);
    }

    public synchronized final String getInit()
    {
        return (String) this.configTbl.get(Init);
    }

    public synchronized final String getNext()
    {
        return (String) this.configTbl.get(Next);
    }

    public synchronized final String getView()
    {
        return (String) this.configTbl.get(View);
    }

    public synchronized final String getSymmetry()
    {
        return (String) this.configTbl.get(Symmetry);
    }

    public synchronized final Vect getInvariants()
    {
        return (Vect) this.configTbl.get(Invariant);
    }

    public synchronized final String getSpec()
    {
        return (String) this.configTbl.get(Spec);
    }

    public synchronized final Vect getProperties()
    {
        return (Vect) this.configTbl.get(Prop);
    }

    public synchronized final String getType()
    {
        return (String) this.configTbl.get(Type);
    }

    public synchronized final String getTypeConstraint()
    {
        return (String) this.configTbl.get(TypeConstraint);
    }

    /**
     * Testing method of the parser
     * @param args
     * @deprecated
     */
    public static void main(String[] args)
    {
        try
        {
            // SZ Feb 20, 2009: move to test package
            // REFACTOR: Name to stream
            FileInputStream fis = new FileInputStream(args[0]);
            SimpleCharStream scs = new SimpleCharStream(fis, 1, 1);
            TLAplusParserTokenManager tmgr = new TLAplusParserTokenManager(scs, 2);

            Token t = getNextToken(tmgr);
            while (t.kind != 0)
            {
                System.err.println(t);
                t = getNextToken(tmgr);
            }
        } catch (Exception e)
        {
            System.err.println(e.getMessage());
        }
    }

}
