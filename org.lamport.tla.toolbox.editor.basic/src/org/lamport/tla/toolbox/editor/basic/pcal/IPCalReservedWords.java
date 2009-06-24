package org.lamport.tla.toolbox.editor.basic.pcal;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface IPCalReservedWords
{
    public final static String ALGORITHM = "--algorithm";

    public final static String ASSERT = "assert";
    // public final static String AWAIT = "";
    public final static String BEGIN = "begin";
    public final static String CALL = "call";
    // public final static String DEFINE = "define";
    public final static String DO = "do";
    public final static String EITHER = "either";
    public final static String ELSE = "else";
    public final static String ELSEIF = "elseif";
    public final static String END = "end";
    public final static String GOTO = "goto";
    public final static String IF = "if";
    public final static String MACRO = "macro";
    public final static String OR = "or";
    public final static String PRINT = "print";
    public final static String PROCEDURE = "procedure";
    public final static String PROCESS = "process";
    public final static String RETURN = "return";
    public final static String SKIP = "skip";
    public final static String THEN = "then";
    public final static String VARIABLE = "variable";
    public final static String VARIABLES = "variables";
    public final static String WHILE = "while";
    public final static String WITH = "with";
    // public final static String WHEN = "";

    public final static String[] ALL_WORDS_ARRAY = new String[] { ASSERT, BEGIN, CALL, DO, EITHER, ELSE, ELSEIF, END,
            GOTO, IF, MACRO, OR, PRINT, PROCEDURE, PROCESS, RETURN, SKIP, THEN, VARIABLE, VARIABLES, WHILE, WITH };

}
