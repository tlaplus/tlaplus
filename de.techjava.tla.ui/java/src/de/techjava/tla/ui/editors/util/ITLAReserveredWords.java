package de.techjava.tla.ui.editors.util;

import java.util.Arrays;
import java.util.HashSet;

/**
 * TLA+ Reserved words
 * TODO complete the word list
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: ITLAReserveredWords.java,v 1.1 2005/08/22 15:43:33 szambrovski Exp $
 */
public interface ITLAReserveredWords 
{
    public final static String ASSUME 		= "ASSUME";
    public final static String ASSUMPTION 	= "ASSUMPTION";
    public final static String AXIOM 		= "AXIOM";
    public final static String CASE 		= "CASE";
    public final static String CHOOSE 		= "CHOOSE";
    public final static String CONSTANT		= "CONSTANT";
    public final static String CONSTANTS	= "CONSTANTS";
    public final static String DOMAIN		= "DOMAIN";
    public final static String ELSE 		= "ELSE";
    public final static String ENABLED		= "ENABLED";
    public final static String EXCEPT		= "EXCEPT";
    public final static String EXTENDS 		= "EXTENDS";
    public final static String IF 			= "IF";
    public final static String IN 			= "IN";
    public final static String INSTANCE		= "INSTANCE";
    public final static String LET 			= "LET";
    public final static String LOCAL 		= "LOCAL";
    public final static String MODULE 		= "MODULE";
    public final static String OTHER 		= "OTHER";
    public final static String SF_ 			= "SF_";
    public final static String SUBSET 		= "SUBSET";
    public final static String THEN 		= "THEN";
    public final static String THEOREM 		= "THEOREM";
    public final static String UNCHANGED 	= "UNCHANGED";
    public final static String UNION 		= "UNION";
    public final static String VARIABLE 	= "VARIABLE";
    public final static String VARIABLES 	= "VARIABLES";
    public final static String WF_ 			= "WF_";
    public final static String WITH 		= "WITH";
    
    public final static String[] ALL_WORDS_ARRAY = new String[]
    {
            ASSUME,
            ASSUMPTION,
            AXIOM,
            CASE,
            CHOOSE,
            CONSTANT,
            CONSTANTS,
            DOMAIN,
            ELSE,
            ENABLED,
            EXCEPT,
            EXTENDS,
            IF,
            IN,
            INSTANCE,
            LET,
            LOCAL,
            MODULE,
            OTHER,
            SF_,
            SUBSET,
            THEN,
            THEOREM,
            UNCHANGED,
            UNION,
            VARIABLE,
            VARIABLES,
            WF_,
            WITH
    };
    
    public final static HashSet ALL_WORDS_SET = new HashSet(Arrays.asList(ALL_WORDS_ARRAY));
}

/*
 * $Log: ITLAReserveredWords.java,v $
 * Revision 1.1  2005/08/22 15:43:33  szambrovski
 * sf cvs init
 *
 * Revision 1.2  2004/10/13 14:45:00  sza
 * operators added
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.1  2004/10/12 09:55:11  sza
 * additions
 *
 * Revision 1.1  2004/10/06 01:02:29  sza
 * initial commit
 *
 * Revision 1.1  2004/10/06 00:59:04  sza
 * initial commit
 *
 *
 */