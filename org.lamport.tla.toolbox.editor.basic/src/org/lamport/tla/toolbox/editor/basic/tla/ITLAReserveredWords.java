package org.lamport.tla.toolbox.editor.basic.tla;

import java.util.Arrays;
import java.util.HashSet;

/**
 * TLA+ Reserved words

 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: ITLAReserveredWords.java,v 1.1 2005/08/22 15:43:33 szambrovski Exp $
 */
public interface ITLAReserveredWords 
{
    public final static String ACTION       = "ACTION";
    public final static String ASSUME 		= "ASSUME";
    public final static String ASSUMPTION 	= "ASSUMPTION";
    public final static String AXIOM 		= "AXIOM";
    public final static String BY           = "BY";    
    public final static String CASE 		= "CASE";
    public final static String CHOOSE 		= "CHOOSE";
    public final static String CONSTANT		= "CONSTANT";
    public final static String CONSTANTS	= "CONSTANTS";
    public final static String DEF          = "DEF";
    public final static String DEFINE       = "DEFINE";
    public final static String DEFS         = "DEFS";
    public final static String DOMAIN		= "DOMAIN";
    public final static String ELSE 		= "ELSE";
    public final static String ENABLED		= "ENABLED";
    public final static String EXCEPT		= "EXCEPT";
    public final static String EXTENDS 		= "EXTENDS";
    public final static String HAVE         = "HAVE";
    public final static String HIDE         = "HIDE";
    public final static String IF 			= "IF";
    public final static String IN 			= "IN";
    public final static String INSTANCE		= "INSTANCE";
    public final static String LET 			= "LET";
    public final static String LAMBDA       = "LAMBDA";
    public final static String LEMMA        = "LEMMA";
    public final static String LOCAL 		= "LOCAL";
    public final static String MODULE 		= "MODULE";
    public final static String NEW          = "NEW";
    public final static String OBVIOUS      = "OBVIOUS";
    public final static String OMITTED      = "OMITTED";
    public final static String OTHER 		= "OTHER";
    public final static String PICK         = "PICK";
    public final static String PROOF        = "PROOF";
    public final static String PROPOSITION  = "PROPOSITION";
    public final static String PROVE        = "PROVE";
    public final static String QED          = "QED";
    public final static String RECURSIVE    = "RECURSIVE";
    public final static String SF_ 			= "SF_";
    public final static String STATE        = "STATE";
    public final static String SUFFICES     = "SUFFICES";
    public final static String SUBSET 		= "SUBSET";
    public final static String TAKE         = "TAKE";
    public final static String TEMPORAL     = "TEMPORAL";
    public final static String THEN 		= "THEN";
    public final static String THEOREM 		= "THEOREM";
    public final static String UNCHANGED 	= "UNCHANGED";
    public final static String UNION 		= "UNION";
    public final static String USE          = "USE";
    public final static String VARIABLE 	= "VARIABLE";
    public final static String VARIABLES 	= "VARIABLES";
    public final static String WF_ 			= "WF_";
    public final static String WITH 		= "WITH";
    public final static String WITNESS      = "WITNESS";
    
    public final static String TRUE         = "TRUE";
    public final static String FALSE        = "FALSE";
    
    
    
    
    public final static String[] ALL_WORDS_ARRAY = new String[]
    {
        ACTION,
        ASSUME,
        ASSUMPTION,
        AXIOM,
        BY,
        CASE,
        CHOOSE,
        CONSTANT,
        CONSTANTS,
        DEF,
        DEFINE,
        DEFS,
        DOMAIN,
        ELSE,
        ENABLED,
        EXCEPT,
        EXTENDS,
        HAVE, 
        HIDE,
        IF,
        IN,
        INSTANCE,
        LAMBDA,
        LEMMA,
        LET,
        LOCAL,
        MODULE,
        NEW,
        OBVIOUS,
        OMITTED,
        OTHER,
        PICK,
        PROOF,
        PROPOSITION,
        PROVE,
        QED,
        RECURSIVE,
        SF_,
        STATE,
        SUBSET,
        SUFFICES,
        TAKE,
        TEMPORAL,
        THEN,
        THEOREM,
        UNCHANGED,
        UNION,
        USE,
        VARIABLE,
        VARIABLES,
        WF_,
        WITH,
        WITNESS
};
    
    public static final String[] ALL_VALUES_ARRAY = {
        TRUE, 
        FALSE
    };
    
    public final static HashSet ALL_WORDS_SET = new HashSet(Arrays.asList(ALL_WORDS_ARRAY));
    
}