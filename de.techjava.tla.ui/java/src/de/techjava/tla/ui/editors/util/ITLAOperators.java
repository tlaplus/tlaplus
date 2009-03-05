package de.techjava.tla.ui.editors.util;

import java.util.Arrays;
import java.util.HashSet;

/**
 * Defines a set of TLA+ Operators
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: ITLAOperators.java,v 1.1 2005/08/22 15:43:33 szambrovski Exp $
 */
public interface ITLAOperators 
{
    /*
     * Prefix operators
     */
    public final static String OP_PRE_01			= "-";
    public final static String OP_PRE_02			= "~";
    public final static String OP_PRE_03			= "\\lnot";
    public final static String OP_PRE_04			= "\\neg";
    public final static String OP_PRE_05			= "[]";
    public final static String OP_PRE_06			= "<>";
    public final static String OP_PRE_07			= "DOMAIN";
    public final static String OP_PRE_08			= "ENABLED";
    public final static String OP_PRE_09			= "SUBSET";
    public final static String OP_PRE_10			= "UNCHAGED";
    public final static String OP_PRE_11			= "UNION";

    /*
     * Infix operators
     */
    public final static String OP_INF_01			= "!!";
    public final static String OP_INF_02			= "&";
    public final static String OP_INF_03			= "*";
    public final static String OP_INF_04			= "-|";
    public final static String OP_INF_05			= "::=";
    public final static String OP_INF_06			= "=<";
    public final static String OP_INF_07			= "@@";
    public final static String OP_INF_08			= "|=";
    public final static String OP_INF_09			= "#";
    public final static String OP_INF_10			= "&&";
    public final static String OP_INF_11			= "**";
    public final static String OP_INF_12			= "..";
    public final static String OP_INF_13			= ":=";
    public final static String OP_INF_14			= "=>";
    public final static String OP_INF_15			= "\\";
    public final static String OP_INF_16			= "||";
    public final static String OP_INF_17			= "##";
    public final static String OP_INF_18			= "(*)";
    public final static String OP_INF_19			= "+";
    public final static String OP_INF_20			= "...";
    public final static String OP_INF_21			= ":>";
    public final static String OP_INF_22			= "=|";
    public final static String OP_INF_23			= "\\/";
    public final static String OP_INF_24			= "~>";
    public final static String OP_INF_25			= "$";
    public final static String OP_INF_26			= "(-)";
    public final static String OP_INF_27			= "++";
    public final static String OP_INF_28			= "/";
    public final static String OP_INF_29			= "<";
    public final static String OP_INF_30			= ">";
    public final static String OP_INF_31			= "^";
    public final static String OP_INF_32			= ".";
    public final static String OP_INF_33			= "$$";
    public final static String OP_INF_34			= "(.)";
    public final static String OP_INF_35			= "-";
    public final static String OP_INF_36			= "//";
    public final static String OP_INF_37			= "<:";
    public final static String OP_INF_38			= ">=";
    public final static String OP_INF_39			= "^^";
    public final static String OP_INF_40			= "%";
    public final static String OP_INF_41			= "(/)";
    public final static String OP_INF_42			= "-+->";
    public final static String OP_INF_43			= "/=";
    public final static String OP_INF_44			= "<=>";
    public final static String OP_INF_45			= "?";
    public final static String OP_INF_46			= "|";
    public final static String OP_INF_47			= "%%";
    public final static String OP_INF_48			= "(\\X)";
    public final static String OP_INF_49			= "--";
    public final static String OP_INF_50			= "/\\";
    public final static String OP_INF_51			= "=";
    public final static String OP_INF_52			= "??";
    public final static String OP_INF_53			= "|-";


    public final static String OP_APROX 		= "\\aprox";
    public final static String OP_ASYMP 		= "\\asymp";
    public final static String OP_BIGCIRC 		= "\\bigcirc";
    public final static String OP_BULLET 		= "\\bullet";
    public final static String OP_CAP 			= "\\cap";
    public final static String OP_CDOT 			= "\\cdot";
    public final static String OP_CIRC 			= "\\circ";
    public final static String OP_CONG 			= "\\cong";
    public final static String OP_CUP 			= "\\cup";
    public final static String OP_DIV 			= "\\div";
    public final static String OP_DOTEQ 		= "\\doteq";
    public final static String OP_EQUIV 		= "\\equiv";
    public final static String OP_GEQ 			= "\\geg";
    public final static String OP_GG 			= "\\gg";
    public final static String OP_IN 			= "\\in";
    public final static String OP_INTERSECT 	= "\\intersect";
    public final static String OP_LAND 			= "\\land";
    public final static String OP_LEQ   		= "\\leq";
    public final static String OP_LL 	 		= "\\ll";
    public final static String OP_LOR     		= "\\lor";
    public final static String OP_O      		= "\\o";
    public final static String OP_ODOT			= "\\odot";
    public final static String OP_OMINUS		= "\\ominus";
    public final static String OP_OPLUS			= "\\oplus";
    public final static String OP_OSLASH		= "\\oslash";
    public final static String OP_OTIMES		= "\\otimes";
    public final static String OP_PREC			= "\\prec";
    public final static String OP_PRECEQ		= "\\preceq";
    public final static String OP_PROPTO		= "\\propto";
    public final static String OP_SIM 			= "\\sim";
    public final static String OP_SIMEQ			= "\\simeq";
    public final static String OP_SQCAP			= "\\sqcap";
    public final static String OP_SQSUBSET  	= "\\sqsubset";
    public final static String OP_SQSUBSETEQ	= "\\sqsubseteq";
    public final static String OP_SQSUPSET		= "\\sqsupset";
    public final static String OP_SQSUPSETEQ	= "\\sqsupseteq";
    public final static String OP_STAR			= "\\star";
    public final static String OP_SUBSET		= "\\subset";
    public final static String OP_SUBSETEQ		= "\\subseteq";
    public final static String OP_SUCC			= "\\succ";
    public final static String OP_SUPSET		= "\\supset";
    public final static String OP_SUPSETEQ		= "\\supseteq";
    public final static String OP_UNION			= "\\union";
    public final static String OP_WR			= "\\wr";

     
    /*
     * Postfix operators
     */
    public final static String OP_POS_01			= "^+";
    public final static String OP_POS_02			= "^*";
    public final static String OP_POS_03			= "^#";
    public final static String OP_POS_04			= "'";
    
    
    public final static String OP_ASSIGNMENT		= "==";
    public final static String OP_TUPLE_BEGIN		= "<<";
    public final static String OP_TUPLE_END			= ">>";
    
    /** Array representation */
    public final static String[] ALL_OPERATOR_ARRAY = new String[]
    {
            // PREFIX
            OP_PRE_01,
            OP_PRE_02,
            OP_PRE_03,
            OP_PRE_04,
            OP_PRE_05,
            OP_PRE_06,
            OP_PRE_07,
            OP_PRE_08,
            OP_PRE_09,
            OP_PRE_10,
            OP_PRE_11,
            
            // INFIX
            OP_APROX,
            OP_ASYMP,
			OP_BIGCIRC,
			OP_BULLET, 		
			OP_CAP, 			
			OP_CDOT, 			
			OP_CIRC, 			
			OP_CONG, 			
			OP_CUP, 			
			OP_DIV, 			
			OP_DOTEQ, 		
			OP_EQUIV, 		
			OP_GEQ, 			
			OP_GG, 			
			OP_IN, 			
			OP_INTERSECT, 	
			OP_LAND, 			
			OP_LEQ,   		
			OP_LL, 	 		
			OP_LOR,     		
			OP_O,      		
			OP_ODOT,			
			OP_OMINUS,		
			OP_OPLUS,			
			OP_OSLASH,		
			OP_OTIMES,		
			OP_PREC,			
			OP_PRECEQ,		
			OP_PROPTO,		
			OP_SIM, 			
			OP_SIMEQ,			
			OP_SQCAP,			
			OP_SQSUBSET,  	
			OP_SQSUBSETEQ,	
			OP_SQSUPSET,		
			OP_SQSUPSETEQ,	
			OP_STAR,			
			OP_SUBSET,		
			OP_SUBSETEQ,		
			OP_SUCC,			
			OP_SUPSET,		
			OP_SUPSETEQ,		
			OP_UNION,			
			OP_WR,          
            OP_INF_01,
            OP_INF_02,
            OP_INF_03,
            OP_INF_04,
            OP_INF_05,
            OP_INF_06,
            OP_INF_07,
            OP_INF_08,
            OP_INF_09,
            OP_INF_10,
            OP_INF_11,
            OP_INF_12,
            OP_INF_13,
            OP_INF_14,
            OP_INF_15,
            OP_INF_16,
            OP_INF_17,
            OP_INF_18,
            OP_INF_19,
            OP_INF_20,
            OP_INF_21,
            OP_INF_22,
            OP_INF_23,
            OP_INF_24,
            OP_INF_25,
            OP_INF_26,
            OP_INF_27,
            OP_INF_28,
            OP_INF_29,
            OP_INF_30,
            OP_INF_31,
            OP_INF_32,
            OP_INF_33,
            OP_INF_34,
            OP_INF_35,
            OP_INF_36,
            OP_INF_37,
            OP_INF_38,
            OP_INF_39,
            OP_INF_40,
            OP_INF_41,
            OP_INF_42,
            OP_INF_43,
            OP_INF_44,
            OP_INF_45,
            OP_INF_46,
            OP_INF_47,
            OP_INF_48,
            OP_INF_49,
            OP_INF_50,
            OP_INF_51,
            OP_INF_52,
            OP_INF_53,
            
            // POSTFIX
            OP_POS_01,
            OP_INF_02,
            OP_INF_03,
            OP_INF_04,
            
            
            OP_ASSIGNMENT
            
            
    };
    /** Hashset representation */
    public final static HashSet ALL_OPERATOR_SET = new HashSet( Arrays.asList(ALL_OPERATOR_ARRAY) );
    
}

/*
 * $Log: ITLAOperators.java,v $
 * Revision 1.1  2005/08/22 15:43:33  szambrovski
 * sf cvs init
 *
 * Revision 1.2  2004/10/20 22:42:31  sza
 * editor improvements
 *
 * Revision 1.1  2004/10/13 14:45:00  sza
 * operators added
 *
 *
 */