package de.techjava.tla.ui.util;

import org.eclipse.swt.graphics.RGB;

/**
 * Encapsulates colors for TLA+ editor
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: ITLAEditorColorConstants.java,v 1.1 2005/08/22 15:43:31 szambrovski Exp $
 */
public interface ITLAEditorColorConstants 
{
    // ztztzt
	public final static RGB DEFAULT_COMMENT_COLOR 				= new RGB( 63, 127,  95);
	public final static RGB DEFAULT_COMMENT_MULTI_COLOR 		= new RGB( 63,  95, 191);
	public final static RGB DEFAULT_RESERVED_COLOR 				= new RGB(127, 	 0,  85);
	public final static RGB DEFAULT_TEXT_COLOR 					= new RGB(  0,   0,   0);
	public final static RGB DEFAULT_OPERATOR_COLOR 				= new RGB(127, 159, 191);
	public final static RGB DEFAULT_CTX_INFORMATION_POPUP_BG 	= new RGB(225, 225, 127);
	public final static RGB DEFAULT_IDENTIFIER 					= new RGB( 39, 134, 230);
	
    
	public static final String COMMENT 					= "__comment";
	public static final String COMMENT_MULTILINE 		= "__commentMultiLine";
	public static final String RESERVED 				= "__reserved";
	public static final String TEXT 					= "__text";
    public static final String OPERATOR 				= "__operator";
    public static final String CTX_INFORMATION_POPUP_BG = "__contextInformationPopupBackground";
    public static final String IDENTIFIER 				= "__identifier";
	
}

/*
 * $Log: ITLAEditorColorConstants.java,v $
 * Revision 1.1  2005/08/22 15:43:31  szambrovski
 * sf cvs init
 *
 * Revision 1.6  2004/10/27 15:21:47  sza
 * default colors changed
 *
 * Revision 1.5  2004/10/20 22:42:31  sza
 * editor improvements
 *
 * Revision 1.4  2004/10/13 21:42:08  sza
 * new colors
 *
 * Revision 1.3  2004/10/13 19:30:26  sza
 * new colors
 *
 * Revision 1.2  2004/10/13 14:43:14  sza
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