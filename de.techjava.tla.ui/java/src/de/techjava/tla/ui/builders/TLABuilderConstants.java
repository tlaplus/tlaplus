package de.techjava.tla.ui.builders;

import org.eclipse.core.runtime.QualifiedName;


/**
 * Constants used to store the session properties on resources 
 *
 * @author Boris Gruschko ( http://gruschko.org, boris at gruschko.org )
 * @version $Id: TLABuilderConstants.java,v 1.1 2005/08/22 15:43:36 szambrovski Exp $
 */
public interface TLABuilderConstants
{
	public static final QualifiedName LAST_BUILT = 
		new QualifiedName( TLABuilder.BUILDER_ID, "LAST_BUILT" );
}

/*-
 * $Log: TLABuilderConstants.java,v $
 * Revision 1.1  2005/08/22 15:43:36  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/20 17:57:39  bgr
 * incremental build functionality started
 *
 */