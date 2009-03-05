package de.techjava.tla.ui.markers;

/**
 * A set of constants defining TLA Markers
 * 
 * The markers in plugin.xml get their id relative to de.techjava.tla.ui
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: ITLAMarkerTypes.java,v 1.1 2005/08/22 15:43:34 szambrovski Exp $
 */
public interface ITLAMarkerTypes 
{
    /** de.techjava.tla.ui.markers.SanyAbortInitMarker */
    public final static String MARKER_SANY_ABORT_INIT 		= "de.techjava.tla.ui.markers.SanyAbortInitMarker";
    /** de.techjava.tla.ui.markers.SanyErrorInitMarker */
    public final static String MARKER_SANY_ERROR_INIT 		= "de.techjava.tla.ui.markers.SanyErrorInitMarker";
    /** de.techjava.tla.ui.markers.SanyWarningInitMarker */
    public final static String MARKER_SANY_WARN_INIT 		= "de.techjava.tla.ui.markers.SanyWarningInitMarker";
    /** de.techjava.tla.ui.markers.SanyAbortParserMarker */
    public final static String MARKER_SANY_ABORT_PARSER 	= "de.techjava.tla.ui.markers.SanyAbortParserMarker";
    /** de.techjava.tla.ui.markers.SanyErrorParserMarker */
    public final static String MARKER_SANY_ERROR_PARSER 	= "de.techjava.tla.ui.markers.SanyErrorParserMarker";
    /** de.techjava.tla.ui.markers.SanyWarningParserMarker */
    public final static String MARKER_SANY_WARN_PARSER 		= "de.techjava.tla.ui.markers.SanyWarningParserMarker";
    /** de.techjava.tla.ui.markers.SanyAbortSemanticMarker */
    public final static String MARKER_SANY_ABORT_SEMANTIC 	= "de.techjava.tla.ui.markers.SanyAbortSemanticMarker";
    /** de.techjava.tla.ui.markers.SanyErrorSemanticMarker */
    public final static String MARKER_SANY_ERROR_SEMANTIC 	= "de.techjava.tla.ui.markers.SanyErrorSemanticMarker";
    /** de.techjava.tla.ui.markers.SanyWarningSemanticMarker */
    public final static String MARKER_SANY_WARN_SEMANTIC 	= "de.techjava.tla.ui.markers.SanyWarningSemanticMarker";
    
}

/*
 * $Log: ITLAMarkerTypes.java,v $
 * Revision 1.1  2005/08/22 15:43:34  szambrovski
 * sf cvs init
 *
 * Revision 1.2  2004/10/13 10:50:56  bgr
 * ids changed
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.1  2004/10/12 09:55:12  sza
 * additions
 *
 *
 */