// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.st;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import pcal.PCalLocation;
import pcal.Region;

import tlc2.output.EC;
import util.Assert;
import util.UniqueString;

/**
 * A location specifies the position of a syntactic unit in the source.
 * A location is immutable and consists of beginning and ending line and column numbers 
 * and a source name -- usually the name of the file from which the input
 * comes.
 * @author Leslie Lamport, Simon Zambrovski
 * @version $Id$                                                              
 */
public final class Location
{
    // strings used in toString() and Regex
    private static final String LINE = "line ";
    private static final String LINE_CAP = "Line ";
    private static final String TO_LINE = " to line ";
    private static final String COL = ", col ";
    private static final String COLUMN = ", column ";
    private static final String OF_MODULE = " of module ";
    private static final String IN_MODULE = "In module ";
    private static final String IN = " in ";
    private static final String UNKNOWN_LOCATION = "Unknown location";
    private static final String NATURAL = "([0-9]+)";
    private static final String MODULE_ID = "([A-Za-z_0-9]+)";
    private static final String CLOSE_ACTION = ">";
    private static final String OPEN_ACTION = "<Action ";

    private static final UniqueString unknown = UniqueString.uniqueStringOf("--unknown--");

    /**
     * Unknown location
     */
    public static final Location nullLoc = new Location(unknown, 0, 0, 0, 0);

    /**
     * A REGEX pattern to match the locations 
     * <br>
     * The usual code will look like following:
     * <pre>
     * Matcher matcher = Location.LOCATION_MATCHER.matcher(inputString);
     * if (matcher.find()) 
     * {
     *      String locationString = matcher.group();
     *      Location location = Location.parseLocation(locationString); 
     * }
     * </pre>
     * @see {@link Location#parseLocation(String)}
     * @see Location#getParsedLocations(String)
     */
    public static final Pattern LOCATION_MATCHER = Pattern
            .compile(LINE + NATURAL /* bl group */+ COL + NATURAL
            /* bc group */+ TO_LINE + NATURAL /* el group */+ COL + NATURAL /* ec group */+ OF_MODULE + MODULE_ID /* module group */);

    /**
     * A REGEX pattern to match the locations 
     */
    public static final Pattern LOCATION_MATCHER2 = Pattern.compile(IN_MODULE + MODULE_ID /* module group */);

    /**
     * A pattern to match locations in states.
     */
    public static final Pattern LOCATION_MATCHER3 = Pattern.compile(OPEN_ACTION + LINE + NATURAL /* bl group */+ COL
            + NATURAL
            /* bc group */+ TO_LINE + NATURAL /* el group */+ COL + NATURAL /* ec group */+ OF_MODULE + MODULE_ID /* module group */
            + CLOSE_ACTION);

    /**
     * A pattern to match locations when there is an error evaluating a nested expression.
     */
    public static final Pattern LOCATION_MATCHER4 = Pattern
            .compile(LINE_CAP + NATURAL /* bl group */+ COLUMN + NATURAL
            /* bc group */+ TO_LINE + NATURAL /* el group */+ COLUMN + NATURAL /* ec group */+ IN + MODULE_ID /* module group */);

    /**
     * An array containing all {@link Pattern} currently defined
     * in this class.
     */
    public static final Pattern[] ALL_PATTERNS = new Pattern[] { LOCATION_MATCHER, LOCATION_MATCHER2,
            LOCATION_MATCHER3, LOCATION_MATCHER4 };

    protected UniqueString name;
    protected int bLine, bColumn, eLine, eColumn;

    /**
     * Constructs a location
     * @param fName name of the source
     * @param bl begin line
     * @param bc begin column
     * @param el end line
     * @param ec end column
     */
    public Location(UniqueString fName, int bl, int bc, int el, int ec)
    {
        name = fName;
        bLine = bl;
        bColumn = bc;
        eLine = el;
        eColumn = ec;
    }

    public Location(int bl, int bc, int el, int ec) {
		this(null, bl, bc, el, ec);
	}

	
	/**
	 * @param coordinates
	 *            An int array of size 4 with 0-based coordinates: 0=beginLine,
	 *            1=beginColum, 2=endLine, 3=endColumn. 2 & 3 may be smaller
	 *            than 1 & 2, in which case they get set to 1 & 2.
	 */
	public Location(final int[] coordinates) {
	    // LL modified error message on 7 April 2012
		Assert.check(coordinates != null && coordinates.length == 4, "Illegal coordinates found.");

        bLine = coordinates[0];
        bColumn = coordinates[1];

        eLine = coordinates[2];
		eColumn = coordinates[3];
		
		if (eLine < bLine) {
			eLine = bLine;
		}
		
		if (eColumn < bColumn) {
			eColumn = bColumn;
		}
	}

	/**
     * Factory method to create unknown locations in a given module
     * @param moduleName, string representation of the module name
     * @return a location
     */
    public static Location moduleLocation(String moduleName)
    {
        return new Location(UniqueString.uniqueStringOf(moduleName), 0, 0, 0, 0);
    }

    /**
     * Parses location from its string representation  
     * @param locationString the string representation produced by {@link Location#toString()} method
     * @return location if it could be parsed, or a {@link Location#nullLoc} otherwise
     */
    public static Location parseLocation(String locationString)
    {
        if (locationString == null || locationString.length() == 0 || UNKNOWN_LOCATION.equals(locationString))
        {
            return nullLoc;
        }

        Matcher matcher;
        /*
         * In module (unknown coordinates) 
         */
        if ((matcher = LOCATION_MATCHER2.matcher(locationString)).matches())
        {
            // the REGEX LOCATION_MATCHER2 defines one group
            // which captures the module name
            return moduleLocation(matcher.group(1));
        } else if ((matcher = LOCATION_MATCHER.matcher(locationString)).matches())
        {
            // REGEX LOCATION_MATCHER defines 5 groups
            // these are: bl, bc, el, ec, moduleName
            try
            {
                return new Location(UniqueString.uniqueStringOf(matcher.group(5)), Integer.parseInt(matcher.group(1)),
                        Integer.parseInt(matcher.group(2)), Integer.parseInt(matcher.group(3)), Integer
                                .parseInt(matcher.group(4)));
            } catch (NumberFormatException e)
            {
                return nullLoc;
            }
        } else if ((matcher = LOCATION_MATCHER3.matcher(locationString.trim())).matches())
        {
            // REGEX LOCATION_MATCHER3 defines 5 groups
            // these are: bl, bc, el, ec, moduleName
            try
            {
                return new Location(UniqueString.uniqueStringOf(matcher.group(5)), Integer.parseInt(matcher.group(1)),
                        Integer.parseInt(matcher.group(2)), Integer.parseInt(matcher.group(3)), Integer
                                .parseInt(matcher.group(4)));
            } catch (NumberFormatException e)
            {
                return nullLoc;
            }
        } else if ((matcher = LOCATION_MATCHER4.matcher(locationString.trim())).matches())
        {
            // REGEX LOCATION_MATCHER3 defines 5 groups
            // these are: bl, bc, el, ec, moduleName
            try
            {
                return new Location(UniqueString.uniqueStringOf(matcher.group(5)), Integer.parseInt(matcher.group(1)),
                        Integer.parseInt(matcher.group(2)), Integer.parseInt(matcher.group(3)), Integer
                                .parseInt(matcher.group(4)));
            } catch (NumberFormatException e)
            {
                return nullLoc;
            }
        } else
        {
            // not recognized pattern
            return nullLoc;
        }
    }

    /**
     * Returns an array of {@link Location} that can be parsed
     * from the input. More precisely, this method returns all
     * instances of {@link Location} <code>loc</code> such that
     * 
     * <pre>
     * loc != null && !loc.equals(Location.nullLoc)
     * </pre>
     * 
     * and such that there exists some substring <code>sub</code> of input
     * for which
     * 
     * <pre>
     * Location loc = Location.parseLocation(sub)
     * </pre>
     * 
     * @param input
     * @return
     * @see Location#nullLoc
     */
    public static Location[] getParsedLocations(String input)
    {
        /*
         * The Toolbox does not support generics,
         * so generics cannot be used here.
         */
        List<Location> locations = new ArrayList<Location>();
        /*
         * For each Pattern defined in this class, we find
         * all matches of the pattern and add this to the list
         * of locations.
         * 
         * Do not add locations that are null or equal
         * to nullLoc.
         */
        Matcher matcher;
        for (int i = 0; i < ALL_PATTERNS.length; i++)
        {
            matcher = ALL_PATTERNS[i].matcher(input);
            while (matcher.find())
            {
                String locationString = matcher.group();
                Location location = Location.parseLocation(locationString);
                if (location != null && !location.equals(nullLoc))
                {
                    locations.add(location);
                }
            }
        }

        return (Location[]) locations.toArray(new Location[locations.size()]);
    }

    /** 
     * gets the begin line number of this location. 
     */
    public final int beginLine()
    {
        return this.bLine;
    }

    /** 
     * gets the begin column number of this location. 
     */
    public final int beginColumn()
    {
        return this.bColumn;
    }

    /** 
     * gets the end line number of this location. 
     */
    public final int endLine()
    {
        return this.eLine;
    }

    /** 
     * gets the end column number of this location. 
     */
    public final int endColumn()
    {
        return this.eColumn;
    }

    /** 
     * gets the file name of this location. 
     */
    public final String source()
    {
        return name.toString();
    }

    /**
     * This method should be called by all tools to print the location, so
     * users see a consistent method of identifying a location. I        
     * recommend something like                                           
     *                                                                    
     *   line 17, col 22 to line 18, col 13 of module Foo                   
     *                                                                    
     * where source() = "Foo".                                       
     */
    public final String toString()
    {
        if (this == nullLoc)
        {
            return UNKNOWN_LOCATION;
        } else if (this.name == null) // this arm added by LL on 12 Jun 2010
        {
            return (LINE + bLine + COL + bColumn + TO_LINE + eLine + COL + eColumn + OF_MODULE + "null");
        }
        else if (
             !this.name.equals(unknown) && this.bColumn == 0 && this.eColumn == 0 && this.bLine == 0
                && this.eLine == 0)
        {
            return IN_MODULE + name; // Changed from "Unknown location in module..." by LL on 4 Aug 2009
        } else
        {
            return (LINE + bLine + COL + bColumn + TO_LINE + eLine + COL + eColumn + OF_MODULE + name);
        }
    }

    /**
     * Returns true if object is an instance of Location
     * and has the same begin line, begin column, end line,
     * end column, and module name.
     */
    public boolean equals(Object object)
    {
        if (object instanceof Location)
        {
            Location loc = (Location) object;
            return loc.bLine == bLine && loc.bColumn == bColumn && loc.eLine == eLine && loc.eColumn == eColumn
                    && loc.source().equals(source());
        }

        return false;
    }

	/**
	 * Translates the {@link Location} into a PCal {@link Region} adjusting the
	 * 1-based offset to a 0-based one.
	 * 
	 * @return a 0-based {@link Region}
	 */
	public Region toRegion() {
		return new pcal.Region(new PCalLocation(bLine - 1, bColumn - 1),
				new PCalLocation(eLine - 1, eColumn - 1));
	}
}
