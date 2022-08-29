// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.st;

import pcal.PCalLocation;
import pcal.Region;
import util.TLAConstants;
import util.UniqueString;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * A location specifies the position of a syntactic unit in the source.
 * A location is immutable and consists of beginning and ending line and column numbers
 * and a source name -- usually the name of the file from which the input
 * comes.
 *
 * @author Leslie Lamport, Simon Zambrovski
 * @version $Id$
 */
public final class Location implements Comparable<Location> {
    // strings used in toString() and Regex
    private static final String LINE = TLAConstants.LINE;
    private static final String LINE_CAP = "Line ";
    private static final String TO_LINE = " to line ";
    private static final String COL = ", col ";
    private static final String COLUMN = ", column ";
    private static final String OF_MODULE = " of module ";
    private static final String IN_MODULE = "In module ";
    private static final String IN = " in ";
    private static final String UNKNOWN_LOCATION = "Unknown location";
    private static final String NATURAL = "(\\d+)";
    private static final String MODULE_ID = "(\\w+)";
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
     *
     * @see tla2sany.st.Location#parseLocation(String)
     * @see tla2sany.st.Location#getParsedLocations(String)
     */
    public static final Pattern LOCATION_MATCHER = Pattern
            .compile(LINE + NATURAL /* bl group */ + COL + NATURAL
                    /* bc group */ + TO_LINE + NATURAL /* el group */ + COL + NATURAL /* ec group */ + OF_MODULE + MODULE_ID /* module group */);
    /**
     * A REGEX pattern to match the locations
     */
    public static final Pattern LOCATION_MATCHER2 = Pattern.compile(IN_MODULE + MODULE_ID /* module group */);
    /**
     * A pattern to match locations when there is an error evaluating a nested expression.
     */
    public static final Pattern LOCATION_MATCHER4 = Pattern
            .compile(LINE_CAP + NATURAL /* bl group */ + COLUMN + NATURAL
                    /* bc group */ + TO_LINE + NATURAL /* el group */ + COLUMN + NATURAL /* ec group */ + IN + MODULE_ID /* module group */);
    private static final String CLOSE_ACTION = ">";
    private static final String OPEN_ACTION = "<\\w+ "; // The regex used to just be "Action" but the most recent TLC prints the name of the action instead of just the location.
    /**
     * A pattern to match locations in states.
     */
    public static final Pattern LOCATION_MATCHER3 = Pattern.compile(OPEN_ACTION + LINE + NATURAL /* bl group */ + COL
            + NATURAL
            /* bc group */ + TO_LINE + NATURAL /* el group */ + COL + NATURAL /* ec group */ + OF_MODULE + MODULE_ID /* module group */
            + CLOSE_ACTION);
    /**
     * An array containing all {@link Pattern} currently defined
     * in this class.
     */
    public static final Pattern[] ALL_PATTERNS = new Pattern[]{LOCATION_MATCHER, LOCATION_MATCHER2,
            LOCATION_MATCHER3, LOCATION_MATCHER4};
    private static final UniqueString unknown = UniqueString.uniqueStringOf("--unknown--");
    /**
     * Unknown location
     */
    public static final Location nullLoc = new Location(unknown, 0, 0, 0, 0);
    protected final UniqueString name;
    protected final int bLine;
    protected final int bColumn;
    protected final int eLine;
    protected final int eColumn;

    public Location(final String fName, final String bl, final String bc, final String el, final String ec) {
        this(UniqueString.uniqueStringOf(fName), Integer.parseInt(bl), Integer.parseInt(bc), Integer.parseInt(el),
                Integer.parseInt(ec));
    }

    public Location(final String fName, final int bl, final int bc, final int el, final int ec) {
        this(UniqueString.uniqueStringOf(fName), bl, bc, el, ec);
    }

    /**
     * Constructs a location
     *
     * @param fName name of the source
     * @param bl    begin line
     * @param bc    begin column
     * @param el    end line
     * @param ec    end column
     */
    public Location(final UniqueString fName, final int bl, final int bc, final int el, final int ec) {
        name = fName;
        bLine = bl;
        bColumn = bc;
        eLine = el;
        eColumn = ec;
    }

    public Location(final int bl, final int bc, final int el, final int ec) {
        this((UniqueString) null, bl, bc, el, ec);
    }


    /**
     * Factory method to create unknown locations in a given module
     *
     * @param moduleName, string representation of the module name
     * @return a location
     */
    public static Location moduleLocation(final String moduleName) {
        return new Location(UniqueString.uniqueStringOf(moduleName), 0, 0, 0, 0);
    }

    /**
     * Parses location from its string representation
     *
     * @param locationString the string representation produced by {@link Location#toString()} method
     * @return location if it could be parsed, or a {@link Location#nullLoc} otherwise
     */
    public static Location parseLocation(final String locationString) {
        if (locationString == null || locationString.length() == 0 || UNKNOWN_LOCATION.equals(locationString)) {
            return nullLoc;
        }

        Matcher matcher;
        /*
         * In module (unknown coordinates)
         */
        if ((matcher = LOCATION_MATCHER2.matcher(locationString)).matches()) {
            // the REGEX LOCATION_MATCHER2 defines one group
            // which captures the module name
            return moduleLocation(matcher.group(1));
        } else if ((matcher = LOCATION_MATCHER.matcher(locationString)).matches()) {
            // REGEX LOCATION_MATCHER defines 5 groups
            // these are: bl, bc, el, ec, moduleName
            try {
                return new Location(UniqueString.uniqueStringOf(matcher.group(5)), Integer.parseInt(matcher.group(1)),
                        Integer.parseInt(matcher.group(2)), Integer.parseInt(matcher.group(3)), Integer
                        .parseInt(matcher.group(4)));
            } catch (final NumberFormatException e) {
                return nullLoc;
            }
        } else if ((matcher = LOCATION_MATCHER3.matcher(locationString.trim())).matches()) {
            // REGEX LOCATION_MATCHER3 defines 5 groups
            // these are: bl, bc, el, ec, moduleName
            try {
                return new Location(UniqueString.uniqueStringOf(matcher.group(5)), Integer.parseInt(matcher.group(1)),
                        Integer.parseInt(matcher.group(2)), Integer.parseInt(matcher.group(3)), Integer
                        .parseInt(matcher.group(4)));
            } catch (final NumberFormatException e) {
                return nullLoc;
            }
        } else if ((matcher = LOCATION_MATCHER4.matcher(locationString.trim())).matches()) {
            // REGEX LOCATION_MATCHER3 defines 5 groups
            // these are: bl, bc, el, ec, moduleName
            try {
                return new Location(UniqueString.uniqueStringOf(matcher.group(5)), Integer.parseInt(matcher.group(1)),
                        Integer.parseInt(matcher.group(2)), Integer.parseInt(matcher.group(3)), Integer
                        .parseInt(matcher.group(4)));
            } catch (final NumberFormatException e) {
                return nullLoc;
            }
        } else {
            // not recognized pattern
            return nullLoc;
        }
    }

    public static Location parseCoordinates(final String source, final String coordinates) {
        final String[] c = coordinates.split(" ");
        return new Location(source, c[0], c[1], c[2], c[3]);
    }

    /**
     * Returns an array of {@link Location} that can be parsed
     * from the input. More precisely, this method returns all
     * instances of {@link Location} <code>loc</code> such that
     *
     * <pre>
     * loc != null && !loc.equals(Location.nullLoc)
     * </pre>
     * <p>
     * and such that there exists some substring <code>sub</code> of input
     * for which
     *
     * <pre>
     * Location loc = Location.parseLocation(sub)
     * </pre>
     *
     * @see Location#nullLoc
     */
    public static Location[] getParsedLocations(final String input) {
        /*
         * The Toolbox does not support generics,
         * so generics cannot be used here.
         */
        final List<Location> locations = new ArrayList<>();
        /*
         * For each Pattern defined in this class, we find
         * all matches of the pattern and add this to the list
         * of locations.
         *
         * Do not add locations that are null or equal
         * to nullLoc.
         */
        Matcher matcher;
        for (final Pattern allPattern : ALL_PATTERNS) {
            matcher = allPattern.matcher(input);
            while (matcher.find()) {
                final String locationString = matcher.group();
                final Location location = Location.parseLocation(locationString);
                if (location != null && !location.equals(nullLoc)) {
                    locations.add(location);
                }
            }
        }

        return locations.toArray(new Location[0]);
    }

    /**
     * gets the begin line number of this location.
     */
    public int beginLine() {
        return this.bLine;
    }

    /**
     * gets the begin column number of this location.
     */
    public int beginColumn() {
        return this.bColumn;
    }

    /**
     * gets the end line number of this location.
     */
    public int endLine() {
        return this.eLine;
    }

    public int[] getCoordinates() {
        return new int[]{bLine, bColumn, eLine, eColumn};
    }

    /**
     * gets the end column number of this location.
     */
    public int endColumn() {
        return this.eColumn;
    }

    /**
     * gets the file name of this location.
     */
    public String source() {
        return name != null ? name.toString() : null;
    }

    public UniqueString sourceAsUniqueString() {
        return name;
    }

    /**
     * This method should be called by all tools to print the location, so
     * users see a consistent method of identifying a location. I
     * recommend something like
     * <p>
     * line 17, col 22 to line 18, col 13 of module Foo
     * <p>
     * where source() = "Foo".
     */
    public String toString() {
        if (this == nullLoc) {
            return UNKNOWN_LOCATION;
        } else if (this.name == null) // this arm added by LL on 12 Jun 2010
        {
            return (LINE + bLine + COL + bColumn + TO_LINE + eLine + COL + eColumn + OF_MODULE + "null");
        } else if (
                !this.name.equals(unknown) && this.bColumn == 0 && this.eColumn == 0 && this.bLine == 0
                        && this.eLine == 0) {
            return IN_MODULE + name; // Changed from "Unknown location in module..." by LL on 4 Aug 2009
        } else {
            return (LINE + bLine + COL + bColumn + TO_LINE + eLine + COL + eColumn + OF_MODULE + name);
        }
    }

    /**
     * Returns true if object is an instance of Location
     * and has the same begin line, begin column, end line,
     * end column, and module name.
     */
    public boolean equals(final Object object) {
        if (object instanceof final Location loc) {
            return loc.bLine == bLine && loc.bColumn == bColumn && loc.eLine == eLine && loc.eColumn == eColumn
                    && Objects.requireNonNull(loc.source()).equals(source());
        }

        return false;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + bColumn;
        result = prime * result + bLine;
        result = prime * result + eColumn;
        result = prime * result + eLine;
        result = prime * result + ((name == null) ? 0 : name.hashCode());
        return result;
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

    /**
     * @return returns true if line is in [beginLine, endLine]
     */
    public boolean containsLine(final int line) {
        return ((line >= bLine) && (line <= eLine));
    }

    @Override
    public int compareTo(final Location other) {
        if (this.equals(other)) {
            return 0;
        }
        if (this.name.compareTo(other.name) != 0) {
            return this.name.compareTo(other.name);
        }

        if (this.bLine > other.bLine) {
            return 1;
        } else if (this.bLine < other.bLine) {
            return -1;
        }

        if (this.bColumn > other.bColumn) {
            return 1;
        } else if (this.bColumn < other.bColumn) {
            return -1;
        }

        if (this.eLine > other.eLine) {
            return 1;
        } else if (this.eLine < other.eLine) {
            return -1;
        }

        if (this.eColumn < other.eColumn) {
            return -1;
        }
        return 1;
    }

    /**
     * @return true if other is a location within this location (same module file
     * and the range of chars is within this range of chars).
     */
    public boolean includes(final Location other) {
        if (this.name != other.name) {
            return false;
        }
        if (this.bLine > other.bLine) {
            return false;
        }
        if (this.beginLine() == other.beginLine() && this.beginColumn() > other.beginColumn()) {
            return false;
        }
        if (this.eLine < other.eLine) {
            return false;
        }
        return this.endLine() != other.endLine() || this.endColumn() >= other.endColumn();
    }

    public String linesAndColumns() {
        return toString().replaceAll(OF_MODULE + ".*", "");
    }
}
