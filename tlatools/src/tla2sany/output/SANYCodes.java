package tla2sany.output;

import tlc2.output.EC;

/**
 * Provides error codes for SANY.
 * 
 * @author Simon Zambrovski, Leslie Lamport
 * @version $Id$
 */
public interface SANYCodes 
{

    public final static int UNKNOWN = EC.UNKNOWN;
    
    /* All codes should be above 4000! */
    public final static int SANY_PARSER_CHECK = 4000;
    /* new codes goes here */

    public static final int UNIT_TEST = 4001;

    
    
}
