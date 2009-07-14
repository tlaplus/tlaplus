// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Last modified on Tue 13 May 2008 at  1:06:18 PST by lamport
//      modified on Wed Jul 25 11:56:59 PDT 2001 by yuanyu

package util;

/**
 * A toolkit for checking conditions and throwing unchecked exceptions if they are not met.
 * 
 * @author Yuan Yu, Simon Zambrovski
 * @version $Id$
 */
public class Assert
{
    /**
     * Unconditioned way to throw an exception
     * @param reason the explaining message to be enclosed into the exception
     */
    public static void fail(String reason) throws RuntimeException
    {
        throw new RuntimeException(reason);
    }

    /**
     * Checks whether the condition is true. Throws an unchecked exception if otherwise
     * @param condition the condition to check
     * @param reason the message explaining the exception
     * @throws RuntimeException
     */
    public static void check(boolean condition, String reason) throws RuntimeException
    {
        if (!condition) 
        {
            throw new RuntimeException(reason);
        }
    }
}
