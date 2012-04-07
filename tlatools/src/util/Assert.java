// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Last modified on Tue 13 May 2008 at  1:06:18 PST by lamport
//      modified on Wed Jul 25 11:56:59 PDT 2001 by yuanyu

package util;

import tlc2.output.EC;
import tlc2.output.MP;

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
     * @deprecated Use {@link EC} constants instead
     */
    public static void fail(String reason) throws RuntimeException
    {
        throw new RuntimeException(reason);
    }

    /**
     * Unconditioned way to throw an exception
     * @param errorCode error code of explanation
     * @param parameters parameters for the message
     */
    public static void fail(int errorCode, String[] parameters)
    {
        throw new RuntimeException(MP.getMessage(errorCode, parameters));
    }
    
    /**
     * Unconditioned way to throw an exception
     * @param errorCode error code of explanation
     * @param parameter parameter for the message
     */
    public static void fail(int errorCode, String parameter)
    {
        throw new RuntimeException(MP.getMessage(errorCode, parameter));
    }

    /**
     * Unconditioned way to throw an exception, the runtime will chain the cause
     * @param errorCode error code of explanation
     * @param cause reason of the fail and the message for the runtime exception
     */
    public static void fail(int errorCode, Throwable cause)
    {
        throw new RuntimeException(MP.getMessage(errorCode, cause.getMessage()), cause);
    }

    /**
     * Unconditioned way to throw an exception
     * @param errorCode error code of explanation
     */
    public static void fail(int errorCode)
    {
        throw new RuntimeException(MP.getMessage(errorCode));
    }

    /**
     * Checks whether the condition is true. Throws an unchecked exception if otherwise
     * @param condition condition the condition to check
     * @param errorCode error code of explanation
     * @param parameter parameter for the message
     * @throws RuntimeException
     */
    public static void check(boolean condition, int errorCode, String[] parameters) throws RuntimeException
    {
        if (!condition) 
        {
            throw new RuntimeException(MP.getMessage(errorCode, parameters));
        }
    }

    /**
     * Checks whether the condition is true. Throws an unchecked exception if otherwise
     * @param condition condition the condition to check
     * @param errorCode error code of explanation
     * @param parameters parameters for the message
     * @throws RuntimeException
     */
    public static void check(boolean condition, int errorCode, String parameter) throws RuntimeException
    {
        if (!condition) 
        {
            throw new RuntimeException(MP.getMessage(errorCode, parameter));
        }
    }

    /**
     * Checks whether the condition is true. Throws an unchecked exception if otherwise
     * @param condition condition the condition to check
     * @param errorCode error code of explanation
     * @throws RuntimeException
     */
    public static void check(boolean condition, int errorCode) throws RuntimeException
    {
        if (!condition) 
        {
            throw new RuntimeException(MP.getMessage(errorCode));
        }
    }

    /**
     * The following method added by LL on 5 Oct 2009 because, for some unknown reason, 
     * javacc seems to have begun generating code that requires such a method.
     * 
     * Someone removed it (probably Simon Z), presumably because it was no longer needed
     * by javacc.  However, it was added again by LL on 7 April 2012 to replace
     * check(boolean, int) above when it was called with error code EC.GENERAL, which
     * produces no useful message.
     * 
     * Checks whether the condition is true. Throws an unchecked exception if otherwise
     * @param condition condition the condition to check
     * @param errorMsg error explanation
     * @throws RuntimeException
     */
    public static void check(boolean condition, String errorMsg) throws RuntimeException
    {
        if (!condition) 
        {
            throw new RuntimeException(errorMsg);
        }
    }

}
