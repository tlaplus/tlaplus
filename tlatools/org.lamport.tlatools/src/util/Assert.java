// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Last modified on Tue 13 May 2008 at  1:06:18 PST by lamport
//      modified on Wed Jul 25 11:56:59 PDT 2001 by yuanyu

package util;

import tla2sany.semantic.SemanticNode;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.StatefulRuntimeException;
import tlc2.util.Context;

/**
 * A toolkit for checking conditions and throwing unchecked exceptions if they are not met.
 *
 * @author Yuan Yu, Simon Zambrovski
 */
public class Assert {
    /**
     * Unconditioned way to throw an exception
     *
     * @param reason the explaining message to be enclosed into the exception
     */
    public static void fail(final String reason) throws RuntimeException {
        throw new TLCRuntimeException(reason);
    }

    public static void fail(final String reason, final SemanticNode expr) throws RuntimeException {
        if (expr == null) {
            // expr is null if Value#getSource returns null in Tool.
            fail(reason);
        } else {
            throw new TLCDetailedRuntimeException(reason, expr, Context.Empty);
        }
    }

    public static void fail(final String reason, final SemanticNode expr, final Context ctxt) throws RuntimeException {
        if (expr == null) {
            fail(reason);
        } else {
            throw new TLCDetailedRuntimeException(reason, expr, ctxt);
        }
    }

    /**
     * Unconditioned way to throw an exception
     *
     * @param errorCode  error code of explanation
     * @param parameters parameters for the message
     */
    public static void fail(final int errorCode, final String[] parameters) {
        throw new TLCRuntimeException(errorCode, parameters, MP.getMessage(errorCode, parameters));
    }

    public static void fail(final int errorCode, final String[] parameters, final SemanticNode expr) {
        if (expr == null) {
            fail(errorCode, parameters);
        } else {
            throw new TLCDetailedRuntimeException(errorCode, parameters, MP.getMessage(errorCode, parameters), expr, Context.Empty);
        }
    }

    public static void fail(final int errorCode, final String[] parameters, final SemanticNode expr, final Context ctxt) {
        if (expr == null) {
            fail(errorCode, parameters);
        } else {
            throw new TLCDetailedRuntimeException(errorCode, parameters, MP.getMessage(errorCode, parameters), expr, ctxt);
        }
    }

    /**
     * Unconditioned way to throw an exception
     *
     * @param errorCode error code of explanation
     * @param parameter parameter for the message
     */
    public static void fail(final int errorCode, final String parameter) {
        throw new TLCRuntimeException(errorCode, new String[]{parameter}, MP.getMessage(errorCode, parameter));
    }

    public static void fail(final int errorCode, final String parameter, final SemanticNode expr, final Context ctxt) {
        if (expr == null) {
            fail(errorCode, parameter);
        } else {
            throw new TLCDetailedRuntimeException(errorCode, new String[]{parameter}, MP.getMessage(errorCode, parameter), expr, ctxt);
        }
    }

    /**
     * Unconditioned way to throw an exception, the runtime will chain the cause
     *
     * @param errorCode error code of explanation
     * @param cause     reason of the fail and the message for the runtime exception
     */
    public static void fail(final int errorCode, final Throwable cause) {
        throw new TLCRuntimeException(errorCode, MP.getMessage(errorCode, cause.getMessage()), cause);
    }

    /**
     * Unconditioned way to throw an exception
     *
     * @param errorCode error code of explanation
     */
    public static void fail(final int errorCode) {
        throw new TLCRuntimeException(errorCode, MP.getMessage(errorCode));
    }

    /**
     * Checks whether the condition is true. Throws an unchecked exception if otherwise
     *
     * @param condition condition the condition to check
     * @param errorCode error code of explanation
     */
    public static void check(final boolean condition, final int errorCode, final String[] parameters) throws RuntimeException {
        if (!condition) {
            throw new TLCRuntimeException(errorCode, parameters, MP.getMessage(errorCode, parameters));
        }
    }

    /**
     * Checks whether the condition is true. Throws an unchecked exception if otherwise
     *
     * @param condition condition the condition to check
     * @param errorCode error code of explanation
     */
    public static void check(final boolean condition, final int errorCode, final String parameter) throws RuntimeException {
        if (!condition) {
            throw new TLCRuntimeException(errorCode, new String[]{parameter}, MP.getMessage(errorCode, parameter));
        }
    }

    /**
     * Checks whether the condition is true. Throws an unchecked exception if otherwise
     *
     * @param condition condition the condition to check
     * @param errorCode error code of explanation
     */
    public static void check(final boolean condition, final int errorCode) throws RuntimeException {
        if (!condition) {
            throw new TLCRuntimeException(errorCode, MP.getMessage(errorCode));
        }
    }

    /**
     * The following method added by LL on 5 Oct 2009 because, for some unknown reason,
     * javacc seems to have begun generating code that requires such a method.
     * <p>
     * Someone removed it (probably Simon Z), presumably because it was no longer needed
     * by javacc.  However, it was added again by LL on 7 April 2012 to replace
     * check(boolean, int) above when it was called with error code EC.GENERAL, which
     * produces no useful message.
     * <p>
     * Checks whether the condition is true. Throws an unchecked exception if otherwise
     *
     * @param condition condition the condition to check
     * @param errorMsg  error explanation
     */
    public static void check(final boolean condition, final String errorMsg) throws RuntimeException {
        if (!condition) {
            throw new TLCRuntimeException(errorMsg);
        }
    }

    @SuppressWarnings("serial")
    public static class TLCRuntimeException extends StatefulRuntimeException {

        public final int errorCode;
        public String[] parameters = null;

        public TLCRuntimeException(final String errorMsg) {
            super(errorMsg);
            this.errorCode = EC.GENERAL; // Unknown error code.
        }

        public TLCRuntimeException(final int errorCode, final String message) {
            super(message);
            this.errorCode = errorCode;
        }

        public TLCRuntimeException(final int errorCode, final String message, final Throwable cause) {
            super(message, cause);
            this.errorCode = errorCode;
        }

        public TLCRuntimeException(final int errorCode, final String[] parameters, final String message) {
            this(errorCode, message);
            this.parameters = parameters;
        }
    }

    @SuppressWarnings("serial")
    public static class TLCDetailedRuntimeException extends TLCRuntimeException {

        public final SemanticNode expr;
        public final Context ctxt;

        public TLCDetailedRuntimeException(final String errorMsg, final SemanticNode expr, final Context ctxt) {
            this(EC.GENERAL, errorMsg, expr, ctxt);
        }

        public TLCDetailedRuntimeException(final int errorCode, final String message, final SemanticNode expr, final Context ctxt) {
            super(errorCode, message);
            this.expr = expr;
            this.ctxt = ctxt;
        }

        public TLCDetailedRuntimeException(final int errorCode, final String[] parameters, final String message, final SemanticNode expr, final Context ctxt) {
            super(errorCode, parameters, message);
            this.expr = expr;
            this.ctxt = ctxt;
        }
    }
}
