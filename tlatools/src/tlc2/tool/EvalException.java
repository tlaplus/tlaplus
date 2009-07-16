// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at  9:27:18 PST by lamport
//      modified on Thu Dec  7 20:32:45 PST 2000 by yuanyu

package tlc2.tool;

import tlc2.output.MP;

/**
 * Evaluation exception
 * @author Simon Zambrovski
 * @version $Id$
 */
public class EvalException extends RuntimeException
{
// SZ Jul 14, 2009: not used since error codes are in the {@link EC} class    
//    public final static int ERROR = 0;
//    public final static int ASSERT = 1;
//    private int type;


    public EvalException(int errorCode, String[] parameters)
    {
        super(MP.getMessage(errorCode, parameters));
    }

    public EvalException(int errorCode, String parameter)
    {
        super(MP.getMessage(errorCode, parameter));
    }

    public EvalException(int errorCode)
    {
        super(MP.getMessage(errorCode));        
    }

    
    // SZ Jul 14, 2009: refactored and deprecated, all usage changed to standard constructor 
    // public EvalException(int type, String message)
    // {
    //      super(message);
    //      this.type = type;
    // }
    
    

    // SZ Jul 14, 2009: not used
    // public final int getErrno()
    // {
    //      return this.type;
    // }

    // SZ Jul 14, 2009: not used
    // public final EvalException addMessage(String msg) {
    //      return new EvalException(this.errno, this.getMessage() + "\n" + msg);
    // }

}
