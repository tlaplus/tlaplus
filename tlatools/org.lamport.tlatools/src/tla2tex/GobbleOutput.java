// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
 * CLASS GobbleOutput                                                       *
 *                                                                          *
 * When you execute a system command with the exec method of the Runtime    *
 * class, the output produced by the command is put into a buffer.  If      *
 * that buffer fills up, the command hangs waiting for the output to be     *
 * read from that buffer.  A GobbleOutput object is used to read that       *
 * output from the buffer and throw it away.                                *
 *                                                                          *
 * A GobbleOutput object is a thread.  The code                             *
 *                                                                          *
 *    GobbleOutput threadObj = new GobbleOutput(bool, proc, str);           *
 *    threadObj.start() ;                                                   *
 *                                                                          *
 * launches a thread that reads and throws away the output produced         *
 * by Process proc on either stdout (if bool = true) or stderr (if          *
 * bool = false).  If you're not sure where proc sends its output,          *
 * you can launch two threads to read both output streams.                  *
 *                                                                          *
 * The String str is the name of the command, and is used only for an       *
 * error message.                                                           *
 ***************************************************************************/
package tla2tex;

import java.io.InputStream;

public class GobbleOutput extends Thread {
    final boolean stdOrError;
    /**********************************************************************
     * True  if gobbling stdout                                            *
     * False if gobbling stderr                                            *
     **********************************************************************/
    final Process proc;
    final String cmd;

    GobbleOutput(final boolean stdOrError,
                 final Process proc,
                 final String cmd) {
        this.stdOrError = stdOrError;
        this.proc = proc;
        this.cmd = cmd;
    }

    @Override
    public void run() {
        InputStream outStream;
        if (stdOrError) {
            outStream = proc.getInputStream();
        } else {
            outStream = proc.getErrorStream();
        }
        final byte[] readBytes = new byte[100000];
        int outBytes = 1;
        try {
            while (outBytes != -1) {
                outBytes = outStream.read(readBytes);
            }
        } catch (final Exception e) {
            Debug.ReportError(
                    "Trying to read output for command\n " + cmd +
                            "\n produced the following error\n    " + e.getMessage());
        }
    }
}