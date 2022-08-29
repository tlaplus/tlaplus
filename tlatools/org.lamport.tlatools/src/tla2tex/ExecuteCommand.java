// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
 * CLASS ExecuteCommand                                                     *
 *                                                                          *
 * This class contains the one public method                                *
 *                                                                          *
 *    public static void ExecuteCommand(String cmd);                        *
 *                                                                          *
 * It calls the operating system to execute the command cmd, using two      *
 * GobbleOutput threads to get rid of any output produced by the command.   *
 ***************************************************************************/
package tla2tex;

public class ExecuteCommand {
    public static void executeCommand(final String cmd, final Parameters parameters) {
        int errorCode = -99;
        try {
            final Runtime rt = Runtime.getRuntime();
            Process proc;
            if (parameters.MetaDir.equals("")) {
                proc = rt.exec(cmd);
            } else {
                proc = rt.exec(cmd, null, parameters.ParentDir);
            }
            final GobbleOutput outThread = new GobbleOutput(true, proc, cmd);
            outThread.start();
            final GobbleOutput errThread = new GobbleOutput(false, proc, cmd);
            errThread.start();
            errorCode = proc.waitFor();
            outThread.join();
            errThread.join();
        } catch (final Exception e) {
            Debug.ReportError(
                    "Trying to run the command `" + cmd
                            + "' produced the following error\n    " + e.getMessage());
        }
        if (errorCode < 0) {
            Debug.ReportError(
                    "Running the command `" + cmd
                            + "' produced an error");
        }
    }
}