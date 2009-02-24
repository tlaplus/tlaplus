package tlc2.util;

import java.io.IOException;
import java.io.PrintWriter;

import tlc2.tool.TLCState;
import util.FileUtil;

/**
 * State writer 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class StateWriter
{
    private PrintWriter writer;
    private int stateNum;

    public StateWriter(String fname) throws IOException
    {
        // SZ Feb 24, 2009: stream creation moved
        this.writer = new PrintWriter(FileUtil.newBFOS(fname));
        this.stateNum = 1;
    }

    public synchronized void writeState(TLCState state)
    {
        this.writer.println("State " + this.stateNum + ":");
        this.writer.println(state.toString());
        this.stateNum++;
    }

    public final void close()
    {
        this.writer.close();
    }
}
