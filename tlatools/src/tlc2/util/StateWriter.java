package tlc2.util;

import java.io.BufferedOutputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintWriter;

import tlc2.tool.TLCState;
import util.FilenameToStream;

/**
 * State writer 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class StateWriter
{
    private PrintWriter writer;
    private int stateNum;

    public StateWriter(String fname, FilenameToStream resolver) throws IOException
    {
        FileOutputStream fos = new FileOutputStream(fname);
        this.writer = new PrintWriter(new BufferedOutputStream(fos));
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
