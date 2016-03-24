package tlc2.util;

import java.io.IOException;
import java.io.PrintWriter;

import tlc2.tool.TLCState;
import util.FileUtil;

/**
 * State writer 
 * @author Simon Zambrovski
 */
public class StateWriter implements IStateWriter
{
    protected final PrintWriter writer;
    protected int stateNum;

    public StateWriter(String fname) throws IOException
    {
        // SZ Feb 24, 2009: stream creation moved
        this.writer = new PrintWriter(FileUtil.newBFOS(fname));
        this.stateNum = 1;
    }

    /* (non-Javadoc)
	 * @see tlc2.util.IStateWriter#writeState(tlc2.tool.TLCState)
	 */
    public synchronized void writeState(TLCState state)
    {
        this.writer.println("State " + this.stateNum + ":");
        this.writer.println(state.toString());
        this.stateNum++;
    }

    /* (non-Javadoc)
	 * @see tlc2.util.IStateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.TLCState, boolean)
	 */
    public synchronized void writeState(final TLCState state, final TLCState successor, final boolean successorStateIsNew)
    {
    	if (successorStateIsNew) {
    		this.writeState(state);
    	}
    }

    /* (non-Javadoc)
     * @see tlc2.util.IStateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.TLCState, boolean, tlc2.util.IStateWriter.Visualization)
     */
    public void writeState(TLCState state, TLCState successor, final boolean successorStateIsNew, final Visualization visualization) {
    	if (successorStateIsNew) {
    		this.writeState(state);
    	}
    }
    
    public void close()
    {
        this.writer.close();
    }
}
