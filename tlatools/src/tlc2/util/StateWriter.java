package tlc2.util;

import java.io.IOException;
import java.io.PrintWriter;

import tlc2.tool.Action;
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
	private String fname;

    public StateWriter(String fname) throws IOException
    {
        this.fname = fname;
        this.writer = new PrintWriter(FileUtil.newBFOS(fname));
        this.stateNum = 1;
    }

    /* (non-Javadoc)
     * @see tlc2.util.IStateWriter#getDumpFileName()
     */
    @Override
    public String getDumpFileName() {
    	return this.fname;
    }

	/* (non-Javadoc)
	 * @see tlc2.util.IStateWriter#isNoop()
	 */
	@Override
    public boolean isNoop() {
		return false;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.util.IStateWriter#isDot()
	 */
	@Override
	public boolean isDot() {
		return false;
	}

	/* (non-Javadoc)
	 * @see tlc2.util.IStateWriter#writeState(tlc2.tool.TLCState)
	 */
    @Override
    public synchronized void writeState(TLCState state)
    {
        this.writer.println("State " + this.stateNum + ":");
        this.writer.println(state.toString());
        this.stateNum++;
    }

    /* (non-Javadoc)
	 * @see tlc2.util.IStateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.TLCState, boolean)
	 */
    @Override
    public synchronized void writeState(final TLCState state, final TLCState successor, final boolean successorStateIsNew)
    {
    	if (successorStateIsNew) {
    		this.writeState(state);
    	}
    }

    @Override
    public synchronized void writeState(final TLCState state, final TLCState successor, final boolean successorStateIsNew, Action action)
    {
    	if (successorStateIsNew) {
    		this.writeState(state);
    	}
    }
    
    /* (non-Javadoc)
     * @see tlc2.util.IStateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.TLCState, boolean, tlc2.util.IStateWriter.Visualization)
     */
    @Override
    public void writeState(TLCState state, TLCState successor, final boolean successorStateIsNew, final Visualization visualization) {
    	if (successorStateIsNew) {
    		this.writeState(state);
    	}
    }
    
    /* (non-Javadoc)
     * @see tlc2.util.IStateWriter#close()
     */
    @Override
    public void close()
    {
        this.writer.close();
    }

	/* (non-Javadoc)
	 * @see tlc2.util.IStateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.TLCState, tlc2.util.BitVector, int, int, boolean)
	 */
	@Override
    public void writeState(TLCState state, TLCState successor, BitVector actionChecks, int from, int to, boolean successorStateIsNew) {
    	if (successorStateIsNew) {
    		this.writeState(state);
    	}
	}

	/* (non-Javadoc)
	 * @see tlc2.util.IStateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.TLCState, tlc2.util.BitVector, int, int, boolean, tlc2.util.IStateWriter.Visualization)
	 */
	@Override
    public void writeState(TLCState state, TLCState successor, BitVector actionChecks, int from, int to, boolean successorStateIsNew,
                           Visualization visulation) {
    	if (successorStateIsNew) {
    		this.writeState(state);
    	}
	}
}
