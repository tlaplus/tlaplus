package tlc2.tool.distributed.selector;

import tlc2.tool.TLCState;
import tlc2.tool.distributed.TLCServer;
import tlc2.tool.distributed.TLCWorkerRMI;
import tlc2.tool.queue.IStateQueue;

public class StaticBlockSelector extends BlockSelector {
    /**
     * System property to set a fixed block size
     */
    private static final String BLOCK_SIZE = "tlc2.tool.distributed.TLCServerThread.BlockSize";
    /**
     * TLC server threads manage the set of existing TLC workers.
     */
    private static final int BlockSize = Integer.getInteger(BLOCK_SIZE, 1024);

    StaticBlockSelector(final TLCServer aTLCServer) {
        super(aTLCServer);
        averageBlockCnt = BlockSize;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.BlockSelector#getBlocks(tlc2.tool.queue.StateQueue, tlc2.tool.distributed.TLCWorkerRMI)
     */
    @Override
    public TLCState[] getBlocks(final IStateQueue stateQueue, final TLCWorkerRMI worker) {
        return stateQueue.sDequeue(BlockSize);
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.selector.BlockSelector#setAverageBlockCnt(long)
     */
    @Override
    protected void setAverageBlockCnt(final long blockCnt) {
        // nop
    }
}
