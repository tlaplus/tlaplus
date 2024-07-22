package tlc2.tool.liveness;

import java.io.IOException;

import tlc2.util.statistics.IBucketStatistics;

public class DebugTableauDiskGraph extends TableauDiskGraph {

	private static final String FORMAT = "%s%sdgraph_%03d_%s.dot";

	private final OrderOfSolution oos;
	private int counter = 0;

	public DebugTableauDiskGraph(String metadir, int soln, IBucketStatistics graphStats, OrderOfSolution oos)
			throws IOException {
		super(metadir, soln, graphStats);
		this.oos = oos;
	}

	@Override
	public long addNode(final GraphNode node) throws IOException {
		try {
			return super.addNode(node);
		} finally {
			writeDotViz(oos, new java.io.File(String.format(FORMAT, metadir, java.io.File.separator, counter++,
					Long.toString(node.stateFP).substring(0, 6))));
		}

	}

	@Override
	public int setDone(final long fp) {
		try {
			return super.setDone(fp);
		} finally {
			writeDotViz(oos, new java.io.File(String.format(FORMAT, metadir, java.io.File.separator, counter++,
					Long.toString(fp).substring(0, 6))));
		}
	}

	@Override
	public void recordNode(final long fp, final int tidx) {
		try {
			super.recordNode(fp, tidx);
		} finally {
			writeDotViz(oos, new java.io.File(String.format(FORMAT, metadir, java.io.File.separator, counter++,
					Long.toString(fp).substring(0, 6))));
		}
	}
}
