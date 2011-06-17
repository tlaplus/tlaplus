package tlc2.tool.distributed;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.net.URI;
import java.util.Date;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import tlc2.TLCGlobals;

public class TLCStatistics {
	
	/**
	 * writes stats to .csv
	 */
	public static void writeStats(TLCServer server, Date processStart,
			Date computationStart, Date processEnd) {
		File sFile;
		File wFile;

		// has the user given an output path?
		final String path = System.getProperty(TLCStatistics.class.getName()
				+ ".path");
		if (path != null) {
			sFile = new File(path + File.separator + "server.csv");
			wFile = new File(path + File.separator + "worker.csv");
		} else {
			sFile = new File("server.csv");
			wFile = new File("worker.csv");
		}

		try {
			sFile.createNewFile();
			wFile.createNewFile();

			serverStats(server, sFile, processStart, computationStart, processEnd);
			workerStats(server, wFile);
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	// create server stats .csv file
	private static void workerStats(TLCServer server, File file)
			throws IOException {
		final FileWriter writer = new FileWriter(file);

		// headlines
		writer.write("WorkerName");
		writer.write(",");
		writer.write("StatesReceived");
		writer.write(",");
		writer.write("StatesComputed");
		writer.write("\n");

		// values
		final TLCServerThread[] threads = server.getThreads();
		for (int i = 0; i < threads.length && threads[i] != null; i++) {
			// print worker stats
			int sentStates = threads[i].getSentStates();
			int receivedStates = threads[i].getReceivedStates();
			URI name = threads[i].getUri();

			writer.write(name.toString());
			writer.write(",");
			writer.write(Integer.toString(sentStates));
			writer.write(",");
			writer.write(Integer.toString(receivedStates));
			writer.write("\n");
		}

		writer.close();
	}

	// create server stats .csv file
	private static void serverStats(TLCServer server, File file,
			Date processStartTime, Date computationStart,
			Date processEndTime) throws IOException {
		final FileWriter writer = new FileWriter(file);

		// headlines
		writer.write("SpecName");
		writer.write(",");
		writer.write("ConfigName");
		writer.write(",");
		writer.write("NumberFingerprintServer");
		writer.write(",");
		writer.write("NumberWorkers");
		writer.write(",");
		writer.write("NumberCores");
		writer.write(",");
		writer.write("ProcessStartupTime");
		writer.write(",");
		writer.write("ComputationStartupTime");
		writer.write(",");
		writer.write("ComputationEndTime");
		writer.write(",");
		writer.write("TimePassedDuringComputationInSeconds");
		writer.write(",");
		writer.write("NumberDistinctStates");
		writer.write(",");
		
		// get all rmi method invocations from monitor if any
		final Map<String, Integer> invocations = RMIMethodMonitor.getInvocations();
		for (Iterator<String> iterator = invocations.keySet().iterator(); iterator.hasNext();) {
			final String methodName = (String) iterator.next();
			writer.write(methodName);
			writer.write(",");
		}
		
		// write "end tag"
		writer.write("\n");

		// values
		writer.write(server.getSpecFileName());
		writer.write(",");
		writer.write(server.getConfigFileName());
		writer.write(",");
		if (TLCGlobals.fpServers == null) {
			writer.write("1");
		} else {
			writer.write(TLCGlobals.fpServers.length);
		}
		writer.write(",");
		writer.write(Integer.toString(server.getWorkerCount()));
		writer.write(",");
		
		// print core count by checking how many threads ran on the same node
		Set<String> hosts = new HashSet<String>();
		final TLCServerThread[] threads = server.getThreads();
		for (int i = 0; i < threads.length && threads[i] != null; i++) {
			String host = threads[i].getUri().getHost();
			hosts.add(host);
		}
		writer.write(Integer.toString(server.getWorkerCount() / hosts.size()));
		writer.write(",");
		
		writer.write(processStartTime.toString());
		writer.write(",");
		writer.write(computationStart.toString());
		writer.write(",");
		writer.write(processEndTime.toString());
		writer.write(",");
		writer.write(new Date(processEndTime.getTime()
				- computationStart.getTime()).toString());
		writer.write(",");
		writer.write(Long.toString(server.fpSetManager.size()));
		writer.write(",");

		// write number of invocations
		for (Iterator<Integer> iterator = invocations.values().iterator(); iterator.hasNext();) {
			final Integer amountOfInvocations = (Integer) iterator.next();
			writer.write(Integer.toString(amountOfInvocations));
			writer.write(",");
		}
		
		// write "end tag"
		writer.write("\n");

		// close file
		writer.close();
	}

}
