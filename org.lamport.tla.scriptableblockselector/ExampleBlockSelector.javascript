function getBlocks(stateQueue, worker) {

	var size = stateQueue.size();
	var blockSize = getBlockSize(size);
	var states = stateQueue.sDequeue(blockSize);
	
	print(" BlockSize: " +  blockSize);
	print(" StateQueue size: " + size);
	print(" DeQueued: " + states.length + "\n");
	
	return states;
}

function getBlockSize(size) {
	var workerCount = tlcServer.getWorkerCount();
	print("WorkerCount: " + workerCount);
	var factor = 1.0 / workerCount;
	print(" Factor: " + factor);
	return size * factor;
}
