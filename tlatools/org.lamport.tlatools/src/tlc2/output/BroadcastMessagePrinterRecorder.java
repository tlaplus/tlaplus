package tlc2.output;

import java.util.HashSet;
import java.util.Set;

/**
 * Pushes recorded events to recorders which subscribe to this broadcaster.
 */
public class BroadcastMessagePrinterRecorder implements IMessagePrinterRecorder {
	
	/**
	 * The list of recorders subscribed to this broadcaster.
	 */
	private Set<IMessagePrinterRecorder> subscribers = new HashSet<IMessagePrinterRecorder>();
	
	@Override
	public void record(int code, Object... objects) {
		for (IMessagePrinterRecorder recorder : this.subscribers)
		{
			recorder.record(code, objects);
		}
	}
	
	/**
	 * Subscribes a recorder to this broadcaster.
	 * This function is idempotent; recorders cannot be subscribed twice.
	 */
	public void subscribe(final IMessagePrinterRecorder recorder)
	{
		this.subscribers.add(recorder);
	}
	
	/**
	 * Unsubscribes a recorder from this broadcaster.
	 * @param recorder The recorder the unsubscribe.
	 */
	public void unsubscribe(final IMessagePrinterRecorder recorder)
	{
		this.subscribers.remove(recorder);
	}
}
