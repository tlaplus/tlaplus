package tlc2.output;

/**
 * Interface for recording messages that pass through {@link tlc2.output.MP}.
 */
public interface IMessagePrinterRecorder {
	
	/**
	 * Records a message.
	 * @param code Code identifying the message type.
	 * @param objects Data comprising the message.
	 */
	public void record(int code, Object... objects);
}
