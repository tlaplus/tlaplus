package tlc2.input;

public class MCOutputMessage {
	private final int code;
	private final int type;
	private String body;
	
	MCOutputMessage(final int messageCode, final int messageType) {
		code = messageCode;
		type = messageType;
	}
	
	void setBody(final StringBuilder sb) {
		body = sb.toString();
	}

	/**
	 * @return e.g EC.TLC_VERSION
	 */
	public int getCode() {
		return code;
	}

	/**
	 * Returns the type of the message - a.k.a message class
	 * @return e.g MP.ERROR
	 */
	public int getType() {
		return type;
	}

	/**
	 * @return the body of the message - the content of the lines found between the
	 *         start and end message delimiters
	 */
	public String getBody() {
		return body;
	}
	
	@Override
	public String toString() {
		return "[" + code + "," + type + "]\n" + body;
	}
}
