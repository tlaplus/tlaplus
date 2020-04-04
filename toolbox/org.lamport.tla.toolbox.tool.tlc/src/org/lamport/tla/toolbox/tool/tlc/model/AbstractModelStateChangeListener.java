package org.lamport.tla.toolbox.tool.tlc.model;

/**
 * An instance of this is notified when the running state of the model changes. There is no guarantee as to which thread
 * is being used to send the notification.
 * 
 * @see Model#add(AbstractModelStateChangeListener)
 * @see Model#remove(AbstractModelStateChangeListener)
 */
public abstract class AbstractModelStateChangeListener {
	public enum State {
		RUNNING, NOT_RUNNING, DELETED, REMOTE_RUNNING, REMOTE_NOT_RUNNING;
		
		public boolean in(final State ... states) {
			for (final State state : states) {
				if (state == this) {
					return true;
				}
			}
			return false;
		}
	}

	
	public static class ChangeEvent {
		private final State state;
		private final Model model;

		public ChangeEvent(final Model model, final State state) {
			this.model = model;
			this.state = state;
		}

		public State getState() {
			return state;
		}

		public Model getModel() {
			return model;
		}
	}

	
	/**
	 * @return true iff the listener should be unsubscribed from receiving future events after it handled the event.
	 */
	public abstract boolean handleChange(final ChangeEvent event);
}
