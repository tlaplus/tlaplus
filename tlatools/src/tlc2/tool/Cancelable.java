package tlc2.tool;

/**
 * The interface for a cancelable.
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface Cancelable
{
    /**
     * Sets the flag to cancel the instance
     * @param flag cancellation flag
     */
    public void setCancelFlag(boolean flag);
}
