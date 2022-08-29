package tlc2.tool;

import java.util.HashSet;
import java.util.Set;

public class WorkerMonitor {

    private static final Set<ThreadListener> listeners = new HashSet<>();

    public static void addPerformanceResult(final Thread thread, final long runningTime) {
        for (final ThreadListener threadListener : listeners) {
            threadListener.terminated(thread, runningTime);
        }
    }

    public static void addThreadListener(final ThreadListener threadListener) {
        listeners.add(threadListener);
    }


    /**
     * A ThreadListener is notified of when the Worker thread terminates. The
     * notification includes the execution time of the thread.
     */
    public interface ThreadListener {

        void terminated(final Thread thread, final long runningTime);
    }
}
