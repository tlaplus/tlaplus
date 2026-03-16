package formatter;

import com.opencastsoftware.prettier4j.Doc;

import java.util.List;

/**
 * Utility methods for creating common Doc patterns.
 * These are truly generic utilities not specific to TLA+ constructs.
 */
public class DocUtils {

    private DocUtils() {
        // Utility class
    }

    /**
     * Creates a sequence of documents separated by lines
     */
    public static Doc lines(List<Doc> docs) {
        if (docs.isEmpty()) {
            return Doc.empty();
        }

        Doc result = docs.get(0);
        for (int i = 1; i < docs.size(); i++) {
            result = result.appendLine(docs.get(i));
        }
        return result;
    }

}