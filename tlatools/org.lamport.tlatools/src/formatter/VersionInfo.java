package formatter;

import java.io.IOException;
import java.io.InputStream;
import java.util.Properties;

public final class VersionInfo {
    private static final String VERSION;
    private static final String COMMIT_ID;

    static {
        Properties props = new Properties();
        try (InputStream is = VersionInfo.class.getClassLoader().getResourceAsStream("version.properties")) {
            if (is != null) {
                props.load(is);
            }
        } catch (IOException e) {
            // ignore
        }
        VERSION = props.getProperty("version", "unknown");
        COMMIT_ID = props.getProperty("git.commit", "unknown");
    }

    private VersionInfo() {
    }

    public static String getFullVersion() {
        return VERSION + " (commit " + COMMIT_ID + ")";
    }
}
