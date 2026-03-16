package formatter;

import formatter.constructs.ListFormatStrategy;

import java.util.HashMap;
import java.util.Map;

/**
 * Configuration settings for the TLA+ formatter.
 * Contains formatting preferences like line width and indentation,
 * as well as construct-specific formatting settings.
 */
public final class FormatConfig {

    public static final int DEFAULT_LINE_WIDTH = 80;
    public static final int DEFAULT_INDENT_SIZE = 2;

    private final int lineWidth;
    private final int indentSize;
    private final Map<String, Object> constructSettings;

    public FormatConfig() {
        this(DEFAULT_LINE_WIDTH, DEFAULT_INDENT_SIZE);
    }

    public FormatConfig(int lineWidth, int indentSize) {
        if (lineWidth <= 0) {
            throw new IllegalArgumentException("Line width must be positive, got: " + lineWidth);
        }
        if (indentSize < 0) {
            throw new IllegalArgumentException("Indent size must be non-negative, got: " + indentSize);
        }

        this.lineWidth = lineWidth;
        this.indentSize = indentSize;
        this.constructSettings = new HashMap<>();
        loadDefaultSettings();
    }

    /**
     * Load default construct-specific settings.
     */
    private void loadDefaultSettings() {
        // EXTENDS-specific settings
        setConstructSetting("EXTENDS", "maxModulesPerLine", 8);
        setConstructSetting("EXTENDS", "breakStrategy", ListFormatStrategy.SMART_BREAK);

        // VARIABLES-specific settings  
        setConstructSetting("VARIABLES", "breakStrategy", ListFormatStrategy.SMART_BREAK);

        // OPERATOR-specific settings
        setConstructSetting("OPERATOR", "maxLineLength", Math.max(40, lineWidth - 4));
        setConstructSetting("OPERATOR", "breakStrategy", ListFormatStrategy.SMART_BREAK);

        // THEOREM-specific settings
        setConstructSetting("THEOREM", "breakStrategy", ListFormatStrategy.SMART_BREAK);
    }

    public int getLineWidth() {
        return lineWidth;
    }

    public int getIndentSize() {
        return indentSize;
    }

    /**
     * Get a construct-specific setting.
     *
     * @param constructName Name of the construct (e.g., "EXTENDS", "VARIABLES")
     * @param settingName   Name of the setting (e.g., "breakStrategy", "maxModulesPerLine")
     * @param defaultValue  Default value to return if setting is not found
     * @param <T>           Type of the setting value
     * @return The setting value or default value if not found
     */
    @SuppressWarnings("unchecked")
    public <T> T getConstructSetting(String constructName, String settingName, T defaultValue) {
        String key = constructName + "." + settingName;
        Object value = constructSettings.get(key);
        return value != null ? (T) value : defaultValue;
    }

    /**
     * Set a construct-specific setting.
     *
     * @param constructName Name of the construct
     * @param settingName   Name of the setting
     * @param value         Setting value
     */
    private void setConstructSetting(String constructName, String settingName, Object value) {
        String key = constructName + "." + settingName;
        constructSettings.put(key, value);
    }

    /**
     * Create a copy of this config with the same settings.
     *
     * @return A new FormatConfig instance with the same settings
     */
    public FormatConfig copy() {
        FormatConfig copy = new FormatConfig(lineWidth, indentSize);
        copy.constructSettings.clear();
        copy.constructSettings.putAll(this.constructSettings);
        return copy;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;

        FormatConfig that = (FormatConfig) obj;
        return lineWidth == that.lineWidth &&
                indentSize == that.indentSize &&
                constructSettings.equals(that.constructSettings);
    }

    @Override
    public int hashCode() {
        int result = 31 * lineWidth + indentSize;
        result = 31 * result + constructSettings.hashCode();
        return result;
    }

    @Override
    public String toString() {
        return "FormatConfig{" +
                "lineWidth=" + lineWidth +
                ", indentSize=" + indentSize +
                ", constructSettings=" + constructSettings.size() + " items" +
                "}";
    }
}