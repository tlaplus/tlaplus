package formatter.constructs;

import com.opencastsoftware.prettier4j.Doc;
import formatter.FormatConfig;

import java.util.List;
import java.util.function.Function;

/**
 * Base class for construct formatters providing common formatting patterns.
 * This eliminates code duplication and provides consistent formatting strategies.
 *
 * @param <T> The type of items being formatted (e.g., String for module names)
 */
public abstract class BaseConstructFormatter<T> {

    protected final FormatConfig config;

    public BaseConstructFormatter(FormatConfig config) {
        this.config = config.copy();
    }

    /**
     * Format a list of items with a prefix using the specified strategy.
     *
     * @param items         List of items to format
     * @param prefix        Prefix string (e.g., "EXTENDS ", "VARIABLES ")
     * @param itemFormatter Function to convert items to Doc objects
     * @param strategy      Formatting strategy to use
     * @return Doc object for the entire construct
     */
    protected Doc formatList(List<T> items, Doc prefix,
                             Function<T, Doc> itemFormatter,
                             ListFormatStrategy strategy) {

        if (items.isEmpty()) {
            return Doc.empty();
        }

        if (items.size() == 1) {
            return prefix.appendSpace(itemFormatter.apply(items.get(0)));
        }

        switch (strategy) {
            case SINGLE_LINE:
                return formatAsSingleLine(items, prefix, itemFormatter);
            case SMART_BREAK:
                return formatWithSmartBreaks(items, prefix, itemFormatter);
            case ALWAYS_BREAK:
                return formatWithLineBreaks(items, prefix, itemFormatter);
            default:
                throw new IllegalArgumentException("Unknown strategy: " + strategy);
        }
    }

    /**
     * Format items as a single line with comma separation.
     */
    protected Doc formatAsSingleLine(List<T> items, Doc prefix, Function<T, Doc> itemFormatter) {
        Doc result = prefix.appendSpace(itemFormatter.apply(items.get(0)));

        for (int i = 1; i < items.size(); i++) {
            result = result.append(Doc.text(", ")).append(itemFormatter.apply(items.get(i)));
        }

        return result;
    }

    /**
     * Get the length of the last line of a rendered Doc.
     * When the prefix includes multi-line preComments, only the last line
     * (containing the keyword like "EXTENDS") should determine indentation.
     */
    private static int lastLineLength(Doc doc) {
        String rendered = doc.render();
        int lastNewline = rendered.lastIndexOf('\n');
        if (lastNewline < 0) {
            return rendered.length();
        }
        return rendered.length() - lastNewline - 1;
    }

    /**
     * Format items with smart line breaking based on line width.
     * Uses prettier4j's line-or-space mechanism for optimal breaking.
     */
    protected Doc formatWithSmartBreaks(List<T> items, Doc prefix, Function<T, Doc> itemFormatter) {
        Doc itemList = itemFormatter.apply(items.get(0));

        for (int i = 1; i < items.size(); i++) {
            itemList = itemList
                    .append(Doc.text(","))
                    .appendLineOrSpace(itemFormatter.apply(items.get(i)));
        }

        return
                prefix
                        .appendSpace(Doc.group(itemList).indent(lastLineLength(prefix) + 1));
    }

    /**
     * Format items with line breaks after each item.
     * Each item goes on its own line with proper indentation.
     */
    protected Doc formatWithLineBreaks(List<T> items, Doc prefix, Function<T, Doc> itemFormatter) {
        Doc result = prefix.appendSpace(itemFormatter.apply(items.get(0)));

        for (int i = 1; i < items.size(); i++) {
            result = result
                    .append(Doc.text(","))
                    .appendLine(itemFormatter.apply(items.get(i)).indent(lastLineLength(prefix)));
        }

        return result;
    }

    /**
     * Create a simple text formatter for string items.
     */
    protected static Function<String, Doc> stringFormatter() {
        return Doc::text;
    }

}