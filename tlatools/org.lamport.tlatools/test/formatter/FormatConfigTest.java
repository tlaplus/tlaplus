package formatter;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for FormatConfig.
 */
class FormatConfigTest {

    @Test
    void testDefaultConstructor() {
        FormatConfig config = new FormatConfig();

        assertEquals(FormatConfig.DEFAULT_LINE_WIDTH, config.getLineWidth());
        assertEquals(FormatConfig.DEFAULT_INDENT_SIZE, config.getIndentSize());
        assertEquals(80, config.getLineWidth());
        assertEquals(2, config.getIndentSize());
    }

    @Test
    void testParameterizedConstructor() {
        FormatConfig config = new FormatConfig(120, 2);

        assertEquals(120, config.getLineWidth());
        assertEquals(2, config.getIndentSize());
    }

    @Test
    void testInvalidLineWidth() {
        assertThrows(IllegalArgumentException.class, () -> new FormatConfig(0, 4));
        assertThrows(IllegalArgumentException.class, () -> new FormatConfig(-1, 4));
        assertThrows(IllegalArgumentException.class, () -> new FormatConfig(-100, 4));
    }

    @Test
    void testInvalidIndentSize() {
        assertThrows(IllegalArgumentException.class, () -> new FormatConfig(80, -1));
        assertThrows(IllegalArgumentException.class, () -> new FormatConfig(80, -5));
    }

    @Test
    void testValidEdgeCases() {
        // Minimum valid values
        assertDoesNotThrow(() -> new FormatConfig(1, 0));

        FormatConfig config = new FormatConfig(1, 0);
        assertEquals(1, config.getLineWidth());
        assertEquals(0, config.getIndentSize());
    }

    @Test
    void testLargeValues() {
        FormatConfig config = new FormatConfig(1000, 16);
        assertEquals(1000, config.getLineWidth());
        assertEquals(16, config.getIndentSize());
    }

    @Test
    void testEquals() {
        FormatConfig config1 = new FormatConfig(80, 4);
        FormatConfig config2 = new FormatConfig(80, 4);
        FormatConfig config3 = new FormatConfig(100, 4);
        FormatConfig config4 = new FormatConfig(80, 2);

        assertEquals(config1, config2);
        assertNotEquals(config1, config3);
        assertNotEquals(config1, config4);
        assertNotEquals(config3, config4);
    }

    @Test
    void testEqualsWithSelf() {
        FormatConfig config = new FormatConfig(80, 4);
        assertEquals(config, config);
    }

    @Test
    void testEqualsWithNull() {
        FormatConfig config = new FormatConfig(80, 4);
        assertNotEquals(null, config);
    }
    
    @Test
    void testHashCode() {
        FormatConfig config1 = new FormatConfig(80, 4);
        FormatConfig config2 = new FormatConfig(80, 4);
        FormatConfig config3 = new FormatConfig(100, 4);

        assertEquals(config1.hashCode(), config2.hashCode());
        assertNotEquals(config1.hashCode(), config3.hashCode());
    }

    @Test
    void testToString() {
        FormatConfig config = new FormatConfig(80, 4);
        String str = config.toString();

        assertTrue(str.contains("FormatConfig"));
        assertTrue(str.contains("lineWidth=80"));
        assertTrue(str.contains("indentSize=4"));
    }

    @Test
    void testToStringWithDifferentValues() {
        FormatConfig config = new FormatConfig(120, 2);
        String str = config.toString();

        assertTrue(str.contains("lineWidth=120"));
        assertTrue(str.contains("indentSize=2"));
    }
}