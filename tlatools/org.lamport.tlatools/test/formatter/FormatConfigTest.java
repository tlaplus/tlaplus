package formatter;

import org.junit.Test;

import static org.junit.Assert.*;

/**
 * Unit tests for FormatConfig.
 */
public class FormatConfigTest {

    @Test
    public void testDefaultConstructor() {
        FormatConfig config = new FormatConfig();

        assertEquals(FormatConfig.DEFAULT_LINE_WIDTH, config.getLineWidth());
        assertEquals(FormatConfig.DEFAULT_INDENT_SIZE, config.getIndentSize());
        assertEquals(80, config.getLineWidth());
        assertEquals(2, config.getIndentSize());
    }

    @Test
    public void testParameterizedConstructor() {
        FormatConfig config = new FormatConfig(120, 2);

        assertEquals(120, config.getLineWidth());
        assertEquals(2, config.getIndentSize());
    }

    @Test
    public void testInvalidLineWidth() {
        try {
            new FormatConfig(0, 4);
            fail("Expected IllegalArgumentException");
        } catch (IllegalArgumentException e) {
            // expected
        }
        try {
            new FormatConfig(-1, 4);
            fail("Expected IllegalArgumentException");
        } catch (IllegalArgumentException e) {
            // expected
        }
        try {
            new FormatConfig(-100, 4);
            fail("Expected IllegalArgumentException");
        } catch (IllegalArgumentException e) {
            // expected
        }
    }

    @Test
    public void testInvalidIndentSize() {
        try {
            new FormatConfig(80, -1);
            fail("Expected IllegalArgumentException");
        } catch (IllegalArgumentException e) {
            // expected
        }
        try {
            new FormatConfig(80, -5);
            fail("Expected IllegalArgumentException");
        } catch (IllegalArgumentException e) {
            // expected
        }
    }

    @Test
    public void testValidEdgeCases() {
        // Minimum valid values — should not throw
        FormatConfig config = new FormatConfig(1, 0);
        assertEquals(1, config.getLineWidth());
        assertEquals(0, config.getIndentSize());
    }

    @Test
    public void testLargeValues() {
        FormatConfig config = new FormatConfig(1000, 16);
        assertEquals(1000, config.getLineWidth());
        assertEquals(16, config.getIndentSize());
    }

    @Test
    public void testEquals() {
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
    public void testEqualsWithSelf() {
        FormatConfig config = new FormatConfig(80, 4);
        assertEquals(config, config);
    }

    @Test
    public void testEqualsWithNull() {
        FormatConfig config = new FormatConfig(80, 4);
        assertNotEquals(null, config);
    }
    
    @Test
    public void testHashCode() {
        FormatConfig config1 = new FormatConfig(80, 4);
        FormatConfig config2 = new FormatConfig(80, 4);
        FormatConfig config3 = new FormatConfig(100, 4);

        assertEquals(config1.hashCode(), config2.hashCode());
        assertNotEquals(config1.hashCode(), config3.hashCode());
    }

    @Test
    public void testToString() {
        FormatConfig config = new FormatConfig(80, 4);
        String str = config.toString();

        assertTrue(str.contains("FormatConfig"));
        assertTrue(str.contains("lineWidth=80"));
        assertTrue(str.contains("indentSize=4"));
    }

    @Test
    public void testToStringWithDifferentValues() {
        FormatConfig config = new FormatConfig(120, 2);
        String str = config.toString();

        assertTrue(str.contains("lineWidth=120"));
        assertTrue(str.contains("indentSize=2"));
    }
}