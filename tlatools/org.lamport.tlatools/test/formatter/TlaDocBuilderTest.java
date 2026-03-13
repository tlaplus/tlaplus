package formatter;

import com.opencastsoftware.prettier4j.Doc;
import formatter.exceptions.SanyFrontendException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for TlaDocBuilder.
 * These tests use real TLA+ specs to test the builder functionality.
 */
class TlaDocBuilderTest {

    private TlaDocBuilder builder;
    private FormatConfig config;

    @BeforeEach
    void setUp() {
        config = new FormatConfig(80, 4);
        builder = new TlaDocBuilder(config);
    }

    @Test
    void testBuildWithNullNode() {
        Doc result = builder.build(null);
        
        assertEquals(Doc.empty(), result);
        assertEquals("", result.render(80));
    }

    @Test
    void testBuilderWithSimpleModule() throws IOException, SanyFrontendException {
        String spec = "---- MODULE SimpleTest ----\n" +
                     "VARIABLE x\n" +
                     "====\n";

        TLAPlusFormatter formatter = new TLAPlusFormatter(spec, config);
        String output = formatter.getOutput();
        
        assertTrue(output.contains("---- MODULE SimpleTest ----"));
        assertTrue(output.contains("VARIABLE x"));
        assertTrue(output.contains("===="));
    }

    @Test
    void testBuilderWithMultipleVariables() throws IOException, SanyFrontendException {
        String spec = "---- MODULE MultiVar ----\n" +
                     "VARIABLES x, y, z\n" +
                     "====\n";

        TLAPlusFormatter formatter = new TLAPlusFormatter(spec, config);
        String output = formatter.getOutput();
        
        assertTrue(output.contains("VARIABLES"));
        assertTrue(output.contains("x"));
        assertTrue(output.contains("y"));
        assertTrue(output.contains("z"));
    }

    @Test
    void testBuilderWithOperatorDefinition() throws IOException, SanyFrontendException {
        String spec = "---- MODULE OpTest ----\n" +
                     "EXTENDS Naturals\n" +
                     "VARIABLE x\n" +
                     "Inc == x + 1\n" +
                     "====\n";

        TLAPlusFormatter formatter = new TLAPlusFormatter(spec, config);
        String output = formatter.getOutput();
        
        assertTrue(output.contains("Inc =="));
        assertTrue(output.contains("x + 1"));
    }

    @Test
    void testBuilderWithExtends() throws IOException, SanyFrontendException {
        String spec = "---- MODULE ExtendsTest ----\n" +
                     "EXTENDS Naturals, TLC\n" +
                     "VARIABLE counter\n" +
                     "====\n";

        TLAPlusFormatter formatter = new TLAPlusFormatter(spec, config);
        String output = formatter.getOutput();
        
        assertTrue(output.contains("EXTENDS"));
        assertTrue(output.contains("Naturals"));
        assertTrue(output.contains("TLC"));
    }

    @Test
    void testBuilderConfigurationUsage() {
        FormatConfig customConfig = new FormatConfig(40, 2);
        TlaDocBuilder customBuilder = new TlaDocBuilder(customConfig);
        
        // Just verify builder can be created with different configs
        assertNotNull(customBuilder);
    }
}