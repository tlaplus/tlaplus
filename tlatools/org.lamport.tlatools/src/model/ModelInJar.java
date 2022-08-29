package model;

import util.TLAConstants;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.Enumeration;
import java.util.Objects;
import java.util.Properties;

public abstract class ModelInJar {
    public static final String PATH = "/model/";

    public static boolean hasModel() {
        return ModelInJar.class.getResource(PATH + TLAConstants.Files.MODEL_CHECK_TLA_FILE) != null;
    }

    public static boolean hasCfg() {
        return ModelInJar.class.getResource(PATH + TLAConstants.Files.MODEL_CHECK_CONFIG_FILE) != null;
    }

    public static File getCfg() {
        try (final InputStream source = ModelInJar.class.getResourceAsStream(PATH + TLAConstants.Files.MODEL_CHECK_CONFIG_FILE)) {
            final Path target = Files.createTempFile(TLAConstants.Files.MODEL_CHECK_FILE_BASENAME, TLAConstants.Files.CONFIG_EXTENSION);
            Files.copy(Objects.requireNonNull(source), target, StandardCopyOption.REPLACE_EXISTING);
            return target.toFile();
        } catch (final IOException notExpectedToHappen) {
            return new File("");
        }
    }

    public static boolean loadProperties() {
        final InputStream in = ModelInJar.class.getResourceAsStream(PATH + "generated.properties");
        if (in != null) {
            final Properties prop = new Properties();
            try {
                prop.load(in);
                in.close();
            } catch (final IOException e) {
                e.printStackTrace();
            }
            final Enumeration<Object> elements = prop.keys();
            while (elements.hasMoreElements()) {
                final String key = (String) elements.nextElement();
                System.getProperties().setProperty(key, (String) prop.get(key));
            }
            return true;
        }
        return false;
    }
}
