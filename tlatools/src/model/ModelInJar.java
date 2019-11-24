package model;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.Enumeration;
import java.util.Properties;

import util.TLAConstants;

public abstract class ModelInJar {
	public static final String PATH = "/model/";
	
	public static boolean hasModel() {
		return ModelInJar.class.getResource(PATH + TLAConstants.Files.MODEL_CHECK_TLA_FILE) != null;
	}
	
	public static boolean hasCfg() {
		return ModelInJar.class.getResource(PATH + TLAConstants.Files.MODEL_CHECK_CONFIG_FILE) != null;
	}

	public static File getCfg() {
		try {
			final InputStream source = ModelInJar.class.getResourceAsStream(PATH + TLAConstants.Files.MODEL_CHECK_CONFIG_FILE);
			Path target = Files.createTempFile(TLAConstants.Files.MODEL_CHECK_FILE_BASENAME, TLAConstants.Files.CONFIG_EXTENSION);
			Files.copy(source, target, StandardCopyOption.REPLACE_EXISTING);
			return target.toFile();
		} catch (IOException notExpectedToHappen) {
			return new File("");
		}
	}
	
	public static boolean loadProperties() {
		InputStream in = ModelInJar.class.getResourceAsStream(PATH + "generated.properties");
		if (in != null) {
			Properties prop = new Properties();
			try {
				prop.load(in);
				in.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
			Enumeration<Object> elements = prop.keys();
			while(elements.hasMoreElements()) {
				String key = (String) elements.nextElement();
				System.getProperties().setProperty(key, (String) prop.get(key));
			}
			return true;
		}
		return false;
	}
}
