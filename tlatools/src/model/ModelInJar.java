package model;

import java.io.IOException;
import java.io.InputStream;
import java.util.Enumeration;
import java.util.Properties;

public abstract class ModelInJar {
	public static final String PATH = "/model/";
	
	public static boolean hasModel() {
		return ModelInJar.class.getResource("/model/MC.tla") != null;
	}
	
	public static boolean loadProperties() {
		InputStream in = ModelInJar.class
				.getResourceAsStream("/model/generated.properties");
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
