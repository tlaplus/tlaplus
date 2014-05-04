package model;

public abstract class ModelInJar {
	public static final String PATH = "/model/";
	
	public static boolean hasModel() {
		return ModelInJar.class.getResource("/model/MC.tla") != null;
	}
}
