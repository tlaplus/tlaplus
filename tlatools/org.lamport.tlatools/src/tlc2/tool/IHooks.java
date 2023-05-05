package tlc2.tool;

public interface IHooks {

    default void preInit() {}

    default void preProcess() {}

    default void postProcess() {}
    
}
