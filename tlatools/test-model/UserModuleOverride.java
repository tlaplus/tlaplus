import tlc2.value.impl.BoolValue;
import tlc2.value.impl.Value;

// manually compiled with Java 1.6
public class UserModuleOverride {
    public static Value Get() {
        return new BoolValue(true);
    }
}
