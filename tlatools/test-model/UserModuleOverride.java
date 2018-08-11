import tlc2.value.BoolValue;
import tlc2.value.Value;
// manually compiled with Java 1.6
public class UserModuleOverride {
    public static Value Get() {
        return new BoolValue(true);
    }
}
