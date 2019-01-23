import tlc2.value.BoolValue;
import tlc2.value.IValue;
// manually compiled with Java 1.6
public class UserModuleOverride {
    public static IValue Get() {
        return new BoolValue(true);
    }
}
