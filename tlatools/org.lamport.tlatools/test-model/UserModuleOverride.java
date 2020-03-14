import tlc2.value.impl.BoolValue;
import tlc2.value.impl.Value;

// manually compiled with Java 1.8
public class UserModuleOverride {
    public static Value Get() {
        return BoolValue.ValTrue;
    }

    public static Value Get2(Value v1) {
        return BoolValue.ValFalse;
    }


    public static Value Get3() {
        return BoolValue.ValFalse;
    }
}
