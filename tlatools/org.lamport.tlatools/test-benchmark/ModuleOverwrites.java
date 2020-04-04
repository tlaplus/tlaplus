
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import tlc2.value.IValue;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;

public class ModuleOverwrites {

	public static IValue noDupesOverwrite(final FcnRcdValue frv, final IntValue exclude) {
		// LET sub == SelectSeq(t, LAMBDA e: e # emp)
		// IN ...
		final List<IValue> filtered = Arrays.asList(frv.values).stream().filter(e -> e != exclude).collect(Collectors.toList());
		
		// IF Len(sub) < 2 THEN TRUE ...
		if (filtered.size() < 2) {
			return BoolValue.ValTrue;
		}
		
		// ~n^2:
		// \A i \in 1..(Len(sub) - 1):
        //    \A j \in (i+1)..Len(sub):
        //       abs(sub[i]) # abs(sub[j])
		for (int i = 0; i < filtered.size() - 1; i++) {
			for (int j = i + 1; j < filtered.size(); j++) {
				if (filtered.get(i) == filtered.get(j)) {
					return BoolValue.ValFalse;
				}
			}			
		}
		return BoolValue.ValTrue;
	}
}
