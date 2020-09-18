package util;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Provides utility for iterating through all subsets of a set.
 */
public class SubsetHelper {
	
	/**
	 * Returns an iteration through all subsets of the given set.
	 * @param <T> Type of elements in the set.
	 * @param set The set of elements; must have fewer than 32 elements.
	 * @return An iteration through all subsets of the given set.
	 */
	public static <T> Iterable<Set<T>> getSubsetsOf(Set<T> set) {
		List<Set<T>> subsets = new ArrayList<Set<T>>();
		List<T> elements = new ArrayList<T>(set);
		for (int bitmask = 0; bitmask < (1 << elements.size()); bitmask++) {
			Set<T> subset = new HashSet<T>();
			for (int i = 0; i < elements.size(); i++) {
				if ((bitmask & (1 << i)) != 0) {
					subset.add(elements.get(i));
				}
			}
			
			subsets.add(subset);
		}
		
		return subsets;
	}
	
	/**
	 * Converts to subsets of args, splitting & flattening strings if they
	 * contain a space (for example "-workers 4" goes to ["-workers", "4"]
	 * @param argSubsets The arg subsets to split & flatten
	 * @return Subsets of args ready for passing to TLC.
	 */
	public static Iterable<String[]> toArgsSubsets(Iterable<Set<String>> argSubsets) {
		List<String[]> argsSubsets = new ArrayList<String[]>();
		for (Set<String> argSubset : argSubsets) {
			List<String> args = new ArrayList<String>();
			for (String arg : argSubset) {
				String[] split = arg.split(" ");
				args.addAll(Arrays.asList(split));
			}
			
			argsSubsets.add(args.toArray(new String[0]));
		}
		
		return argsSubsets;
	}
}
