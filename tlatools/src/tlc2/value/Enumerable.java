// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:20:54 PST by lamport
//      modified on Thu Mar 11 21:25:20 PST 1999 by yuanyu

package tlc2.value;

import java.util.HashMap;
import java.util.Map;
import java.util.Properties;
import java.util.function.BiConsumer;

import tlc2.TLCGlobals;
import util.UniqueString;

public interface Enumerable {

  public int size();
  public boolean member(Value elem);
  public ValueEnumeration elements();
  public ValueEnumeration elements(final int k);
  /**
   * Returns a {@link ValueEnumeration} which returns (fraction * n) 
   * {@link Value}s of all {@link Value}s returned by 
   * {@link Enumerable#elements()}. In other words, it returns
   * a randomly chosen subset of all {@link Value} members of
   * this {@link Enumerable}.
   */
  public ValueEnumeration elements(final double fraction);
  public EnumerableValue getRandomSubset(final int k);
  public Value isSubsetEq(Value other);

	/**
	 * @see TLCGlobals#enumFraction, Enumerable#elements() and Enumerable#elements(double)
	 */
	public static ValueEnumeration elements(final UniqueString variable, final Enumerable enumerable) {
		if (EnumFractionConfig.hasFractionFor(variable)) {
			return enumerable.elements(EnumFractionConfig.getFractionFor(variable));
		} else {
			return enumerable.elements();
		}
	}
	
	static class EnumFractionConfig {

		private static final String enumFractionProperty = TLCGlobals.class.getName() + ".enumFraction";

		private static final Map<UniqueString, Double> enumFractionToVar = getEnumFractions();
		
		private static final double defaultEnumFraction = Double
				.valueOf(System.getProperty(enumFractionProperty, "-1d"));

		static Map<UniqueString, Double> getEnumFractions() {
			final Map<UniqueString, Double> enumFraction = new HashMap<UniqueString, Double>();
			final Properties properties = System.getProperties();
			properties.forEach(new BiConsumer<Object, Object>() {
				@Override
				public void accept(Object u, Object v) {
					if (u instanceof String && v instanceof String) {
						final String key = (String) u;
						if (key.startsWith(enumFractionProperty + ".")) {
							final String var = key.substring(enumFractionProperty.length() + 1);
							enumFraction.put(UniqueString.uniqueStringOf(var), Double.valueOf((String) v));
						}
					}
				}
			});
			return enumFraction;
		}
		
		static boolean hasFractionFor(final UniqueString variable) {
			return enumFractionToVar.containsKey(variable) || defaultEnumFraction != -1d;
		}

		static double getFractionFor(final UniqueString var) {
			return enumFractionToVar.getOrDefault(var, defaultEnumFraction);
		}
		
		public static void setFractionFor(final String var, final double fraction) {
			enumFractionToVar.put(UniqueString.uniqueStringOf(var), fraction);
		}
	}
}

