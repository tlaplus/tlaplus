package tla2unicode;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import util.UniqueString;

public final class Alternates {
	private final Set<String> alts;
	
	public Alternates(String... alts) {
		this.alts = new HashSet<>(Arrays.asList(alts));
		for (String s : alts) {
			String u = Unicode.a2u(s);
			if (u != null)
				this.alts.add(u);
		}
	}
	
	public boolean matches(String x) {
		return alts.contains(x);
	}
	
	public boolean matches(UniqueString x) {
		return matches(x.toString());
	}
}
