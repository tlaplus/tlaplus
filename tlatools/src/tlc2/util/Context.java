// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:30:03 PST by lamport
//      modified on Fri Feb 16 14:26:21 PST 2001 by yuanyu

package tlc2.util;

import tla2sany.semantic.SymbolNode;

public final class Context {
	/**
	 * A link list of name and value pairs. When adding <name, value> to the
	 * context, we assume that name != null.
	 */

	private final SymbolNode name;
	private final Object value;
	private final Context next;

	public final static Context Empty = new Context(null, null, null);
	public final static Context BaseBranch = new Context(null, null, Empty);
	
	private Context(SymbolNode name, Object value, final Context next) {
		this.name = name;
		this.value = value;
		this.next = next;
	}

	public static Context branch(Context base) {
		if (base == Empty) {
			// Avoid new instance if the next context in the chain is the Empty
			// one (Branch -> Empty).
			return BaseBranch;
		}
		return new Context(null, null, base);
	}

	public final Context cons(SymbolNode name, Object value) {
		return new Context(name, value, this);
	}

	/**
	 * This method returns the value for the name var. It returns null if this
	 * context does not contain var.
	 */
	public final Object lookup(SymbolNode var) {
		Context cur = this;
		// Follow the linked list of Contexts (chain) starting at this context
		// until a Context has been reached whose name (SymbolNode) is identical
		// to the searched for var. Stop if the Empty context (the base of all
		// Context "chains") has been reached.
		while (cur != Empty) {
			// Check identity of value if not empty or branching
			if (cur.name != null) {
				if (var == cur.name) {
					return cur.value;
				}
			}
			cur = cur.next;
		}
		return null; // On Empty Context (end of chain), return null value
	}

	/**
	 * @param var
	 *            The SymbolNode to lookup
	 * @param cutoff
	 *            Iff true, lookup stops at a branching Context. Follows
	 *            complete chain if false.
	 * @return value associated with the {@link SymbolNode} var or null if var
	 *         could not be found in the search along the Context "chain"
	 */
	public final Object lookup(SymbolNode var, boolean cutoff) {
		Context cur = this;
		// Follow the linked list of Contexts (chain) starting at this context until a Context has been
		// reached whose name (SymbolNode) is identical to the searched for var. Stop if the Context's
		// name is null, which is the case for a branching Context (see branch(..)
		// above) or the Empty context (the base of all Context "chains") has been reached.
		while (cur != Empty) {
			// Check identity of value if not empty or branching
			if (cur.name != null) {
				if (var == cur.name) {
					return cur.value;
				}
			} else if (cutoff == true) {
				// reached a branching context (value is null)
				assert cur.value == null;
				return null;
			}
			cur = cur.next;
		}
		return null; // On Empty Context (end of chain), return null value
	}

	public final StringBuffer toString(StringBuffer sb) {
		if (this.name == null) {
			if (this == Empty) {
				return sb;
			}
			return this.next.toString(sb);
		}
		sb.append(this.name.getName());
		sb.append("->");
		sb.append(this.value);
		Context cur;
		for (cur = this.next; cur.name != null; cur = cur.next) {
			sb.append(", ");
			sb.append(cur.name.getName());
			sb.append("->");
			sb.append(cur.value);
		}
		cur.toString(sb);
		return sb;
	}

	public final String toString() {
		StringBuffer sb = new StringBuffer("[");
		sb = this.toString(sb);
		sb.append("]");
		return sb.toString();
	}
}
