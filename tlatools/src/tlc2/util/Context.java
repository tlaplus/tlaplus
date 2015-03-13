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

	private Context(SymbolNode name, Object value, Context next) {
		this.name = name;
		this.value = value;
		this.next = next;
	}

	public static Context branch(Context base) {
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
		Context cur;
		for (cur = this; cur.name != null; cur = cur.next) {
			if (var == cur.name) {
				return cur.value;
			}
		}
		if (cur == Empty) {
			return null;
		}
		return cur.next.lookup(var);
	}

	public final Object lookup(SymbolNode var, boolean cutoff) {
		Context cur;
		// Follow the linked list of Contexts (chain) starting at this context until a Context has been
		// reached whose name is identical to the searched for var. Stop if the Context
		// has no name which is the case for a branching Context (see branch(..)
		// above) and the Empty context (the base of all Context "chains").
		for (cur = this; cur.name != null; cur = cur.next) {
			if (var == cur.name) {
				return cur.value;
			}
		}
		// Following the Context chain has not produced a match and the end (the
		// Empty context) has been reached.
		if (cur == Empty || cutoff) {
			return null;
		}
		// Make the next Context the first node and start all over again.
		//
		// TODO How can this ever lead to a match if the previous for loop has
		// not found a match? Note it moves past the cur.name != null check if
		// the cur's name is null (which undoubtedly is the case due to the for
		// loop), but the next C. isn't. Logically it moves past a branching
		// Context.
		return cur.next.lookup(var);
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
