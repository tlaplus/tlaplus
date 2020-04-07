// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:30:03 PST by lamport
//      modified on Fri Feb 16 14:26:21 PST 2001 by yuanyu

package tlc2.util;

import java.util.function.Function;

import tla2sany.semantic.SymbolNode;

// Context is used two times:
// 1) To determine the level boundedness of the expression appearing in the spec
//    (see Tool#getLevelBounds*). This is done once as part of parsing.
// 2) To store the variable/name binding at each scope during state exploration.
//    The hierarchy of levels/scopes is represented as a chain of context instances 
//    (link-list or associative list). The Empty context is the outer most scope 
//    (first level).
// 1) is not relevant performance-wise, but 2) has - provided non-trivial level -
// a significant performance impact because of excessive lookups. What makes
// optimizations difficult, is the fact that the context chain is recreated each
// time a state is generated, as part of the next state relation. An optimization
// thus has to ensure that it doesn't trade fast - ideally constant - lookups for
// an equally expensive creation complexity.
//
// The contrived spec at the bottom exhibits this problem. Increasing the level,
// the number of lookups go through the roof.
public final class Context {
	/**
	 * A link list of name and value pairs. When adding <name, value> to the
	 * context, we assume that name != null.
	 */

	private final SymbolNode name;
	private final Object value;
	private final Context next;

	public final static Context Empty = new Context(null, null, null);
	
	private final static Context BaseBranch = new Context(null, null, Empty);
	
	private Context(SymbolNode name, Object value, final Context next) {
		this.name = name;
		this.value = value;
		this.next = next;
	}

	// This method is only called within the context of the ENABLED (temporal)
	// operator. A branching context is specially handled during lookup below
	// if cutoff is true.
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
			// Check identity of value if match (this is slightly simpler
			// compared to the second lookup method. Here we can ignore the else
			// if branch since there is no cutoff.
			if (var == cur.name) {
				return cur.value;
			}
			cur = cur.next;
		}
		return null; // On Empty Context (end of chain), return null value
	}
	
	public final Object lookup(final Function<SymbolNode, Boolean> f) {
		Context cur = this;
		while (cur != Empty) {
			if (f.apply(cur.name)) {
				return cur.value;
			}
			cur = cur.next;
		}
		return null;
	}

	public final SymbolNode lookupName(final Function<SymbolNode, Boolean> f) {
		Context cur = this;
		while (cur != Empty) {
			if (f.apply(cur.name)) {
				return cur.name;
			}
			cur = cur.next;
		}
		return null;
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
	public final Object lookup(final SymbolNode var, final boolean cutoff) {
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
/*
----------------------------- MODULE Scoping -----------------------------
EXTENDS Naturals
CONSTANT Limit
VARIABLE var

A(a) == TRUE
B(b) == A(b)
C(c) == B(c)
D(d) == C(d)
E(e) == D(e)
F(f) == E(f)
G(g) == F(g)
H(h) == G(h)
I(i) == H(i)
J(j) == I(j)
K(k) == J(k)
L(l) == K(l)
M(m) == L(m)
N(n) == M(n) 
O(o) == N(o)
P(p) == O(p)
Q(q) == P(q)
R(r) == Q(r) 
S(s) == R(s)
T(t) == S(t)
U(u) == T(u)
V(v) == U(v)
W(w) == V(w)
X(x) == W(x)
Y(y) == X(y)
Z(z) == U(z)

Next == /\ var' = var + 1
        /\ var < 1
        /\ Z(1)

Spec == var=0 /\ [][Next]_<<var>>
=============================================================================
*/
