// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:50 PST by lamport
//      modified on Thu Sep 21 22:20:35 PDT 2000 by yuanyu

package tlc2.tool.liveness;

import tlc2.output.EC;
import tlc2.util.Vect;
import util.Assert;

/**
 * See Section 5.5 "Particle Tableaux" in Temporal Verification of Reactive
 * Systems *Safety* by Zohar Manna and Amir Pnueli.
 * <p>
 * A {@link TBPar} means Tableau Particle. A particle is an incomplete atom
 * because it only adheres to a relaxed version of atoms. Due to its
 * incompleteness, it results in a more efficient tableau since its size is less
 * than that with complete atoms. However, it does not loose generality.
 * <p>
 * The formulas are in positive form, meaning negation
 * is only applied to state formulas. The state formulas are not keep in
 * {@link TBPar}, but in {@link TBGraphNode#statePreds} instead. There is also where the
 * successors of the particle are held.
 * <p>
 * TLA+ supports only future formulas and no past temporal operators (compare
 * with p. 43 fig. 0.15), thus it uses the PART-TAB algorithm (p. 456) for the
 * tableau construction.
 */
@SuppressWarnings("serial")
public class TBPar extends Vect<LiveExprNode> {

	TBPar() {
		super(0);
	}

	public TBPar(int i) {
		super(i);
	}

	public final LiveExprNode exprAt(int i) {
		return (LiveExprNode) elementAt(i);
	}

	/* This method returns true iff this particle is equal to another particle */
	public final boolean equals(TBPar par) {
		return (this.contains(par) && par.contains(this));
	}

	/**
	 * This method tests whether or not an expression is in a list of
	 * expressions.
	 */
	final boolean member(LiveExprNode e) {
		for (int i = 0; i < this.size(); i++) {
			if (e.equals(this.exprAt(i))) {
				return true;
			}
		}
		return false;
	}

	/**
	 * This method tests whether a particle par is a subset of this particle.
	 */
	private final boolean contains(TBPar par) {
		for (int i = 0; i < par.size(); i++) {
			if (!this.member(par.exprAt(i))) {
				return false;
			}
		}
		return true;
	}

	/* This method returns the unions of two particles. */
	@SuppressWarnings("unused")
	private final TBPar union(TBPar par) {
		TBPar res = new TBPar(this.size() + par.size());
		for (int i = 0; i < this.size(); i++) {
			if (!par.member(this.exprAt(i))) {
				res.addElement(this.exprAt(i));
			}
		}
		for (int i = 0; i < par.size(); i++) {
			res.addElement(par.exprAt(i));
		}
		return res;
	}

	/* This method appends an expression to the tail of Par. */
	private final TBPar append(LiveExprNode ln) {
		TBPar res = new TBPar(this.size() + 1);
		for (int i = 0; i < this.size(); i++) {
			res.addElement(this.exprAt(i));
		}
		res.addElement(ln);
		return res;
	}

	/* This method appends two expressions to the tail of Par. */
	private final TBPar append(LiveExprNode ln1, LiveExprNode ln2) {
		TBPar res = new TBPar(this.size() + 2);
		for (int i = 0; i < this.size(); i++) {
			res.addElement(this.exprAt(i));
		}
		res.addElement(ln1);
		res.addElement(ln2);
		return res;
	}

	/**
	 * The method particleClosure, given a list of terms (initially just a
	 * single term), returns a list of all particles containing those terms.
	 * It's a recursive tree search.
	 */
	public TBParVec particleClosure() {
		TBPar positive_closure = this.positiveClosure();
		Vect<TBTriple> alphas = positive_closure.alphaTriples();
		Vect<TBTriple> betas = positive_closure.betaTriples();
		return particleClosure(this, alphas, betas);
	}

	private TBParVec particleClosure(final TBPar terms, final Vect<TBTriple> alphas, final Vect<TBTriple> betas) {
		// if terms is not locally consistent, then terminate .
		if (!terms.isLocallyConsistent()) {
			// TODO: The calling code does not seem to terminate if the term is
			// inconsistent.
			return new TBParVec(0);
		}
		// if terms is not alpha-closed, then close it.
		// first, try alpha expansion. See MP page 403 
		// figure 5.1. for alpha expansion rules.
		TBPar terms1 = terms;
		for (int i = 0; i < terms1.size(); i++) {
			LiveExprNode ln = terms1.exprAt(i);
			LiveExprNode kappa1 = null, kappa2 = null;
			if (ln instanceof LNAll) {
				// Alpha-Expansion: []p expands to p, ()[]p
				kappa1 = ((LNAll) ln).getBody();
				kappa2 = new LNNext(ln);
			} else if (ln instanceof LNConj) {
				// Alpha-Expansion: p /\ q expands to p, q
				kappa1 = ((LNConj) ln).getBody(0);
				kappa2 = ((LNConj) ln).getBody(1);
			}
			if (kappa1 != null) {
				if (terms1.member(kappa1)) {
					if (!terms1.member(kappa2)) {
						terms1 = terms1.append(kappa2);
					}
				} else if (terms1.member(kappa2)) {
					terms1 = terms1.append(kappa1);
				} else {
					terms1 = terms1.append(kappa1, kappa2);
				}
			}
		}
		// second, try alpha^-1 expansion (inverse expansion)
		boolean done;
		do {
			done = true;
			for (int i = 0; i < alphas.size(); i++) {
				TBTriple alpha = (TBTriple) alphas.elementAt(i);
				if (terms1.member(alpha.getB()) && terms1.member(alpha.getC()) && !terms1.member(alpha.getA())) {
					terms1.addElement(alpha.getA());
					done = false;
				}
			}
		} while (!done);
		// finally, recurse only when locally consistent
		if ((terms1.size() > terms.size()) && (!terms1.isLocallyConsistent())) {
			return new TBParVec(0);
		}
		return particleClosureBeta(terms1, alphas, betas);
	}

	private TBParVec particleClosureBeta(final TBPar terms, final Vect<TBTriple> alphas, final Vect<TBTriple> betas) {
		// try a beta expansion. See MP page 403 
		// figure 5.1. for beta expansion rules.
		for (int i = 0; i < terms.size(); i++) {
			LiveExprNode ln = terms.exprAt(i);
			LiveExprNode kappa1 = null, kappa2 = null;
			if (ln instanceof LNEven) {
				// Beta-Expansion: <>p expands to p, ()<>p
				kappa1 = ((LNEven) ln).getBody();
				kappa2 = new LNNext(ln);
			} else if (ln instanceof LNDisj) {
				// Beta-Expansion: p \/ expands to p, q
				kappa1 = ((LNDisj) ln).getBody(0);
				kappa2 = ((LNDisj) ln).getBody(1);
			}
			if ((kappa1 != null) && !terms.member(kappa1) && !terms.member(kappa2)) {
				TBParVec ps1 = particleClosure(terms.append(kappa1), alphas, betas);
				TBParVec ps2 = particleClosure(terms.append(kappa2), alphas, betas);
				return ps1.union(ps2);
			}
		}
		// try a beta^-1 expansion
		for (int i = 0; i < betas.size(); i++) {
			TBTriple beta = (TBTriple) betas.elementAt(i);
			if ((terms.member(beta.getB()) || terms.member(beta.getC())) && !terms.member(beta.getA())) {
				return particleClosure(terms.append(beta.getA()), alphas, betas);
			}
		}
		// if there are not any more expansions to do, return the terms
		// we've got as the only particle in a list of particles.
		TBParVec res = new TBParVec(1);
		res.addElement(terms);
		return res;
	}

	/**
	 * The methods alphaTriples and betaTriples, given a positive closure,
	 * figure out the alpha and beta triples. The way the algorithm works, by
	 * the time we extract triples, it should already have been positively
	 * closed. All junctions must have been binarified at this stage by
	 * makeBinary, otherwise it may give the wrong answer and crash.
	 */
	private final Vect<TBTriple> alphaTriples() {
		Vect<TBTriple> ts = new Vect<>();
		for (int i = 0; i < this.size(); i++) {
			LiveExprNode ln = this.exprAt(i);
			if (ln instanceof LNAll) {
				ts.addElement(new TBTriple(ln, ((LNAll) ln).getBody(), new LNNext(ln)));
			} else if (ln instanceof LNConj) {
				LNConj lnc = (LNConj) ln;
				ts.addElement(new TBTriple(lnc, lnc.getBody(0), lnc.getBody(1)));
			}
		}
		return ts;
	}

	private final Vect<TBTriple> betaTriples() {
		Vect<TBTriple> ts = new Vect<>();
		for (int i = 0; i < this.size(); i++) {
			LiveExprNode ln = this.exprAt(i);
			if (ln instanceof LNEven) {
				ts.addElement(new TBTriple(ln, ((LNEven) ln).getBody(), new LNNext(ln)));
			} else if (ln instanceof LNDisj) {
				LNDisj lnd = (LNDisj) ln;
				ts.addElement(new TBTriple(lnd, lnd.getBody(0), lnd.getBody(1)));
			}
		}
		return ts;
	}

	/**
	 * The method isLocallyConsistent determines whether a list of state predicates
	 * is locally consistent.
	 * <p>
	 * Manna &Pnueli (p.444): A set of temporal formulae B is (locally) consistent
	 * if it does *not* contain a formulae and its negation, and the conjunction of
	 * all state formulae state(B) is satisfiable.
	 * <p>
	 * Check Manna & Pnueli book page 444ff and 453 specifically for the theory of
	 * locally consistent.
	 */
	private final boolean isLocallyConsistent() {
		// Pre-conditions per Manna & Pnueli and the calling code:
		//assert !this.containsActions (no LNAction instances)
		//assert this.isPositiveForm()
		// First put the elements into positive or negative bin
		TBPar pos = new TBPar(this.size());
		TBPar neg = new TBPar(this.size());
		for (int i = 0; i < this.size(); i++) {
			LiveExprNode ln = this.exprAt(i);
			// Implementation not aligned with TBGraphNode::new because here we split into
			// pos and neg bins.
			if (ln instanceof LNState || ln instanceof LNBool) {
				pos.addElement(ln);
			} else if (ln instanceof LNNeg) {
				LiveExprNode body = ((LNNeg) ln).getBody();
				// Because tf has been brought into positive form by the nested pushNeg of
				// toDNF, the sub-terms of LNNeg can only be LNState and LNBool, but not
				// arbitrary terms such as ~[]p or []<>p.
				//assert body instanceof LNState || body instanceof LNBool;
				if (body instanceof LNState || body instanceof LNBool) {
					neg.addElement(body);
				}
			}
		}
		// If any positive is in the negative bin, that's a clash.
		for (int i = 0; i < pos.size(); i++) {
			if (neg.member(pos.exprAt(i))) {
				// This is reachable if two LNState instances have the same tag
				// (LNState#tetTag), which are set in Liveness before the liveness constraints
				// and properties are brought into disjunct normal form.  Thus, for two (or more)
				// LNState to have the same tag, LiveExprNode.toDNF() would have to duplicate
				// the LNState instance.
				// For two LNBool to be equal, their boolean values have to be the same.
				return false;
			}
		}
		return true;
	}

	/**
	 * This method, given a list of terms, returns all those terms and subterms that
	 * are positive (i.e. whose major operator is not a negation). For LNAll and
	 * LNEven, it also adds LNNext particles.
	 * <p>
	 * There can not be LNActs in the expression.
	 */
	private final TBPar positiveClosure() {
		// tps is the queue of terms to be processed.
		TBPar tps = new TBPar(this.size() * 2);
		for (int i = 0; i < this.size(); i++) {
			tps.addElement(this.elementAt(i));
		}
		TBPar result = new TBPar(this.size() * 2);
		while (tps.size() > 0) {
			LiveExprNode ln = tps.exprAt(tps.size() - 1);
			tps.removeLastElement();
			if (ln instanceof LNNeg) {
				// LNNeg is obviously not positive, but its subterms might.
				tps.addElement(((LNNeg) ln).getBody());
			} else if (ln instanceof LNNext) {
				result.addElement(ln);
				tps.addElement(((LNNext) ln).getBody());
			} else if (ln instanceof LNEven) {
				result.addElement(ln);
				// See page 452, Closure and Particles, 3. item
				result.addElement(new LNNext(ln));
				tps.addElement(((LNEven) ln).getBody());
			} else if (ln instanceof LNAll) {
				result.addElement(ln);
				// See page 452, Closure and Particles, 3. item
				result.addElement(new LNNext(ln));
				tps.addElement(((LNAll) ln).getBody());
			} else if (ln instanceof LNConj) {
				LNConj lnc = (LNConj) ln;
				for (int i = 0; i < lnc.getCount(); i++) {
					tps.addElement(lnc.getBody(i));
				}
				result.addElement(ln);
			} else if (ln instanceof LNDisj) {
				LNDisj lnd = (LNDisj) ln;
				for (int i = 0; i < lnd.getCount(); i++) {
					tps.addElement(lnd.getBody(i));
				}
				result.addElement(ln);
			} else if (ln instanceof LNState) {
				result.addElement(ln);
			} else if (ln instanceof LNBool) {
				result.addElement(ln);
			} else {
				Assert.fail(EC.TLC_LIVE_ENCOUNTERED_ACTIONS);
			}
		}
		return result;
	}

	/**
	 * This method returns a list of implied successors of a given particle.
	 * PART-TAB particle tableau construction on page 456 in Manna & Pnueli.
	 */
	final TBPar impliedSuccessors() {
		TBPar successors = new TBPar(this.size());
		for (int i = 0; i < this.size(); i++) {
			LiveExprNode ln = this.exprAt(i);
			if (ln instanceof LNNext) {
				successors.addElement(((LNNext) ln).getBody());
			}
		}
		return successors;
	}

	/**
	 * This methods returns true iff this particle (TBPar) fulfills the given
	 * promise.
	 * <p>
	 * A particle/atom A is said to fulfill formula &#966; which promises r if either:
	 * <ul>
	 * <li>&#966; \notin A</li>
	 * <li>r \in A</li>
	 * </ul>
	 */
	final boolean isFulfilling(LNEven promise) {
		return !this.member(promise) || this.member(promise.getBody());
	}

	public final void toString(StringBuffer sb, String padding) {
		sb.append("{");
		String padding1 = padding + " ";
		if (this.size() != 0) {
			((LiveExprNode) this.elementAt(0)).toString(sb, padding1);
		}
		for (int i = 1; i < this.size(); i++) {
			sb.append(",\n");
			sb.append(padding1);
			((LiveExprNode) this.elementAt(i)).toString(sb, padding1);
		}
		sb.append("}");
	}

	public final String toString() {
		StringBuffer sb = new StringBuffer();
		this.toString(sb, "");
		return sb.toString();
	}

	public String toDotViz() {
		final StringBuffer sb = new StringBuffer();
		sb.append("{");
		if (this.size() != 0) {
			LiveExprNode liveExprNode = (LiveExprNode) this.elementAt(0);
			sb.append(liveExprNode.toDotViz());
		}
		for (int i = 1; i < this.size(); i++) {
			sb.append(",\n");
			LiveExprNode liveExprNode = (LiveExprNode) this.elementAt(i);
			sb.append(liveExprNode.toDotViz());
		}
		sb.append("}");
		// properly escape the "/\" to "/\\" or "\A" to "\\A"
		return sb.toString().replace("\\", "\\\\");
	}
}
