# Factorial residues: rigorous obstructions to simple prime-subsequence constructions

## Status

This note does **not** prove or disprove

\[
 |A_p|/p\longrightarrow 1-e^{-1},\qquad
 A_p=\{k!\bmod p:1\leq k<p\}.
\]

It records elementary, uniform bounds derived while investigating subsequence constructions. They rule out several proposed *mechanisms* for producing a density counterexample, not every possible construction. The spacing method is classical; no claim of publication-level novelty is made for these consequences or the affine extension below. No Lean proof of the asymptotic, unproved axiom, or theorem from `Spec.lean` is used. `Spec.lean` was not modified.

Throughout, put \(f(n)=n!\in\mathbb F_p^*\), for the integer representatives \(0\leq n<p\). Adding the index 0 does not change the image, since \(f(0)=f(1)=1\). Thus the collision defect for these \(p\) indices is exactly
\[
 D_p=p-|A_p|.
\]
The conjecture is equivalent to \(D_p/p\to e^{-1}\).

## 1. A varying single gap cannot provide a linear collision certificate

For \(1\leq d<p\), define
\[
 S_d=\{0\leq n\leq p-1-d:f(n+d)=f(n)\},\qquad R_d=|S_d|,
\]
and \(P_h(X)=\prod_{j=1}^h(X+j)\in\mathbb F_p[X]\).

**Proposition 1.** For every integer \(0\leq K<p\), with \(N=p-1-d\),
\[
 R_d\leq\min\left(d,\;1+\left\lfloor\frac{N}{K+1}\right\rfloor+
                    \frac{K(K-1)}2\right).
\]
Consequently,
\[
 R_d\leq 1+\tfrac32(p-1-d)^{2/3}=O(p^{2/3}),
\]
uniformly even when \(d\) is chosen as a function of \(p\).

**Proof.** A root of \(P_d-1\) cannot be one of \(p-d,\ldots,p-1\), since \(P_d\) vanishes at these points. All its roots therefore lie in the admissible interval, and cancellation of \(n!\) shows that these roots are exactly \(S_d\). This proves \(R_d\leq d\).

If both \(n,n+h\in S_d\), cancellation of the four factorials gives
\[
 P_h(n+d)=P_h(n).
\]
For \(1\leq h<p\), the polynomial
\[
 P_h(X+d)-P_h(X)
\]
has degree \(h-1\) and leading coefficient \(hd\ne0\) in \(\mathbb F_p\). In particular,
\[
 \#\{n:n,n+h\in S_d\}\leq h-1.                 \tag{1}
\]
List the elements of \(S_d\) in increasing order. Their consecutive gaps have total length at most \(N\). At most \(\lfloor N/(K+1)\rfloor\) gaps exceed \(K\); by (1), at most
\(\sum_{h=1}^K(h-1)=K(K-1)/2\) gaps are at most \(K\). There are \(R_d-1\) gaps if \(R_d>0\), proving the stated bound. For \(N>0\), take \(K=\lfloor N^{1/3}\rfloor\): then \(N/(K+1)\leq N^{2/3}\) and \(K(K-1)/2\leq N^{2/3}/2\). The case \(N=0\) is immediate. ∎

### Consequences for splitting-prime constructions

* If \(P_d-1\) has \(d\) distinct roots modulo \(p\), then necessarily
  \(d\leq1+\tfrac32(p-1-d)^{2/3}\). In particular, complete splitting with \(d\geq\varepsilon p\) is impossible for sufficiently large \(p\). This is an arithmetic restriction, not merely a weakness of effective Chebotarev.
* The edges \(n\!\!\;--\;n+d\) for \(n\in S_d\) form a forest: on each integer residue class modulo \(d\), they are a subgraph of a path. Thus \(D_p\geq R_d\), but a single gap can supply only \(O(p^{2/3})\) independent equalities.
* A family of \(q\) arbitrarily chosen gaps supplies at most \(O(qp^{2/3})\) edges. Hence \(q=o(p^{1/3})\) gaps cannot supply a linear collision forest.
* All gaps at most \(B\) supply at most \(\sum_{d\leq B}d=B(B+1)/2\) edges. Thus a short-gap construction with \(B=o(\sqrt p)\) also cannot supply a linear collision forest.

These upper bounds concern the specified collision families; they are not upper bounds on the total defect \(D_p\).

## 2. Uniform obstruction for affine transformations of the indices

This extends the single-gap obstruction to index multipliers that can themselves vary arbitrarily with the prime.

For \(a\in\mathbb F_p^*\), \(b\in\mathbb F_p\), \((a,b)\ne(1,0)\), and \(c\in\mathbb F_p^*\), let
\[
 S(a,b;c)=\{x\in\{0,\ldots,p-1\}: f(\langle ax+b\rangle)=c f(x)\},
\]
where angle brackets denote the least nonnegative representative.

**Proposition 2.** Suppose integers \(h,t\) satisfy
\[
 1\leq h<p,\quad 0<|t|<p,\quad ah\equiv t\pmod p,
 \qquad L=h+|t|.
\]
For every integer \(0\leq K<p\),
\[
 |S(a,b;c)|\leq\left\lfloor\frac p{K+1}\right\rfloor+L K(K+1).
                                                        \tag{2}
\]
In particular,
\[
 |S(a,b;c)|\leq 3L^{1/3}p^{2/3}.
                                                        \tag{3}
\]
A pigeonhole choice gives \(L=O(\sqrt p)\), so, uniformly in all the affine-map parameters,
\[
 |S(a,b;c)|=O(p^{5/6}).                                 \tag{4}
\]
If \(a=r/s\pmod p\) for fixed nonzero integers \(r,s\), then one can instead use \(L\leq |r|+|s|\), giving \(O_{r,s}(p^{2/3})\). In particular this applies to translations and reflections, with their intercepts allowed to vary with \(p\).

**Proof of the pair bound.** Let \(S=S(a,b;c)\). We first show
\[
 |S\cap(S-\ell h)|\leq2\ell L\qquad(1\leq\ell<p).       \tag{5}
\]
If \(\ell L\geq p\), this follows trivially. Otherwise set \(H=\ell h\), \(T=\ell t\); then \(H,|T|<p\).

Write \(y=\langle ax+b\rangle\). Exclude the at most \(H\) choices of \(x\) for which \(x+H\) crosses the endpoint \(p\), and the at most \(|T|\) choices for which \(y+T\) leaves \([0,p-1]\). The latter count uses that \(a\ne0\), so \(x\mapsto y\) is a permutation. On the remaining points, both factorial quotients can be expanded without wraparound.

If \(T>0\), two points in \(S\) separated by \(H\) imply
\[
 P_T(aX+b)-P_H(X)=0.
\]
If \(T\ne H\), this polynomial has degree \(\max(T,H)\). If \(T=H\), the congruence \(aH=T\) implies \(a=1\); therefore \(b\ne0\), and its leading nonzero coefficient is \(Hb\) at degree \(H-1\). In either case it is nonzero.

If \(T=-U<0\), the corresponding polynomial equation is
\[
 P_H(X)\prod_{j=0}^{U-1}(aX+b-j)-1=0.
\]
It has degree \(H+U\) and leading coefficient \(a^U\ne0\).

Thus there are at most \(H+|T|=\ell L\) good points and at most \(\ell L\) excluded points. This proves (5).

**From pair counts to (2).** Order the points of \(S\) cyclically along the additive cycle generated by \(h\). Its consecutive gap lengths, measured in steps of \(h\), sum to \(p\). At most \(\lfloor p/(K+1)\rfloor\) gaps exceed \(K\); (5) bounds the number of gaps of size \(\ell\) by \(2\ell L\). Summing proves (2). The empty set is trivial, and for a singleton its one cyclic gap is \(p\), so the argument also covers that case.

If \(L\geq p\), (3) is trivial. Otherwise take \(K=\lfloor(p/L)^{1/3}\rfloor\) in (2). Writing \(z=(p/L)^{1/3}\), the two terms are at most
\(L^{1/3}p^{2/3}\) and
\(Lz(z+1)=L^{1/3}p^{2/3}+L^{2/3}p^{1/3}\), respectively. Since \(L\leq p\), this proves (3).

Finally, for \(p\geq3\), put \(Q=\lceil\sqrt p\rceil\). Place the \(Q+1\) residues \(0,a,\ldots,Qa\) into \(Q\) consecutive bins. Two are in the same bin, providing \(1\leq h\leq Q\), \(0<|t|\leq\lceil p/Q\rceil\), and \(ah=t\pmod p\). Thus \(L\leq2\lceil\sqrt p\rceil\). The prime 2 is harmless. ∎

### Application to multiplicative-order constructions

Let \(\Gamma\leq\mathbb F_p^*\) act on the *indices* by multiplication. By (4), the number of indices having a distinct factorial-equal partner within their \(\Gamma\)-orbit is at most
\[
 O(|\Gamma|p^{5/6}).
\]
Thus, if \(|\Gamma|=o(p^{1/6})\), only \(o(p)\) indices can participate in such within-orbit collisions. In particular, an order-\(O(\log p)\) multiplier cannot cause a positive fraction of collisions by identifying factorials along its index orbits.

For Fermat or Mersenne primes, the order of 2 is \(O(\log p)\). No infinitude of either family is assumed: the assertion is uniform for each prime satisfying the order condition. Even granting an infinite such family would not enable the proposed simple doubling-orbit collapse.

More generally, a union of \(o(p^{1/6})\) arbitrary nonidentity affine bijections supplies only \(o(p)\) collision edges. With uniformly bounded rational slopes, \(o(p^{1/3})\) maps suffice for the same conclusion.

## 3. Small multiplicative subgroups of the values cannot capture linear mass

The *value* subgroup assertion is different from the index-orbit assertion above.

**Proposition 3.** Let \(H\leq\mathbb F_p^*\) have order \(d\), and let \(uH\) be any coset. Then
\[
 \#\{0\leq n<p:f(n)\in uH\}=O(d^{1/3}p^{2/3}),
                                                        \tag{6}
\]
with an absolute constant. Therefore, if \(d=o(p)\), this number is \(o(p)\).

**Proof.** Membership implies \(f(n)^d=u^d\). If both \(n,n+h\) satisfy this equation, then \(P_h(n)^d=1\). The polynomial \(P_h(X)^d-1\) is nonzero of degree \(dh\). Consecutive-gap counting, as in Proposition 1, yields for every \(0\leq K<p\)
\[
 M\leq1+\left\lfloor\frac{p-1}{K+1}\right\rfloor
           +\frac{dK(K+1)}2.
\]
Taking \(K\) of order \((p/d)^{1/3}\) proves (6). ∎

Thus small order of a base such as 2 does not put a positive fraction of factorials in its cyclic subgroup. In fact the displayed bound prohibits that conclusion.

There is also a stronger existing statement for subgroups of general size. The uniform nontrivial multiplicative-character estimate in Garaev–Luca–Shparlinski is
\[
 \left|\sum_{n=1}^{p-1}\chi(n!)\right|\ll p^{7/8}(\log p)^{1/4}.
\]
Expanding the indicator of a coset in the characters trivial on \(H\) gives, uniformly in \(H,u\),
\[
 \#\{0\leq n<p:f(n)\in uH\}
   =|H|+O(p^{7/8}(\log p)^{1/4}).
\]
Thus even a fixed-index subgroup cannot have a positive-fraction excess or deficit of factorial *indices* landing in it. This concerns multiplicities, not the number of distinct factorial values within the coset, and does not imply Stauduhar's conjecture. The elementary bound (6) is better for sufficiently small \(d\) and avoids character-sum machinery.

A useful generalization has exactly the same proof. For nonzero \(P,Q\in\mathbb F_p[X]\), \(r\geq1\), and \(D=\deg P+\deg Q\), let
\[
 S=\{0\leq n<p:Q(n)\ne0,\quad Q(n)f(n)^r=P(n)\}.
\]
Then
\[
 |S|\leq1+\left\lfloor\frac{p-1}{K+1}\right\rfloor
             +DK+\frac{rK(K+1)}2.                     \tag{7}
\]
Indeed, a pair separated by \(h\) is a root of
\[
 P(X)Q(X+h)P_h(X)^r-P(X+h)Q(X),
\]
a nonzero polynomial of degree \(D+rh\). In particular, any family with \(r+D=o(p)\) has \(|S|=o(p)\): first fix \(K\), divide (7) by \(p\), let \(p\to\infty\), and then let \(K\to\infty\).

For fixed \(r,D\), the bound is \(O_{r,D}(p^{2/3})\). Wilson self-collisions reduce to fixed-power equations and hence are sublinear. Fermat's equation \(f(n)^{p-1}=1\) has \(r\asymp p\), so it gives no such restriction and, by itself, no missing values.

## 4. A precise CRT obstruction at fixed rational locations

Fix integers \(a,b,q,d\), with \(q>0\) and \(d\geq2\). Suppose an admissible index is
\(n=(ap+b)/q\). For primes \(p\nmid q\), a short-gap equality \(f(n+d)=f(n)\) implies
\[
 p\mid \prod_{j=1}^d(b+jq)-q^d.                       \tag{8}
\]
The integer on the right is nonzero. To see this, \(P_d(X)-1\) is irreducible over \(\mathbb Q\): if it factored as monic nonconstant integer polynomials \(G H\), then at each of the \(d\) distinct integers \(-1,\ldots,-d\) their integer values multiply to \(-1\), so \(G+H\) vanishes at all \(d\) points. Its degree is less than \(d\), but it cannot be identically zero because both factors are monic. This is a contradiction. In particular \(P_d-1\) has no rational root.

Consequently (8) can hold for only finitely many primes. Putting \(p\) in a fixed arithmetic progression cannot create such a fixed-gap collision at a fixed rational fraction of \(p\) for arbitrarily large primes. Chebotarev can instead select algebraic roots whose integer representatives vary nonlinearly with \(p\), but their number is bounded as in Proposition 1.

## 5. Collision counting must use forest rank, not just the number of pairs

Let \(m_v=\#\{n:f(n)=v\}\). Then
\[
 D_p=\sum_{m_v>0}(m_v-1),\qquad
 C_p=\sum_v\binom{m_v}{2}=\sum_{d=1}^{p-1}R_d.
\]
In general \(D_p\leq C_p\), **not** the reverse. A triple of equal values supplies three pairs but only two units of defect. Multiple gap families can overlap or form cycles.

For any specified graph of certified equalities, the valid lower bound on \(D_p\) is its graphic rank (number of vertices minus number of connected components). A forest with \(E\) edges gives \(D_p\geq E\).

To disprove the conjecture downwards by this method, one needs, on arbitrarily large primes, a collision forest of at least
\[
 (e^{-1}+\varepsilon)p
\]
edges, for some fixed \(\varepsilon>0\). Even an arbitrary positive linear lower bound smaller than \(e^{-1}p\) would not suffice.

For an upward deviation, one needs an upper bound \(D_p\leq(e^{-1}-\varepsilon)p\). Excluding collisions for finitely many, or sublinearly many, gap lengths does not control the rest of the collision graph.

## 6. What the candidate prime constructions do and do not establish

* **Fixed structured factorial differences:** a fixed nonzero integer has only finitely many prime divisors. Varying the indices avoids this trivial obstruction, but a single equality provides only one edge; even all equalities of one varying gap are sublinear by Proposition 1.
* **CRT/Dirichlet:** fixed rational-position constructions satisfy the explicit finite-prime obstruction (8). More elaborate fixed congruence conditions may have global consequences, but merely controlling a bounded prefix and its Wilson reflections does not supply a linear collision forest or an almost-injective full sequence.
* **Chebotarev:** for each fixed degree it can produce infinitely many completely splitting primes. The statement \(\forall B\,\exists\text{ infinitely many }p\) does not imply an infinite sequence with \(B\) comparable to a positive power of \(p\). Controlling all degrees at most \(B\) supplies at most \(B(B+1)/2\) edges, so a direct linear certificate requires at least \(B\asymp\sqrt p\), plus rank control. A single splitting polynomial cannot be rescued by taking degree proportional to \(p\), because Proposition 1 forbids that.
* **Almost-injective primes:** an infinite family with \(D_p=o(p)\) would disprove the proposed limit, but no such family is constructed here. For a fixed prefix length, avoiding the finitely many prime divisors of its factorial differences says nothing about comparability of that length and \(p\).
* **Fermat/Mersenne/small-order primes:** infinitude of the special prime families is not assumed or proved. Even on such primes, small value-subgroup concentration and simple affine index-orbit collapse are ruled out by Propositions 2–3. Other, non-affine mechanisms are not excluded.

No candidate above has yielded either required positive-fraction deviation.

## 7. Literature checked and verification

Available corpus references:

* Cobeli–Zaharescu, *Factorials mod p and the average of modular mappings*, arXiv:2011.07582, Introduction: explicitly states Stauduhar's conjecture and distinguishes it from the proved random-mapping model.
* Klurman–Munsch, *Distribution of factorials modulo p*, arXiv:1505.01198, Introduction and upper-bound section: discusses the Chebotarev subsequence scale \(\gg\log\log p/\log\log\log p\), its GRH analogue \(\gg\log p/\log\log p\), and stronger but still sublinear average bounds. None gives a density deviation.
* Grebennikov–Sagdeev–Semchankau–Vasilevskii, *On the sequence n! mod p*, arXiv:2204.01153; published in Revista Matemática Iberoamericana 40 (2024), 637–648: records the conjecture and proves the lower bound \((\sqrt2+o(1))\sqrt p\), far from the proposed linear asymptotic.
* Garaev–Luca–Shparlinski, *Character Sums and Congruences with n!*, arXiv:math/0403422, theorem `Dist of Values`: contains the classical \(O(N^{2/3})\) single-value-fiber bound by spacing. The generalizations here use that same elementary idea.

Verification used exact symbolic degree/leading-coefficient checks and finite-field tests of the stated inequalities, not a search for exceptional density values. In particular, fixed-gap bounds were checked on every gap for the specified primes 2, 3, 5, 7, 11, 17, 31, 59, 101; affine-fiber bounds were checked in 147,716 exact instances over the specified fields; and the subgroup bound was checked across every subgroup/coset in the selected fields. These checks are supplemental: the proofs above, not the finite tests, establish the general assertions.

## 8. Lean feasibility

The finite propositions require only factorial cancellation in `ZMod p`, polynomial degrees and root-count bounds over a field, finite-set cardinalities, and telescoping consecutive gaps. The affine extension additionally needs a finite pigeonhole approximation and cyclic gap counting. These are feasible standalone lemmas without analytic number theory, unproved axioms, or any import of the conjectured statement. They do **not** fill the asymptotic gap: proving one of the two linear-scale subsequence inequalities in Section 5 remains unresolved.
