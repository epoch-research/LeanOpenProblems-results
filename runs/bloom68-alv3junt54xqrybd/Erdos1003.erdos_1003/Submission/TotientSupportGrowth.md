# Verified two-sided support-growth barrier

**Status:** Erdős 1003 is not settled here. `Submission/Spec.lean` is unchanged.
The new file `TotientSupportGrowth.lean` proves necessary conditions for a
nested two-sided extension, not the existence of any such extension.

## Exact composite-block accounting

Start with an adjacent collision and its certificate

\[
 n=Rx,\quad n+1=Sy,\quad F=gy,\quad G=gx,
 \qquad x=G/g,\ y=F/g.
\]

Here \(R,S\) are the disjoint squarefree supports, \(F=\phi(R)\),
\(G=\phi(S)\), and \(g=\gcd(F,G)\). Adjoin disjoint squarefree prime
blocks \(A>1,B>1\), without moving old primes between the two sides. Put

\[
 U=\phi(A),\quad V=\phi(B),\quad
 h=\gcd(yU,xV),\quad M=nA.
\]

The new common factor is \(gh\), and the new unit determinant requires

\[
 (n+1)BU=MV+h. \tag{1}
\]

A full certificate additionally requires

\[
 \operatorname{rad}(xV/h)\mid RA,
 \qquad \operatorname{rad}(yU/h)\mid SB.
\]

If all these conditions hold, its integers are
\(N=MV/h\) and \(N+1=(n+1)BU/h\). No primality assumption is made about
the *values* of the blocks; their actual totients are used.

The formal theorem `normalizedExtension_of_adjacent_support_extension`
derives the normalized hypotheses from an actual old collision and a full
extended support certificate. Thus the following bounds do not rely on
assuming away either support condition.

## Overshoot and minimal crossing

Because \(S\ge2\), we have \(2y\le n+1\) and \(y\le n\). Consequently
\(h\le yU<M\), since \(U<A\).

If \((n+1)U\ge M\), then (1) and \(V<B\) give

\[
 MB\le(n+1)BU=MV+h<M(V+1)\le MB,
\]

an impossibility. Therefore

\[
 (n+1)\phi(A)<nA,
 \qquad 2h\le 2yU\le(n+1)U<M. \tag{2}
\]

In particular, if \(A=p\) is a single new prime, then \(p\le n\),
**regardless of how many new primes are present in \(B\)**.
More generally, if all the \(k\) new primes in \(A\) exceed \(L\), then

\[
 \frac1{n+1}<1-\frac{\phi(A)}A
 \le\sum_{p\mid A}\frac1p\le\frac{k}{L+1},
 \qquad L+1<(n+1)k.
\]

Now let \(C\) be any proper divisor of squarefree \(B\), and write
\(B=CD\), \(D>1\). If \((n+1)CU\ge M\phi(C)\), multiplicativity and
\(\phi(D)\le D-1\) imply

\[
 (n+1)CDU\ge M\phi(C)D
 \ge M\phi(B)+M\phi(C).
\]

Equation (1) would give \(h\ge M\phi(C)\ge M\), contradicting (2).
Hence

\[
 \frac{\phi(C)}C>\frac{(n+1)U}{M}
 \quad\text{for every proper }C\mid B,
 \qquad
 \frac{\phi(B)}B<\frac{(n+1)U}{M}.
\]

Thus the restoring block is a **minimal Euler-ratio crossing**, not merely
a block with approximately the desired ratio.

## Sharp prime-splitting obstruction

Define the positive integer

\[
 d=M-(n+1)U,\qquad \theta=M/d>1.
\]

* If \(B=q\) is prime, (1) is \(dq=M-h\). By (2) and \(h>0\),
  \(\theta/2<q<\theta\).
* If \(B\) is composite, every prime \(q\mid B\) is a proper divisor.
  Minimal crossing applied to \(C=q\) gives
  \((n+1)qU<M(q-1)\), hence \(dq>M\), or \(q>\theta\).
  In particular \(B>\theta^{\omega(B)}\).

Let a proposed restoring-prime candidate \(Q<\theta\) turn out composite.
Every prime factor \(q\mid Q\) satisfies \(q\le Q/2<\theta/2\). Such a
prime cannot belong to **any** squarefree restoring block satisfying (1),
even if that block contains arbitrarily many other primes. This is formally
proved as `composite_candidate_factor_excluded`.

This blocks the repair “take any prime factor of the failed prime candidate”
while holding \(A\) fixed. It does **not** rule out genuinely coupled
substitutions which change both \(A\) and \(B\), or constructions which
reassign/discard old primes.

## Verification and remaining gap

The Lean module builds successfully. The principal lemmas, the bridge from
actual support certificates, and the local support-count bound have axiom
dependencies contained in `{propext, Classical.choice, Quot.sound}`. There
is no `sorry`, added axiom, import of `Submission.Spec`, or use of the original
conjecture in the new module.

The missing result is an unconditional mechanism producing (1) **and both
cross-support conditions**, with unbounded combined support. Minimal
crossing and totient-defect accounting alone do not produce determinant one.
Neither infinitude nor its negation has been established.
