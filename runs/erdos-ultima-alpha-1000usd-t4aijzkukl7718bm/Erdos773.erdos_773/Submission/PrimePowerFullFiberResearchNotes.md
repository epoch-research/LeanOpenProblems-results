# Prime-power full-fiber bound

This continuation does NOT settle Erdős 773. The main file and its sole
admission for 0 < epsilon <= 1/3 are unchanged.

## New verified theorem

`PrimePowerFullFiberBound.lean` imports only clean auxiliary modules. Write

    q = p^k,    A = {q*i+r : r in R, 0 <= i <= H},    N = q*(H+1).

Assume p is prime, every label r in R is canonical (r<q) and a unit modulo q,
R has square-pair matching modulo q, and the square values of the ENTIRE set
A are Sidon. Then the new theorems prove

    |A|^3 <= 1200*N^2,
    |A| <= 11*N^(2/3).

`full_value_real_bound` gives the same bound on the number of square values.
There is no restriction H<=q in these final bounds. The exponent k may be
zero; the formulas still hold. There is no odd-prime hypothesis. The unit
hypothesis is gcd(q,r)=1, not the stronger gcd(q,2r)=1.

This extends the restricted actual full-prefix-family bound to prime-power
moduli, including the p^2 modulus of `ParabolaSquareLift`. It does NOT bound
the largest Sidon SUBSET of a full-fiber union: the whole union is assumed
Sidon. It does not apply to arbitrary partial index sets, arbitrarily shifted
index intervals, or arbitrary moduli with multiple distinct prime factors.
No weighted-certificate theorem was newly asserted or needed here.

## Proof and public APIs

* `gap_capacity`: for an arbitrary positive modulus q, choose unit gaps
  U inside [L,2L], where 10L<=H<=q. If the whole union of the full fibers is
  Sidon, the map (r,u) -> r*u mod q is injective on R x U. Thus

      |R|*|U| <= q.

  Same-label matches cancel because r is a unit. A distinct-label match
  invokes the earlier `small_gap_collision`, which puts every required
  endpoint inside the full prefixes. Sidonness then contradicts either the
  positive gap or the distinct canonical residues. Modular pair matching
  is not used in this capacity lemma.

* `unit_gaps`: for q=p^k, at least one of each two consecutive integers is
  a unit modulo q. An explicit injection selects

      U subset [L,2L],    |U| = floor((L+1)/2).

* `short_capacity`: with H<=q, actual Sidonness implies |R|*H<=40q.
  Use L=floor(H/10) when H>=20; smaller H follows from |R|<=q.

* `full_capacity`: for arbitrary H, |R|*(H+1)<=600q. If H>q, truncate to
  index q, giving |R|<=40, and use the earlier explicit within-fiber collision
  to obtain H<15q for nonempty R. The empty case is handled separately.

* Finally PairMatching gives |R|^2<=2q, so

      (|R|*(H+1))^3
        = |R|^2*(H+1)^2*(|R|*(H+1))
        <= 1200*q^2*(H+1)^2.

  The real-power version uses 1200<11^3. Squaring is injective on natural
  roots, hence the square-value cardinality equals the root cardinality.

## Verification

    lake env lean -s 65536 \
      -o .lake/build/lib/lean/Submission/PrimePowerFullFiberBound.olean \
      Submission/PrimePowerFullFiberBound.lean

All seven printed axiom audits use only propext, Classical.choice, and
Quot.sound. The module compiles without warnings or admissions.

Log: /tmp/prime-power-full-fiber-bound.log.
Main-file check: /tmp/spec-prime-power-full-fiber-check.log.
No original lower or upper exponent has improved. No proof was submitted.
