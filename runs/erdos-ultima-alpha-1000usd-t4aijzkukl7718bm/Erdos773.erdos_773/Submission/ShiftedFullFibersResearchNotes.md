# Arbitrarily shifted full fibers: collision chains and a two-thirds ceiling

## The original conjecture is still unsettled

Spec.lean is unchanged, with the sole admission at line 2031 for
0 < epsilon <= 1/3. The strongest completed actual lower bound remains
M(N) >= N^(2/3)/500 eventually. No actual original upper or lower exponent
improved, and no original proof or disproof was submitted.

The new two-thirds UPPER bounds below concern a RESTRICTED family of whole
full-fiber constructions. They are not upper bounds on the original maximum.

## Five new verified modules

1. ShiftedProgressionCollision.lean
2. ShiftedFiberOverlap.lean
3. ShiftedFullFiberCapacity.lean
4. FiniteTailCapacity.lean
5. UnequalShiftedFullFibers.lean

All compile without warnings, errors, admissions, or extra axioms and have
built oleans. The 24 printed main audits use only propext, Classical.choice,
and Quot.sound. None imports the admitted Spec theorem.

## 1. Collision chains in every residue class

For q>0, r<q, define index functions

    A_t = 2q t^2 + (6q+2r+1)t + 3q+2r+2,
    B_t = A_t + 2qt + 4q+1,
    C_t = A_t + 2qt + 6q+2r.

They satisfy

    A_t < B_t < C_t < A_(t+1),
    (q A_t+r)^2 + (q A_(t+1)+r)^2
      = (q B_t+r)^2 + (q C_t+r)^2.

The last root of one collision is exactly the first root of the next.
The two-step gap is

    A_(t+2)-A_t = 8qt+20q+4r+2.

`full_shifted_index_bound` proves: if ALL indices s,...,s+H have Sidon
square values (q*i+r)^2 and their largest root is at most N, then

    H^2 <= 1600 N.

The proof chooses the first chain endpoint at or above s. If the next endpoint
also lies in the interval, the displayed collision contradicts Sidonness.
Otherwise the interval length is bounded by a two-step chain gap. The preceding
endpoint controls (qt)^2 by N. The initial endpoint and short-length cases are
included. No primality or coprimality assumption is used here.

`progression_sidon_bound` removes the canonical-residue presentation: for any
starting root a, step q>0, and full progression a,a+q,...,a+qH below N, the same
bound holds if its squares are Sidon. Further APIs:

    progression_start_bound:
      H^2 <= 3200 a + 2560000 q^2;
    progression_card_bound:
      |square values of the progression|^2 <= 3200 N + 2.

These are FULL progression results, not statements about arbitrary partial
index sets.

## 2. Forced overlaps with arbitrary starts

The new argument no longer uses a common prefix starting at index zero.
Let the two full index intervals start at A,B. For positive L, put

    center(q,L,r,A) = q(A+5L)+r.

Take u,v in [L,2L], canonical labels r,s<q, and gcd(q,v)=1. Suppose

    r*u = s*v (mod q),
    |u*center(r,A)-v*center(s,B)| < q L^2.

`close_center_collision` produces endpoint indices a,a+2u in [A,A+10L] and
c,c+2v in [B,B+10L] with an actual common positive square difference.

Proof: the modular match supplies t<q with v*t=r and u*t=s modulo q.
Choose k=floor((A+5L)/v) and the two center indices

    a0=v*k+floor(v*t/q), c0=u*k+floor(u*t/q).

Then q*a0+r=v(q*k+t), q*c0+s=u(q*k+t). The first center is within 2L of
A+5L. The weighted-center hypothesis puts the second within 3L of B+5L.
Subtracting u and v gives nonnegative endpoint indices inside the required
intervals. The common-difference identity follows by expansion.

This is an exact integer construction, not a claim that modular aliases by
themselves are collisions.

## 3. A location-aware finite key and common-length capacity

For a label r with start S_r and a unit gap u, define

    key(r,u) = (r*u mod q,
                floor(u*center(q,L,r,S_r)/(q L^2))).

Equal bins imply the preceding strict center-separation bound. If the ENTIRE
full-fiber union is Sidon, `key_injective` proves this key is injective on R x U.
Importantly, SAME-LABEL matches are also handled by the actual Sidon endpoint
uniqueness. Therefore:

* gaps need not be smaller than q;
* H need not be at most q;
* labels need not be units modulo q.

For common index length H>=10L, with every endpoint root at most N,
`gap_capacity` and `scaled_gap_capacity` prove

    |R| |U| <= q*(floor(2 L N/(q L^2))+1),
    |R| |U| L <= 2N+qL.

The second inequality explicitly accounts for the final bin and the division.
The modulus q is arbitrary in these finite key theorems, provided the supplied
gaps are units.

For q=p^k, the earlier explicit unit-gap selection works in EVERY interval
[L,2L], with |U|=floor((L+1)/2). There is no L<q requirement. Taking L=floor(H/10)
and handling H<10 separately yields `prime_power_capacity`:

    |R| H^2 <= 2400 N.

With square-pair matching of the labels, |R|^2<=2q. If also q<=N, the common-length
whole union has

    |roots|^3 <= 20000 N^2,
    |roots| <= 28 N^(2/3).

`positive_length_card_bound` removes the separately supplied q<=N assumption
when H>0: nonempty containment already implies it, and the empty case is trivial.

## 4. Unequal lengths without a logarithmic loss

`FiniteTailCapacity` proves an independent finite inequality. Let H_i be
nonnegative integer lengths on a finite set S, and A>=|S|. Suppose every positive
integer t satisfies

    |{i in S : t<=H_i}| * t^2 <= A.

Then

    (sum_{i in S} (H_i+1))^2 <= 16 A |S|.

`cutoff_bound` first proves, for each integer T>0,

    sum H_i <= |S| T + A/T.

It telescopes truncated sums. At the step x to x+1, the tail bound implies

    count <= A/x - A/(x+1),

since 1/(x+1)^2 <= 1/(x(x+1)). The final choice is
T=ceil(sqrt(A/|S|)); the empty case is handled separately.

`UnequalShiftedFullFibers` now allows an arbitrary start S_r and arbitrary
length H_r for each label. Its root set is

    union_{r in R} {q(S_r+i)+r : 0<=i<=H_r}.

The intervals remain FULL. Truncate all fibers with H_r>=t to common length t.
Containment preserves Sidonness, so the common-length capacity gives every tail

    |{r in R : t<=H_r}| * t^2 <= 2400 N.

The generic finite inequality and exact cardinality of the disjoint fibers give

    M^2 <= 38400 N |R|,  M = sum_r (H_r+1).

Containment, together with q<=N, gives M*q<=2N|R|. Square-pair matching gives
|R|^2<=2q. Multiplying and cancelling positive q proves

    M^3 <= 153600 N^2,
    M <= 54 N^(2/3).

Public final APIs:

    UnequalShiftedFullFibers.card_bound
    UnequalShiftedFullFibers.real_bound
    UnequalShiftedFullFibers.square_value_bound

The last explicitly transfers the bound to square-value cardinality using
injectivity of squaring on natural roots.

## Essential qualifications

* This supersedes the earlier unhandled ARBITRARY-START gap for actual whole
  prime-power full-fiber unions, including unequal lengths.
* It does NOT extend the earlier weighted alteration-certificate theorems.
* It does NOT cover arbitrary partial fibers. Such sets can omit the explicitly
  constructed endpoints. A Sidon SUBSET of a nonsidon full-fiber union is not
  bounded by these theorems merely because it lies in that union.
* The multi-fiber two-thirds theorem still assumes q is a PRIME POWER and that
  the canonical labels have square-pair matching modulo q. Only the finite key
  lemmas and the single-progression collision chain allow arbitrary q.
* The declared height N must also satisfy q<=N. This follows from any positive-
  length nonempty fiber, but cannot be silently dropped if all lengths are zero.
  With a huge modulus and singleton fibers, dropping it would reintroduce the
  original arbitrary-subset problem.
* Unit LABELS are no longer required. Unit GAPS are used and verified for prime
  powers. These are different conditions.

## Why this does not finish the translated-intersection route

The already verified adjacent-quadratic and root-cube reductions produce
arbitrary sparse base sets, not full intervals. Their hypotheses do not imply
that any of the new forced endpoints are present. They also do not supply the
universal affine-Sidon hypotheses. No near-linear compatible partial-fiber
selector, and no uniform fixed-power upper bound for those sparse sets, has
been obtained.

Thus the new restricted ceiling is not erdos_773.disproof and must never be
substituted for the negation of the original quantified proposition.

## Verification

Build logs:

    /tmp/shifted-progression-final.log
    /tmp/shifted-fiber-overlap-second.log
    /tmp/shifted-full-capacity-fifth.log
    /tmp/finite-tail-capacity-final.log
    /tmp/unequal-shifted-full-final.log

Final independent rechecks:

    /tmp/shifted-progression-recheck.log
    /tmp/shifted-fiber-overlap-recheck.log
    /tmp/shifted-full-capacity-recheck.log
    /tmp/finite-tail-capacity-recheck.log
    /tmp/unequal-shifted-full-recheck.log
    /tmp/spec-shifted-full-check.log

Spec SHA-256 remains
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
