# An elementary predecessor-shift obstruction to bounded arithmetic induction

**Status.** `InductionCRTBarrier.lean` proves the results below without `sorry`, without importing or editing `Spec.lean`, and with the actual **strictly ordered** predicate `Erdos242.Good`. This is a restriction on proposed bounded-certificate approaches, **not** a proof or counterexample to Erdős–Straus. We use the complete Type-I condition `c | x²`, not merely the subfamily `c | x`.

## An independent base-case lemma

For every integer `t>0`, **no** positive divisor `c | t²` satisfies

    4t-1 | 4c+1.                                               (1)

In fact positivity of `c` follows from `c|t²` and `t>0`. Put `a=4t-1` and `s=t²/c`. The exact polynomial identity

    4s(4c+1) = (4t)²+4s = a(a+2)+(4s+1)                     (2)

shows that `a|4c+1` also forces `a|4s+1`. Since `a=4t-1`, either divisibility implies respectively `c≥t` and `s≥t`. But `cs=t²`, so `c=s=t`. Then `4c+1=a+2`, forcing `a|2`, contradicting `a≥3`. This **elementary** complementary-divisor proof, formalized as `no_one_predecessor_typeI`, needs neither primality nor Jacobi symbols; it is not an assumption that some large integer is prime.

## Predecessor shift: a necessary condition on every Type-I certificate

Write `p=4H+1`. Suppose `p<4x`, `c|x²` and `4x-p|4c+1`. Then

    c ∤ H.                                                     (3)

For if `c|H`, put `t=x-H>0`. We have `x≡t (mod c)`, so `c|t²`, while `4x-p=4t-1`; this contradicts (1). This is `typeI_cofactor_not_dvd_predecessor` in Lean. It does **not** require `p` to be prime, `x<p/2`, or `c≤x`. In particular, trying to carry a cofactor that divides the predecessor `H=(p-1)/4` straight into a Type-I solution for `p` is impossible. It does not rule out other cofactors or Type II.

As a sanity check, the known strictly ordered identity

    4/193 = 1/50 + 1/1450 + 1/27985

has `H=48`, `a=4·50−193=7`, `c=5|50²`, `7|4·5+1`, and indeed `5∤48`. This positive example is not contradicted by (3).

## A simultaneous finite-budget obstruction, even among **soluble** primes

Fix arbitrary natural numbers `B,N` and write `F=(4(B+1))!`. Existing `BoundedTypeIIBarrier.typeI_primes_escaping_bounded_typeII` supplies a prime `p>N` with `p≡1 (mod 840F)` and `Good(p)`, and rules out every Type-II modular witness with `m≤B+1`. Since `840F=4·210F`, we have

    H=(p−1)/4 divisible by 210F.

Every `c` with `0<c≤B` divides `F`, hence `H`; (3) excludes **every** Type-I certificate with such a cofactor, at **every** first denominator with `p<4x`. For any genuine Type-II certificate at an ordered-eligible `x`, the already proved necessary `typeII_modular_parameter` sets `m=(x+d)/(4x−p)>0`, proves `d|m²` and `4m−1|p+4d`, so the supplied prime's modular obstruction forces `m>B`. No bound on `d` or the first-denominator index is being asserted here.

The resulting theorem `good_primes_escape_both_bounded_axes` states **for every** `B,N` that such a prime exists, `p≡1 (mod 840)`, **has a positive strictly increasing three-unit-fraction decomposition**, yet every full Type-I cofactor is `>B` and every full Type-II modular parameter at an ordered candidate is `>B`. Dirichlet's theorem is used by the imported existing prime-progression construction; merely computing many examples would not prove the unbounded existence. Our new base-case and shift arguments are elementary.

This negates any proposed *fixed*, simultaneous bound on these auxiliary parameters as a route to the universal conjecture. It emphatically does **not** negate the conjecture: these primes were chosen to be soluble; their Type-I solutions have large cofactors. Variable/unbounded certificates remain available and necessary.

**Open quantifier.** `CoveringGap.all_good_iff_explicit_hard_cover` still demands that, for each prime `p=24k+1`, there is **some** `j<6k` with `x=6k+1+j`, `a=4j+3`, and either `c>0, c|x², a|4c+1` or `0<d<x, d|x², a|x+d`. Neither a fixed-budget exclusion nor the existence of ordered solutions for one selected infinite prime progression supplies such a certificate for **every** prime; a counterexample would need to rule out both types at **all** eligible `j`. No such proof or counterexample is claimed.

**Verification.** `lake env lean Submission/InductionCRTBarrier.lean` and `lake build Submission.InductionCRTBarrier` succeed. `#print axioms` on the predecessor-shift, progression, and simultaneous-barrier theorems lists only `propext`, `Classical.choice`, `Quot.sound`, no `sorryAx`. Independent exact rational arithmetic checks the ordered `193` example; integer enumeration of the base lemma through `t=1500` provided a diagnostic, not its proof. `Spec.lean` is unchanged and still contains both original `sorry` declarations.
