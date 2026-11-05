# Local 3-adic factors versus the exact Type-II factor ray

**Status:** A genuinely pointwise *obstruction to a proposed method*, not a proof or disproof of Erdős–Straus. `ThreeAdicFactorRay.lean` certifies the finite statements below without `sorry`; `Spec.lean` is unchanged. In particular the test prime **241 is good**.

For a hard prime `p=24k+1`, full Type II has the **necessary and sufficient** modular form (see `TypeIIOffsetBound.full_square_axis_iff_typeII`):

    m,d>0,  4d<p,  d|m²,  h=4m−1 | N_d=p+4d.             (1)

The bound `m≤(p−1)/6` follows from these conditions, not from a restricted search. Full Type I is separate: at some `p/4<x<p/2`, with `a=4x−p`, it requires `c>0`, `c|x²`, and `a|4c+1`.

## What the 3-adic information really gives

Since `p≡1 (mod 3)`, `3|N_d` **exactly when** `d≡2 (mod 3)`. Thus every offset with positive 3-adic valuation lies in the single sequence `d=2+3t`. For any such `d` (regardless of whether `v₃(N_d)=1`),

    N_d = 3(8k+4t+3) = 3(4(2k+t+1)−1).                 (2)

This explicitly forces an `h≡3 (mod 4)` factor, `h=N_d/3`, with `m=2k+t+1`. When `v₃(N_d)=1`, the remaining cofactor is not divisible by 3 and has at least one prime factor `3 (mod 4)`; when the valuation is higher, the factor 3 itself can account for the mod-4 sign. **Neither statement entails `d|m²`.** In fact `x₀=6k+1` obeys `x₀+d=3m`; as `gcd(d,3)=1`,

    d | (2k+t+1)²    iff    d | (6k+1)².                (3)

Indeed `x₀≡3m (mod d)` and `gcd(d,9)=1`, which proves (3). So the automatic cofactor-3 ray succeeds precisely when the *first-fiber* Type-II square divisor exists (with the same `d` and the requisite `4d<p`). The proved `FirstDenominatorNorm.first_denominator_iff_inert_prime_factor` explains why this whole ray fails if every prime factor of `x₀` is `1 (mod 3)`. Taking more values of `t` does not repair that failure.

More generally define `ρ(d)=∏_{q^e||d} q^⌈e/2⌉`. Then `d|m²` iff `ρ(d)|m`. Consequently, **including composites**, a fixed `d>0` with `4d<p` contributes a full Type-II witness exactly if `N_d` has *some* positive divisor on the precise ray

    h ≡ −1 (mod 4ρ(d));     m=(h+1)/4.                (4)

Indeed (4) is equivalent to `h=4m−1` and `d|m²`; together with `h|N_d`, the quotient `a=N_d/h` is `3 (mod 4)` and at least 3, since `N_d≡1 (mod 4)` and `N_d<2p`. This makes `x=(p+a)/4` eligible; `TypeIIOffsetBound.typeII_of_full_square_axis` supplies `d<x`, `d|x²`, `a|x+d` and strictly ordered integer denominators. A valuation or a nonresidue factor gives **no reason** for a divisor to lie in (4).

The proposed `d=2,5,8` demand, respectively, factors `h≡7 (mod 8)`, `19 (mod 20)`, `15 (mod 16)`; requiring only `h≡3 (mod 4)` loses essential information. Searching proper factors of `N_d/3` or combining factors with 3 must *still* satisfy (4).

For a higher pure-power cofactor `a=3^s` with odd `s`, 3-adic divisibility selects `d≡−p/4 (mod 3^s)`; `h=N_d/a` has the correct mod-4 form and corresponds to `x_s=(p+3^s)/4`. Because `d≡2 (mod 3)` and `x_s+d=3^s m`, `d|m²` is again equivalent to the **exact** condition `d|x_s²`. Full Type I at this fiber separately needs `c|x_s²` with `3^s|4c+1`. Neither target is forced by `v₃(N_d)≥s`. For even `s`, `3^s≡1 (mod 4)` and the naive cofactor `N_d/3^s` has the *wrong* mod-4 class: additional factors are needed.

## One prime defeats the entire positive-3-adic Type-II strategy

`p=241=24·10+1` is prime. Here `0<d`, `4d<p` and `3|p+4d` force the **complete** list `d=2,5,...,59` (20 values). Lean proves that **for every one of these offsets and every `m>0`**,

    d | m²  implies  (4m−1) ∤ 241+4d.                (5)

This is `three_adic_offsets_all_miss_at_241`. The proof invokes the existing *necessary* bound `m≤(241−1)/6=40`, then decides the finite set `1≤m≤40`, `d∈{2,5,...,59}` using Lean's kernel-checked `decide` (not `native_decide` or an assumed finite scan). The independent `ThreeAdicFactorRayAudit.py` instead factors **all** `241+4d`, enumerates **all** their positive divisors and checks (4), so it does not restrict to prime factors, `d|m`, or a prescribed cofactor. In particular a longer 3-adic sequence or a different factor of the *same* shifted numbers cannot fix (5) at 241. The corollary `no_typeII_three_divisible_modulus_at_241` rules out full Type II at **every** eligible `x` with `3|(4x−241)`; this uses the necessary modular reduction and the sharp `4d<p` bound.

For the original three offsets, the factor-ray mismatch is visible directly:

| `d` | `N_d` (factorization) | `v₃(N_d)` | `h|N_d`, `h≡3 (mod 4)` | required class for `h` |
|---:|---|---:|---|---|
| 2 | `249=3·83` | 1 | `3,83` (`3,3 mod 8`) | `7 mod 8` |
| 5 | `261=3²·29` | 2 | `3,87` (`3,7 mod 20`) | `19 mod 20` |
| 8 | `273=3·7·13` | 1 | `3,7,39,91` (`3,7,7,11 mod 16`) | `15 mod 16` |

Even the two valuations equal to one do not align. In the last row, `7` is already a `3 (mod 4)` prime factor and combinations with `3` and `13` are included: no allowed factor is `15 (mod 16)`.

The pure-power cofactor fibers `a=3,27` are the **only** eligible `a=3^s` with odd `s` for 241 (`3^5=243>241`). Their respective first denominators are `x=61` and `x=67`, both primes `1 (mod 3)`. Every divisor of either `x²` is `1 (mod 3)`, whereas full Type I needs `c≡2 (mod 3)` and full Type II needs `d≡−x≡2 (mod 3)`. `pure_three_power_fibers_miss_at_241` certifies **both** full-type failures, not merely the offset bound.

**Crucial fallback:** this is **not a bad prime**. At the next fiber, `x=62`, `a=7`, Type II has `d=1|62²` and `7|(62+1)`; equivalently `m=9`, `h=35`, `35|(241+4)=245`, with `3∤245`. Type I also works there with `c=124|62²` and `7|(4·124+1)`. The strictly ordered solution is

    4/241 = 1/62 + 1/2169 + 1/134478.

`three_adic_miss_but_good_241` proves primality, failures at both pure-power fibers, both complete types at 62, and `Good 241`; the Python audit checks the rational identity independently.

**Precise unresolved pointwise obligation:** `CoveringGap.all_good_iff_explicit_hard_cover` still asks, for *each* hard prime, for **some** eligible first denominator satisfying full Type I or Type II. The 3-adic argument forces factors of `p+4d` for `d≡2 (mod 3)` but does not force any factor in (4), nor a Type-I square divisor in its target residue. Prime 241 shows that even using **every** such `d` and **every** corresponding factor will not give a universal Type-II proof; it does not exclude a strategy that also finds Type I or an unrelated Type-II offset, and certainly does not certify a bad prime. No universal covering assertion or complete bad-prime certificate is obtained here.

**Checks:** `lake env lean Submission/ThreeAdicFactorRay.lean`, `lake build Submission.ThreeAdicFactorRay`, and `python3 Submission/ThreeAdicFactorRayAudit.py` all pass. `#print axioms` of the new main theorems lists only `propext`, `Classical.choice`, and `Quot.sound` (no `sorryAx`). The SHA-256 of unchanged `Spec.lean` is `9f079b4c04f5596d6f13a848eb274e32a2235d4fbd9818b0ed22800512ba8c5f`; it is neither imported nor edited.
