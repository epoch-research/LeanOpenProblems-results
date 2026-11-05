# Forced prime factors versus an ordered Erdős–Straus certificate

**Status.** `ForcedFactorAudit.lean` proves the explicitly named statements below without `sorry`, and does not import or change `Spec.lean`. They are an audit of several genuinely **forced** factor classes, a conditional ordered construction, and a sharper exact formulation of the **unresolved** covering problem. None gives a decomposition for every prime `p≡1 (mod 24)` or an insoluble prime. Here `Good(p)` means positive **strictly increasing** integer denominators satisfying `4/p=1/x+1/y+1/z`.

## The factors of `p−1` cannot themselves be the missing ingredient

Let `p=24k+1` be prime. For **every** prime `r|p−1`, `(r/p)=+1`. If `r` is odd, `p≡1 (mod r)` and quadratic reciprocity applies because `p≡1 (mod 4)`; for `r=2`, use `p≡1 (mod 8)`. The Jacobi statement, without needing primality of `p`, is `hard_minus_one_prime_factor_residue`.

The existing *full* criterion in `PointwiseJacobi.lean` proves that either Type I (`c|x²`, `a=4x−p|4c+1`) or Type II (`0<d<x`, `d|x²`, `a|x+d`) at an eligible first denominator `x` requires a prime `r|x` with `(r/p)=−1`. Therefore **any** `x| (p−1)^e`, however large `e` is, misses *both full conditions* (`hard_minus_one_supported_no_types`). In particular, the last eligible first denominator

    x=(p−1)/2=12k,       a=4x−p=p−2

**always fails both** (`hard_last_candidate_no_types`). This does not exclude other choices of `x` for the same prime. Notice that even though `3|p−1`, its quadratic character modulo `p` is `+1`, not the required `−1`.

The opposite shift offers a precise conditional construction. If **some divisor** `q|p+1` is `3 (mod 4)`, write

    q=4m−1,        p+1=qt,        x=mt, y=pm, z=pmt.          (1)

Since `p≡1 (mod 4)`, `q` cannot equal `p+1`, so `t≥2`. Also `q≥3`, hence `t<p`; thus `0<x<y<z`. Finally `p+t+1=(q+1)t=4mt`, whence

    1/(mt)+1/(pm)+1/(pmt)=(p+t+1)/(pmt)=4/p.                (2)

`plus_one_product_ordered_triple` checks the explicit denominators and exact rational identity, and `plus_one_product_typeII` verifies the actual Type-II certificate `d=m` (`a=t+1`). `good_of_plus_one_three_mod_four` packages the strictly ordered construction **without requiring `q` to be prime**. The factor **is not guaranteed**: for `p=193`, `p+1=2·97`, and neither prime factor is `3 (mod 4)` (`no_plus_one_three_mod_four_prime_193`). The odd prime factors of `p+1` satisfy `(r/p)=(-1/r)` (`hard_plus_one_odd_factor_character`). Consequently if no prime factor `3 (mod 4)` exists in `p+1`, **every** prime factor of `p²−1=(p−1)(p+1)` is a residue modulo `p`. No eligible `x|(p²−1)^e` can then satisfy either full criterion (`hard_square_minus_one_supported_no_types`). This obstruction holds at the *soluble* prime `193` (`hard_193_square_minus_one_supported_no_types`), where, for example, the existing Type-II witness gives `4/193=1/52+1/772+1/5018`. The Lean theorem `hard_plus_one_solution_or_square_minus_one_barrier` packages this as a genuine **dichotomy**: either an eligible `p+1` factor constructs a solution, or denominators supported on `p²−1` are unusable. It does not assert that the first case must hold.

## Three forced factor residues, none a forced certificate

* **`p−2`.** If `p=24k+1>1`, then `p−2≡3 (mod 4)`, so a prime `q≡3 (mod 4)` **must** divide `p−2` (`hard_minus_two_has_three_mod_four_factor`). There is even a guaranteed **eligible first denominator**: since `q≤p−2` and `p+q≡0 (mod 4)`, take `x=(p+q)/4` to get `p/4<x<p/2` and `a=4x−p=q` (`hard_prime_forced_minus_two_candidate`, directly quantified over every prescribed hard prime). But it is *only a candidate*: one still needs a divisor of `x²` in one of the two exact target classes. In particular, when `a=p−2`, this is precisely the always-impossible endpoint `x=(p−1)/2`. For example `p=193`, `p−2=191` is *itself* prime `3 (mod 4)`, so the forced factor's **only** candidate is `x=96`; both full types fail there (`forced_pminus_two_193_endpoint_fails`). A **proper** factor may work for another prime, but its congruence alone supplies no square-divisor witness.

* **`p²−2`.** For **every odd** `p≥3`, some prime `q≡7 (mod 8)` divides `p²−2` (`square_minus_two_has_seven_mod_eight_factor`). Indeed `p²−2≡7 (mod 8)` forces a prime `3 (mod 4)` factor. For any prime factor `q` of this number, `p²≡2 (mod q)`, so `(2/q)=+1`; a factor `3 (mod 4)` must therefore be `7 (mod 8)`. This is a *proved factor-existence theorem*, not an assumption about arbitrary composites. **It supplies neither the size nor the square-divisor congruence of an Erdős–Straus witness.** At the prime `p=313`, `p²−2=97967` is itself prime `7 (mod 8)` and `97967>p`; it cannot be the ordered modulus `a=4x−p<p`. More tellingly, at `p=97`, `p²−2=23·409` has the small eligible prime factor `q=23≡7 (mod 8)`. Taking `a=q` forces `x=(97+23)/4=30`. Type I would need `c|900` with `c≡17 (mod 23)`; none of the 27 positive divisors of `900=2²3²5²` qualifies. Type II would need `0<d<30`, `d|900` and `d≡16 (mod 23)`; the only possible `d=16` does not divide `900`. The **full local failure** is Lean-checked by `square_minus_two_97_small_factor_fiber_fails`. Nevertheless `97` is good at a different `x`: `4/97=1/34+1/85+1/16490`.

* **`p²+4`.** For **every odd** `p`, some prime `q≡5 (mod 8)` divides `p²+4` (`square_plus_four_has_five_mod_eight_factor`). The odd number `p²+4≡5 (mod 8)` has `(2/(p²+4))=−1`, so some factor has `(2/q)=−1`, i.e. `q≡3` or `5 (mod 8)`. But `q≡3 (mod 4)` cannot divide the primitive sum of two squares `p²+2²`, leaving `q≡5 (mod 8)`. In particular **this forced factor is `1 (mod 4)`**, whereas every eligible `a=4x−p` for a hard prime is `3 (mod 4)`; it cannot simply be set equal to `a`. At `p=313`, `p²+4=97973` is itself prime `5 (mod 8)` and exceeds `p` (`square_shift_313_factor_data` proves both primalities). A different way to use a particular factor as a cofactor would *still* need to verify the full Type-I/II criterion. The prime `313` is in fact good: `4/313=1/90+1/626+1/14085` (proved earlier in `HardTypeIISize.lean`).

The `p+2` shift always has the prime factor `3`; **using it as the modulus `a`** selects the smallest candidate `x=(p+3)/4`. At `p=193`, this is `x=49=7²`; every divisor of `x²=7⁴` is `1 (mod 3)`, whereas both targets demand `2 (mod 3)`. Thus even the **forced** factor `3` fails locally while `193` works at `x=52`. Nor does `p+2` force the `7 (mod 8)` divisor required by the familiar Type-II `t=2` shifted-factor test: `p=12721` is prime and `p+2=3·4241` with prime `4241≡1 (mod 8)`, so **no divisor `5` or `7 (mod 8)`** occurs. Its Type-I solution via another auxiliary factor is checked in `FactorTrisection.lean`. A prescribed prime factor of any of these composites must be proved to have the **exact** required class, size, and square-divisor relation before (1) or `Classification.lean` can be used.

## Why the other proposed forcing mechanisms do not bridge this gap

* **Wilson / Fermat.** Wilson gives `p | (p−1)!+1` and Fermat gives, e.g., `p | 2^(p−1)−1`. The *guaranteed factor `p`* is `1 (mod 4)` and is too large to be an eligible `a<p`, or to divide `x²` as a prime when `x<p`. The identities impose no condition `a|4c+1` with `c|x²` or `a|x+d` with `d|x²`. Other factors of these enormous integers may be useful for particular `p`, but their mere existence does not prove their needed class or link to an eligible `x`. This is a limitation of the stated congruences, **not** a theorem that no ingenious factorial/power method could ever work.

* **CRT.** Selecting congruence classes constructs *selected* infinite prime progressions, not a witness for a prescribed arbitrary prime. The already formalized `CoveringGap.hard_primes_escape_bounded_typeII` even supplies, for any fixed `B`, arbitrarily large hard primes on which **every Type-II parameter `m≤B` fails**. It does **not** rule out larger `m` or Type I, so it is not a prime counterexample.

* **Sum of two squares.** Fermat's theorem supplies `p=u²+v²` for every hard prime, but `GaussianNormBarrier.gaussian_coordinate_factors_residue` proves every prime factor of `uv` is a *residue* modulo `p`. Thus any eligible `x` supported on `uv` fails both full types; `x=uv` itself fails whenever it lies in the eligible interval. An independent **nonresidue** prime can occur in another candidate `x`, but even its existence does not force a divisor into `c≡−4⁻¹ (mod a)` or `d≡−x (mod a)`. The norm does not solve that integrality question.

## The exact remaining pointwise obstruction

`good_iff_hard_omit_forced_endpoint` combines the new endpoint failure with the sharp Type-II size bound already in `HardTypeIISize.lean`. The fully expanded Lean equivalence `all_good_iff_explicit_forced_factor_cover` states that solving the **entire ordered conjecture** is equivalent to the following *unproved* assertion. For **each** prime `p=24k+1`, find **either**

    j+1<6k,  x=6k+1+j,  a=4j+3,
    c>0, c|x², a|4c+1;                                      (I)

**or**

    7j<6k,  x=6k+1+j,  a=4j+3,
    0<d<x, d|x², a|x+d.                                     (II)

Given (I), `Classification.good_of_typeI` yields the **strictly ordered integer** triple `(x, (px+x²/c)/a, (px+p²c)/a)`; given (II), `good_of_typeII` yields `(x, p(x+d)/a, p(x+x²/d)/a)`. A genuine bad prime would have to fail (I) for **all** its eligible `j` and (II) for **all** `j` in its sharp range. Conversely, omitting either branch or checking finitely many primes/CRT classes cannot prove such a counterexample. The Jacobi condition that a successful `x` contains a prime nonresidue `r≥5` is necessary, but its mere presence is insufficient: the `p=97,x=30,a=23` example even has such a factor and fails both target classes. In particular, the *restricted universal rules* “use a `3 (mod 4)` prime factor of `p−2` as `a`” and “use a `7 (mod 8)` factor of `p²−2` as `a`” are refuted by `p=193` and `p=313`, respectively; neither example is a counterexample to Erdős–Straus itself.

**Verification:** `lake env lean Submission/ForcedFactorAudit.lean` and `lake build Submission.ForcedFactorAudit` both succeed. `#print axioms` on the principal factor, construction, obstruction and covering theorems reports only `propext`, `Classical.choice` and `Quot.sound`—no `sorryAx`; `Spec.lean` was not imported or changed. The kernel checks primalities and the finite divisor exclusion at `p=97`; independent exact-rational checks confirm the displayed ordered triples. No finite experiment, density result or forced factor is promoted to a proof of the unproved covering statement.
