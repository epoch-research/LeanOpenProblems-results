# A pointwise local-to-positive-integral obstruction (not a counterexample to Erdős–Straus)

`IntegralHasseFiber.lean` is an independent, `sorry`-free Lean proof that does **not** import or modify `Spec.lean`. The prime `p=193=24·8+1` and its minimal eligible first denominator `x=49=6·8+1` give a particularly explicit failure of a **positive-ordered integral local-to-global implication on one fixed fiber**. The original conjecture is **not** refuted: at the *next* denominator `x=50`, there is an ordered solution.

## Rational surface, factor torus, and the exact candidate criterion

For fixed `p,x`, clearing denominators in the rational surface equation gives

    4xyz = p(xy+xz+yz)
        ⇔ a yz = N(y+z),   a=4x−p, N=px
        ⇔ (ay−N)(az−N)=N².                              (1)

The last equivalence uses ordinary polynomial expansion, with `a>0`, and requires **integrality and positivity of the two factors** to reconstruct positive integer denominators. If `y,z>0` solve the middle equality, both factors are positive, since `a/N=1/y+1/z>1/y,1/z`. Their residues modulo `a` must both be `−N`. The rational hyperbola `uv=N²` therefore has rational sections and local points without necessarily having a point in the **finite multiplicative semigroup of positive divisors of `N²`** in the required residue class. The involution `u↦N²/u` preserves that residue when `gcd(a,N)=1`, but does not force a positive divisor into it.

For a hard prime `p=24k+1` (`k≥1`), every ordered first denominator must be `x_j=6k+1+j`, `0≤j<6k`, and `a_j=4j+3`. `Classification.lean` proves the **necessary-and-sufficient** criterion at some such `j`:

* **Type I:** a positive `c|x_j²` with `a_j|4c+1`;
* **Type II:** `0<d<x_j`, `d|x_j²`, `a_j|x_j+d`.

Both alternatives and the whole range of `j` are essential when checking a putative counterexample. The new Lean theorem `no_typeI_or_typeII_193_49` certifies failure of **both** at `j=0` for `193`, not failure for this prime at all `j`.

## A real point, smooth finite-place points, and ordered approximations

For every `k≥1` set `p=24k+1`, `x=6k+1`, and `N=px`; then `a=3`, `N≡1 (mod 3)` and `p>2`. There is an **ordered positive rational point on the same fiber**:

    x < N/2 < N,      4/p = 1/x + 1/(N/2) + 1/N.         (2)

The rational first summands do not imply `N/2` is an integer (in fact `N` is odd for hard primes). There is also an exact **signed** integral point. Put

    Y=(N−1)/3,       Z₀=−N Y.

Then `3Y−N=−1` and `3Y Z₀=N(Y+Z₀)`, while `Z₀<0`. Thus the derivative in `z` of `3yz−N(y+z)` equals `−1`, a unit at **every** finite prime. This one signed integer point supplies smooth integral points at all non-archimedean places; it is outside the positive-ordered real component.

More concretely, `IntegralHasseFiber.hard_first_fiber_smooth_approximation` proves a **uniform pointwise assertion for all `k,m≥1`**. Let

    T=(N+1)Y+1,       Z_m=Y+1+(m−1)T.

Then `x<Y<Z_m`, `3Y−N=−1`, and the defect in the original cleared equation is exactly

    N(Y+Z_m)−3Y Z_m = mT.                                (3)

Consequently for **every** modulus `m≥1` there are honest strictly ordered *positive integers* satisfying the defining polynomial equation modulo `m`, even with a unit Jacobian entry. The combined Lean theorem `ordered_local_not_positive_global_193_49` asserts both this congruence solvability and the failure of an exact positive solution at `p=193,x=49`. This is a modular approximation theorem, emphatically **not** an exact unit-fraction identity. It does not require primes in short intervals, a conjectural squarefreeness statement, or GRH.

## The hard prime `193`: no positive integer point on this fiber

Here `x=49`, `a=3`, `N=193·49=9457=193·7²`. The numbers `7` and `193` are both prime and `1 (mod 3)`, so **every positive divisor** of `N²=7⁴·193²` is `1 (mod 3)`. If positive integers `y,z` satisfied (1), the factor `u=3y−N` would be a **positive** divisor of `N²` but also `u≡−N≡2 (mod 3)`: impossible. This excludes *all positive integer points* on the fiber, a fortiori `49<y<z`. Lean proves both `no_positive_integral_fiber_193_49` and the exact rational-form statement `no_ordered_first_49_at_193`. At the divisor-criterion level, `c,d|49²=7⁴` are `1 (mod 3)`; hence neither `3|4c+1` nor `3|49+d`. The Type-II bound `d<49` is not needed to rule out this particular fiber.

For independent numerical checks, (2) specializes to

    49 < 9457/2 < 9457,
    4/193 = 1/49 + 1/(9457/2) + 1/9457.

The signed integral point and the approximation constants are

    Y=3152,  Z₀=−29808464,  T=29811617,
    Z_m=3153+(m−1)·29811617,
    9457(3152+Z_m)−3·3152·Z_m=m·29811617.

In terms of `u=3y−N`, the signed point chooses `u=−1`, `v=−N²`: **negative** divisors have the required residue `2 (mod 3)`, while positive divisors do not. This is why local congruences on the rational torus miss the sign-sensitive positive-divisor obstruction.

Importantly `p=193` itself is soluble. Its next possible first denominator gives `a=7`, `c=5|50²`, `7|4·5+1`, and the Lean-certified identity

    4/193 = 1/50 + 1/1450 + 1/27985,       50<1450<27985.

This is a **Type-I** witness; the Lean file also checks an ordered triple starting at `52`. Thus the obstruction is to a **specified fiber**, not the full rational surface `S_193`, and is *not* an ordinary integral-Hasse failure for the unrestricted surface (the signed point is already an integral point). We make no assertion about Brauer–Manin conditions, adelic compatibility, or the sufficiency of a stronger local-global principle.

## Validity audit and open gap

`lake env lean Submission/IntegralHasseFiber.lean` succeeds. A separate `#print axioms` audit of the new theorems finds only the ordinary Lean axioms `propext`, `Classical.choice`, and `Quot.sound` (some need only `propext` and `Quot.sound`); there is no `sorryAx`, added axiom, `native_decide`, or import of `Spec.lean`. Exact independent integer/rational checks verify primality of `193`, the five divisors of `49²`, all fifteen divisors of `9457²`, the ordered triple and rational point, and formula (3) for `1≤m≤10000`. The symbolic Lean proof covers **every** positive `m`.

Neither (2), (3), the signed integral point, nor a density/finite computation proves that **every** prime `24k+1` admits an ordered *integer* decomposition. The still-open quantifier is to establish Type I or Type II at **some** `0≤j<6k` for **each** such prime, or to certify a prime for which **both** fail for **every** such `j`. The example `p=193` meets neither description of a counterexample.
