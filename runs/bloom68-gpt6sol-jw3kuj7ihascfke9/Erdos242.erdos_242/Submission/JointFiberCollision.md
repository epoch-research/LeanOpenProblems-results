# A pointwise joint-count bound and a collision of the two divisor targets

**Status.** The arithmetic implications identified below are proved without
`sorry` in `JointFiberCollision.lean`; the finite counts and the dyadic
estimate are ordinary, explicitly justified mathematical arguments. Neither
this file nor its Lean companion imports or edits `Spec.lean`. In particular,
**there is no proof that every hard prime has a witness** and no prime
counterexample to Erdős–Straus.

For a prime `p=24k+1`, put `x_j=6k+1+j` and `a_j=4j+3`, for `0≤j<6k`.
Let `I_j` count divisors `c|x_j²` with `a_j|4c+1`, and let `II_j` count
`d|x_j²` with `0<d<x_j` and `a_j|x_j+d`. The existing
`CoveringGap.all_good_iff_explicit_hard_cover` proves that

    C(p) := Σ_{j<6k} (I_j+II_j) > 0

is **equivalent to an ordered decomposition**. Use exactly the corrected
character decomposition of `JacobiCorrectedJointCount.md`:

    C(p)=M(p)+T(p),
    M_j=[3 D_j−(2+s_j) S_j]/[2 φ(a_j)],
    D_j=τ(x_j²), S_j=Σ_{c|x_j²} (c/p), s_j=(x_j/p)∈{±1}.       (1)

Thus the desired `T(p)>−M(p)` **for all hard primes** is exactly the open
pointwise covering assertion, not a consequence of `M(p)>0`.

## An unconditional, pointwise global lower bound (which can be zero)

For any positive integer `n`, define the *finite, character-free* count

    R₃(n) = #{a>0 : a|n and a≡3 (mod 4)}.

For **every** prime `p≡1 (mod 24)`, the full joint count satisfies

    C(p) ≥ R₃(p+1)+R₃(p+4),
    T(p) ≥ −M(p)+R₃(p+1)+R₃(p+4).                             (2)

This is a lower bound on the **complete** error `T(p)`: it sums over
every eligible modulus dividing either shift, while allowing all other
first denominators to contribute nonnegatively. It is not a statistical
average over primes. The proofs of
the individual arithmetic certificates are
`typeI_of_shift_dvd_p_add_one`, `typeII_of_shift_dvd_p_add_four`,
`hard_typeI_of_factor_p_add_one`, and
`hard_typeII_of_factor_p_add_four` in the Lean file.

**Proof of (2).** If `a≡3 (mod 4)` divides `p+1`, it is odd and hence
`a≤(p+1)/2<p`. Take `x=(p+a)/4`; it is an integer with
`p/4<x<p/2`. The divisor `c=x|x²` satisfies
`4c+1=p+a+1≡0 (mod a)`, giving one Type-I pair. Distinct `a` give
distinct `x`. If instead `a≡3 (mod 4)` divides `p+4`, then `a` is a
**proper** divisor: `p+4≡1 (mod 4)`. Since `p>4`, it follows that
`a≤(p+4)/2<p`. The same `x=(p+a)/4` is eligible, and `d=1<x`
divides `x²`; also

    4(x+1)=p+a+4≡0 (mod a).

Since `a` is odd, `gcd(a,4)=1`, so `a|x+1`, yielding one Type-II pair.
Type-I and Type-II pairs are counted separately even if their first
denominators coincide. This proves (2), including all order and range
conditions. No distribution hypothesis was used. In particular (2) gives
`T(p)>−M(p)` whenever its explicit rightmost divisor count is positive.


The explicit gap in (2) can be made arbitrarily large on infinite **selected
families** of hard primes, still pointwise and without averaging. Fix `t≥1`
distinct primes `q₁,…,q_t≡3 (mod 4)` other than `3`, and put
`Q=∏q_i`. CRT gives a reduced class with `p≡1 (mod 24)` and
`p≡−4 (mod Q)`: `gcd(24,Q)=gcd(4,Q)=1`. Dirichlet supplies
arbitrarily large primes in this class. For each of them all `q_i`
divide `p+4`, so `R₃(p+4)≥t` and, by (2),
`T(p)≥−M(p)+t`. These are `t` distinct first denominators with the
explicit Type-II divisor `1`. Choosing the class *after* choosing `t`
says nothing about an arbitrary prime outside it.

The qualification is essential. At `p=193`, both `p+1=2·97` and
`p+4=197` have **no** divisor `3 (mod 4)`, so the correction in (2)
is zero. Nevertheless `x=50`, `a=7`, `c=5` is a Type-I witness
(`5|50²` and `7|21`). The same vanishing of the bound occurs for
`p=2521`: `p+1=2·13·97` and `p+4=5²·101` have only odd prime
factors `1 (mod 4)`, but this prime has witnesses elsewhere. Thus
(2) is not the required strict inequality for every prime. A hypothetical
bad prime must have *all odd prime factors* of both `p+1` and `p+4`
congruent to `1 (mod 4)`, but soluble primes already satisfy this
necessary condition. Its vanishing is **not** evidence of a bad prime.

## When `a|p−1`, Type I and Type II are the *same target*

For an eligible `x` put `a=4x−p`. Assume `a|p−1`. Since `4x=p+a`,

    4x≡1 (mod a),
    a|4c+1  ⇔  a|x+c           for every integer c.             (3)

This elementary equivalence uses `gcd(a,4)=1` and is Lean-proved as
`type_targets_coincide`. Since `gcd(a,x)=1` for a prime `p` and eligible
`x<p`, complementary divisors `c ↔ x²/c` of `x²` preserve the target
class `c≡−x (mod a)`. The fixed point `c=x` is impossible in this
class: it would give `a|2x`, contradicting `a≥3` and `gcd(a,x)=1`.
Therefore exactly half of the matching divisors are below `x`:

    I_x=2 II_x;        I_x+II_x=3 II_x.                       (4)

In particular the **full Type-I and Type-II predicates are equivalent
at that particular `x`**. This is Lean-proved as
`typeI_iff_typeII_of_one_mod` and
`hard_typeI_iff_typeII_of_mod_one`, using the already proved
complementary-divisor lemma in `LocalResidues.lean`. It is not an
all-prime existence statement.

There is a precise consequence for the Jacobi correction. By the proved
transfer `(x/a)=(x/p)` and `x≡4⁻¹=(2⁻¹)² (mod a)`, we have `s_x=+1`.
With the notation in (1),

    M_x=3(D_x−S_x)/(2φ(a)),
    T_x=3 II_x−3(D_x−S_x)/(2φ(a)).                              (5)

If this one fiber has no target divisor, it has `T_x=−M_x` even when
`D_x−S_x` is large: the Jacobi sign does not enforce the exact target.
The two branches in (4) do not provide two independent chances.

The collision can occur simultaneously at **arbitrarily many initial
first denominators of hard primes**. For any `B≥3` put
`L_B=24·lcm(1,2,…,B)`. Dirichlet's theorem gives arbitrarily large
primes `p≡1 (mod L_B)`. For *each* of the
`⌊(B+1)/4⌋` moduli `a=3,7,11,…≤B`, we have `a|p−1`, `a<p`, and
(3)–(5) hold at its eligible `x=(p+a)/4`. This asserts only target
**coincidence**, not target failure or a global error estimate;
primes in the progression may (and do) succeed at other moduli.
It explains why multiplying the Type-I and Type-II local probabilities
as if they were independent cannot be justified uniformly in `p`.

## Exact prime fiber with corrected mass exceeding the unit-group size

The following example is a stricter local cancellation test than merely
having all prime factors quadratic-residue modulo `a`:

    p=3942577,   x=985647=3·13·127·199,   a=4x−p=11.

Here `p≡1 (mod 24)` and `p≡1 (mod 11)`. Primality and the existence of
an ordered solution at the **different** first denominator
`x₀=985645`, `a₀=3`, `c=5` are both checked by the Lean theorems
`collision_3942577_prime` and `collision_3942577_good`.
For a standalone primality certificate,
`p−1=2⁴·3²·11·19·131`; base `5` has `(p−1)`st power `1 (mod p)`
and powers with exponents `(p−1)/q`, for `q=2,3,11,19,131`, equal
respectively `3942576,2604881,343400,399908,2294845` modulo `p`.
All are different from `1`, so its order is `p−1` and `p` is prime.

Modulo 11, the four prime factors of `x` are `3,2,6,1`. Since `2`
has order ten, `3≡2⁸` and `6≡2⁹`. Every divisor of `x²` has residue
`2^(8i+j+9m)` with `0≤i,j,m≤2` (the `199`-exponent is irrelevant).
The possible base exponents `8i+9m (mod 10)` are only
`{0,4,5,6,7,8,9}`. Adding `j∈{0,1,2}` never yields `3 (mod 10)`;
thus **no divisor is `2³=8 (mod 11)`**. By (3), *both* targets are
`−x≡8 (mod 11)`. Hence `I_x=II_x=0` even before imposing `d<x`.

Transfer gives signs `+,-,-,+` on `3,13,127,199` respectively.
Consequently `s_x=+1`, `D_x=3⁴=81`, `S_x=3·1·1·3=9`, and

    E_I(x)=36,  E_II(x)=18,
    M_x=2(36+18)/φ(11)=54/5 > φ(11)=10,
    T_x=−54/5.                                                (6)

All equalities concern **this one fiber**, not the global `T(p)`.
In particular this soluble prime is no counterexample; the actual
Type-I certificate `c=5|985645²` at `a=3` proves otherwise.
The example rules out even a local pigeonhole inference from corrected
mass exceeding the number of unit classes.

## The remaining *pointwise* error, quantified by dyadic blocks

For comparison, the Fourier/Pólya–Vinogradov proof in
`JacobiCorrectedJointCount.md` gives the following **for each single**
prime `p≡1 (mod 24)` with `L=log p≥64`, without averaging over `p`.
For every dyadic `A=2^h` satisfying `p^(3/4)≤A≤p/16`, put
`J_A={x:A≤4x−p<2A}` and `M_A=Σ_{x∈J_A} M_x`. It proves separately
for **each** such `A` that

    M_A ≥ L²/(3·2¹⁵),
    #{such disjoint blocks} ≥ L/(8 log 2),
    M(p) ≥ L³/(3·2¹⁸ log 2).                                 (7)

For completeness, a block has exactly `H=A/4` candidates. On any
interval of at most `p` consecutive integers, Fourier inversion for the
Legendre character (zero Fourier coefficient `0`, other coefficients of
magnitude `√p`) and the geometric-sum inequality
`|Σ_{v=0}^{h−1} exp(2πirv/p)|≤p/[2 min(r,p−r)]` give an
incomplete-interval error at most
`(√p/p)·p H_{(p−1)/2}≤B₀=√p(1+L)`. For coprime
`d,e≤U=⌊A^(1/16)⌋`, put `l=de≤A^(1/8)<p`. Among the `H`
consecutive `x`, at least `H/l−1` are multiples of `l`; their character
sum is bounded in absolute value by `B₀`: write `x=lv` and use
`(l/p)=±1`. Moreover

    H/l ≥ p^(21/32)/4 ≥ 2(1+B₀),

because `p^(5/32)≥8(L+2)` for `L≥64` (check at `L=64`, then use
monotonicity). Thus at least `H/(4l)` of these multiples satisfy
`(x/p)=−1`. Discarding non-coprime pairs via the weighted union bound
and `Σ_{q prime}1/q²<3/4` gives at least one quarter of the unrestricted
harmonic-square weight: here `1/4+Σ_{n≥3}1/[n(n−1)]=3/4` is an
explicit strict upper bound on the prime reciprocal-square sum.
Also `U≥A^(1/16)/2` implies
`log U≥3L/64−log 2≥L/32`. Therefore

    Σ_{d,e≤U, (d,e)=1} 1/(de) ≥ (log U)²/4 ≥ L²/2¹².

The identity `τ(x²)=#{(d,e):d|x, e|x, (d,e)=1}` now yields
`Σ_{J_A,(x/p)=−1} τ(x²)≥H L²/2¹⁴`. Since
`M_x≥4τ(x²)/(3φ(4x−p))` there and `φ(4x−p)<2A`, this gives the
first inequality in (7). The allowable dyadic exponents lie in
`[3L/(4 log 2), L/log 2−4]`, providing at least
`L/(4 log 2)−5≥L/(8 log 2)` disjoint blocks. These are **bounds on
the corrected main, not on witnesses**.

One explicit sufficient pointwise error estimate would be
`T_A(p)>−L²/(3·2¹⁵)` for **any one** of these dyadic blocks: (7)
would then give `Σ_{x∈J_A}(I_x+II_x)>0` and hence a solution. No such
uniform-in-`p` block estimate is proved here.


If `p` were a counterexample, *every* fiber would have `I_x+II_x=0`,
so **every one** of these blocks would have

    T_A=−M_A ≤ −L²/(3·2¹⁵),                                  (8)

and globally `T(p)=−M(p)≤−L³/(3·2¹⁸ log 2)`.
This is a quantitative, pointwise *necessary error pattern*, not a
contradiction: neither the character interval bound nor (2) estimates
the other characters in `T_A`. For example, (6) proves exact
cancellation of a large corrected main on a single prime fiber;
(2) can vanish altogether even at a soluble prime. To conclude for
**every** hard prime one still has to prove `T(p)>−M(p)` (or find a
combinatorial witness) with an additional argument controlling *all*
remaining moduli. No such pointwise estimate is obtained here.
