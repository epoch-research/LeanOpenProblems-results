# A norm-to-norm obstruction and three exact shifted norm families

**Status.** `NormShiftDescent.lean` proves the stated polynomial Type-I/II certificates, the conditional square-cofactor construction, and ordered `Good` statements without `sorry` or an import of `Spec.lean`. The elementary inert-prime argument below and the finite first-success searches are ordinary mathematical arguments / independently reproducible integer checks, not additional Lean theorems. **There is no descent for every hard prime, no counterexample prime, and no claim that any quadratic polynomial here has infinitely many prime values. `Submission/Spec.lean` is unchanged.**

## Exactly what the failed first norm says

Let `p=24k+1` be prime, `k>=1`, and put

    N=x₀=(p+3)/4=6k+1,   x_j=N+j,   a_j=4x_j−p=4j+3.

Every ordered solution has one of the first denominators `x_j`, `0<=j<6k`. The necessary-and-sufficient **full** classification from `Classification.lean` is that at one such `j` we must exhibit

    I:   c>0, c|x_j²,             a_j|4c+1,             or
    II:  0<d<x_j, d|x_j²,         a_j|x_j+d.                (1)

At `j=0`, since `N≡1 (mod 3)`, *both* types occur iff `N` has a prime factor `2 (mod 3)`: use that prime as `c` and `d`, and note that it must be `<N`. Conversely either target requires a divisor `2 (mod 3)` of `N²`, hence such a prime. Thus simultaneous failure at `x₀` means **every prime dividing `N` is `1 (mod 3)`**. This is stronger than saying that `N` is a positive Eisenstein norm. For instance `p=97`, `N=25=5²+3·0²` is a norm, but the inert prime `5≡2 (mod 3)` supplies *both* types at `x₀`, with `c=d=5`. By contrast `p=193`, `N=49=1²+3·4²` has a *primitive* norm representation and fails there (even though it also has the nonprimitive representation `7²+3·0²`).

Here is the **precise obstruction to a norm-preserving descent**. Suppose an odd integer `X=A²+3B²` has `gcd(A,B)=1` and `3∤A`. Then every prime factor of `X` is `1 (mod 3)`. Indeed `2∤X`, `3∤X`; if an odd prime `r≡2 (mod 3)` divided `X`, it could not divide `B` (else it would also divide `A`). The element `t=A/B` in `F_r` would satisfy `t²=−3`, so `(t−1)/2` would be a nontrivial cube root of unity. This would force `3|r−1`, a contradiction. **Oddness is essential** for the coordinates `A²+3B²`: the even number `4=1²+3·1²` has coprime coordinates but the inert prime factor `2`. The primitive maximal-order norm `U²−UV+V²` excludes inert primes without this suborder parity caveat.

Now if such an odd primitive norm `X` is any eligible *shifted* first denominator for the same prime `p`, then `X≡p≡1 (mod 3)`. Therefore `3|(4X−p)`, but **every positive divisor of `X²` is `1 (mod 3)`**. Alternative I would require `c≡2 (mod 3)`, and II would require `d≡−X≡2 (mod 3)`: *both are impossible*. The elementary last step, assuming all divisors are `1 (mod 3)`, is Lean-proved as `no_types_if_divisors_one_mod_three`. In particular, moving from one **odd primitive** Eisenstein norm to another cannot itself be the desired descent. For example, at `p=2521`, `N=22²+3·7²=631`; changing `B=7` to `B=9` makes the eligible `X=22²+3·9²=727`, with `j=96` and `a_j=387`, but **both full types still fail**. The basic norm move changes the number, not the required divisor residue.

Escaping the split-prime norm semigroup is not sufficient either. At `p=2521`, `x₁=632=2³·79` has a `2 (mod 3)` factor, but `a₁=7`. All divisors of `632²` are `1,2,4 (mod 7)`, whereas **both** actual targets are `5 (mod 7)` (`−4⁻¹≡−632≡5`), so I and II fail. An inert factor of the shifted `x`, even starting from a positive norm `N`, supplies neither exact divisibility in (1).

## An explicit full-Type-I square-cofactor identity

The following template is useful for producing *actual* certificates rather than only character signs. Let `r,u,a>0`, `a<2ru` and `a | 4ru²+1`. Define

    x=ru,       p=4ru−a,       c=ru²,       y=r(pu+1)/a,
    z=pu·y.                                                   (2)

Here `c|x²` with complementary factor `x²/c=r`, even if `c∤x`. The quotient defining `y` is integral since `pu+1=4ru²−au+1`. Furthermore `p>a`, so `x<y`, and `pu>1`, so `y<z`; directly,

    1/x+1/y+1/z = 1/(ru)+a/(pru) = (p+a)/(pru) = 4/p.

The existence of these strictly ordered denominators is formalized by `good_of_square_cofactor` (via the full Type-I criterion). For a hard prime whose *first* norm is `N`, this template would yield a solution at `x=N+j` if one can find a factorization `N+j=ru` with `a=4j+3` and `a|4ru²+1`. **The norm `N=A²+3B²` does not force this last congruence.** It is exactly an arithmetic constraint to solve, not a consequence of positivity or unique factorization in `Z[ω]`.

## Three infinite parameterized norm identities, not a covering

In **each** family below `N=A²+3B²` is odd and primitive with `3∤A`; hence every prime factor of `N` is `1 (mod 3)`. Also `p=4N−3≡1 (mod 24)`. The identities and strict order hold for **every** nonnegative integer parameter, without assuming `p` is prime. When it *is* prime, its first denominator `N` fails both types and the displayed later denominator succeeds. The prime-input statement is conditional; infinitude of primes represented by these quadratic polynomials is **not asserted**.

**Shift `j=1`, including `p=193`.** For `s>=0`, set

    t=5s+2,  A=1,  B=2t,  N=1+12t²,
    q=10+48s+60s²,    N=5q−1,    p=20q−7,
    x=N+1=5q,       a=7,       c=5.

Then `c|x²`, `7|4c+1=21`, and the *specific* ordered identity is

    4/p = 1/(5q) + 1/[5q(3q−1)] + 1/[5p(3q−1)].           (3)

At `s=0`, this reads `p=193`, `N=49`, `x=50`, `(x,y,z)=(50,1450,27985)`. `norm_one_shift_family` checks the entire Type-I/`Good` family in Lean.

**Shift `j=5`, including `p=2521`; both branches genuinely require `x²`.** Put

    A=22+1932s,  B=7,  N=A²+147,
    w=2+308s+13524s²,    u=23w+7,
    N=12u−5,  p=1104w+313,  x=N+5=12u,  a=23.

Both of the **full** targets in (1) hold, with `c=9u` and `d=8`:

    x²=(9u)(16u)=8(18u²),
    4c+1=23(36w+11),       x+d=23(12w+4).               (4)

Yet `c∤x`; also `w` is even, `u` is odd, `x≡4 (mod 8)`, so `d∤x`. The Type-II branch yields the explicit ordered denominators

    x=12u,     y=4(3w+1)p,     z=6(3w+1)u p.              (5)

For `s=0`, `w=2`, `u=53`, `p=2521`, `N=631`, `x=636`, `c=477`, `d=8` and `(x,y,z)=(636,70588,5611746)`. The **first four** candidates fail; the shift-five one is the first success. The generic theorem `twenty_three_both_types_and_good` and the norm specialization `norm_five_shift_family` verify (4) and an ordered solution for every `s`; the specified Type-II fraction at `s=0` is also Lean-checked. Restricting either branch to divisors of `x` would miss *both* certificates at this first successful fiber.

**Shift `j=4`, including the Type-I-only first success at `p=66529`.** For `s>=0`, let

    A=85+405384s, B=56, N=A²+9408,
    t=6+28560s+68104512s²,  q=19t+17,
    N=127q−4, p=508q−19, x=N+4=127q, a=19,
    c=127q² > x.

Now `c|x²`, and `q≡−2 (mod 19)` gives `19|4·127q²+1`. Also `19|pq+1`. Thus **full Type I**, with its cofactor larger than `x`, gives the strictly ordered identity

    4/p = 1/(127q) + 1/[127(pq+1)/19]
          + 1/[pq · 127(pq+1)/19].                         (6)

Indeed the last two fractions sum to `19/(px)`. At `s=0`, `q=131`, `p=66529`, `N=16633=85²+3·56²`, `x=16637=127·131`, `c=127·131²=2179447`; (6) is

    4/66529 = 1/16637 + 1/58254900 + 1/507708871715100.

At this first successful `j=4`, **no Type-II divisor exists**, and `c∤x`: since `x=127·131`, the only divisors of `x²` strictly below `x` are `1,127,131,127²`; their residues modulo 19 are `1,13,17,17`, none the required `−x≡7`. Both the infinite conditional family and the displayed exact fraction are Lean-checked (`norm_four_shift_family`, `norm_shift_66529_typeI_explicit`); the finite earlier misses and Type-II absence are independently checked by `NormShiftAudit.py`.

## Stress tests and the unresolved descent

A larger, independent example excludes *all* constant-shift assertions up to 25: the **prime** `p=8803369` has `N=2200843=1480²+3·59²`, itself prime `1 (mod 3)`. Exhausting every divisor of `x_j²` for both full targets finds the **first** success only at `j=26`:

    x=2200869=3²·11²·43·47,  a=107,  d=121=11²,
    107 | x+d=2200990,
    4/8803369 = 1/2200869 + 1/181085300330
                + 1/3293760527702370.                   (7)

Lean independently certifies both primalities, the displayed norm, the full Type-II witness and the exact ordered identity (`norm_shift_8803369_prime_data`, `_typeII`, `_explicit`). The self-contained Python audit uses trial-division primality checks, exact divisor lists, and `Fraction`; it checks *all* `j<26`, not merely selected norm shifts. **The absence of earlier witnesses is verified by that finite script, not by a Lean theorem.** This is a finite counterexample to proposed early-shift bounds, *not* evidence of unbounded first-success indices and emphatically not an ESC counterexample.

Even knowing a nonresidue factor of a shifted `x` does not settle (1). At `p=66529`, the twisted-norm factor `19` is a quadratic nonresidue, and its first in-range multiple after `N` is `x=16644=N+11=2²·3·19·73`, `a=47`. Yet all **135** divisors of `x²` miss the two exact residues `−4⁻¹≡35` and `−x≡41 (mod 47)` (their set of nonzero residues misses `{35,41,44}`). Thus both complete types fail **at that x**, even though the same prime succeeded earlier at `j=4`. The exact cofactor condition, not a norm representation, the existence of a nonresidue, or divisor-count positivity, is the missing ingredient.

The still-unproved all-prime quantifier is precisely: **for every** hard prime with a split-prime norm `N=x₀`, find *some* `0<=j<6k` for which one of the actual divisors in (1) exists. The three congruence strata and the square-cofactor template are conditional constructions, not an exhaustion of all primitive norms. Staying within primitive norms is impossible; exiting their semigroup is easy, but does not force either exact divisor target. A proof of this pointwise covering (or a certified prime failing it at *every* `j`) would resolve the open conjecture, and is not given here.

Verification: `lake env lean Submission/NormShiftDescent.lean`, `lake build Submission.NormShiftDescent`, and `python3 Submission/NormShiftAudit.py` succeed. The new Lean theorems have only the standard `propext`, `Classical.choice`, `Quot.sound` axioms, with no `sorryAx`; `Spec.lean` was not edited.
