# The greedy-denominator transfer is the original problem, not an induction shortcut

**Status.** `PrimeGreedyTransfer.lean` proves a logical equivalence, a prime-power first-fiber obstruction, and three individual `Good` instances. It does **not** establish the transfer, the conjecture, or a counterexample. It does not import or edit `Spec.lean`.

## Exactly what a prime-induction step would have to say

For a hard prime `p=24k+1`, set `q=(p+3)/4=6k+1`. The proved theorem `all_good_iff_prime_greedy_transfer` is

```
(∀ n>2, Good n)  ↔
(∀ k, (24k+1).Prime → Good (6k+1) → Good (24k+1)).
```

For the nontrivial direction, strongly induct on `n`. If `n mod 24 ≠ 1`, the elementary ordered constructions apply. Otherwise take a prime divisor `p|n`; if `p<n`, induction and scaling solve `n`. If `p=n`, it is a hard prime, and `2<q<p` implies `Good q` by induction. **Only here** is the proposed transfer invoked. Conversely the conjecture plainly implies that transfer. Thus *assuming* a universal `Good q → Good p` lemma assumes an equivalently hard theorem; proving it constructively would be a genuine resolution, not an independent shortcut. The Lean proof retains primality and strict order via `good_outside_24` and `good_mul`.

Two tempting integral transfers demonstrably fail:

* **Homothety.** A known solution `4/q=1/s+1/t+1/u` gives a rational solution for `p` by multiplying all three denominators by `p/q`. Since `p=4q−3`, `q≡1 (mod 3)` and `gcd(p,q)=1`, all three new denominators would be integers only if `q` divided **each** of `s,t,u`. Writing `s=qS,t=qT,u=qU` in the source identity would give `4=1/S+1/T+1/U≤3`, impossible. This rules out componentwise scaling for **every** source solution, not more elaborate transformations.
* **Changing only the greedy first denominator.** From `4/p=1/q+3/(pq)`, a solution with first denominator `q` is equivalent to splitting `3/(pq)` into two unit fractions. If `1/y+1/z=3/(pq)`, then `(3y−pq)(3z−pq)=(pq)²`, and the first positive factor must be a divisor of `(pq)²` that is `−pq≡2 (mod 3)`. If all prime factors of `q` are `1 (mod 3)`, none exists (as `p≡1 (mod 3)`). Conversely, a prime factor `r|q`, `r≡2 (mod 3)`, gives the *strictly ordered* solution

      `x=q, y=p(q+r)/3, z=p(q+q²/r)/3`.

  Here `r<q`, both quotients are integers, and `q<y<z`; the fraction identity follows by combining `1/y+1/z` or by the full Type-II criterion with `a=3,d=r`. Thus this is an exact criterion **at x=q only**, not an all-prime transfer.

## An affine rational action still has an integer gap

There is a completely general ordered *positive rational* transfer. Starting with `4/q=1/s+1/t+1/u`, let `p=4q−3` and set

```
s' = 4spq/(pq+12s),        t'=4t,        u'=4u.
```

Since `1/s'=1/(4s)+3/(pq)`, one has `4/p=1/s'+1/t'+1/u'` and `0<s'<t'<u'`. However,

```
4s−s' = 48s²/(pq+12s).
```

Thus the new *first* denominator is integral **only if** `pq+12s` divides `48s²`. Euclidean or matrix actions on rational solutions do not automatically preserve the integer lattice. For each of the three exact source solutions below, `0<48s²<pq+12s`, so `4s−1<s'<4s`: the rational point is strictly ordered but `s'` is *provably nonintegral*. This disproves this particular action as an integral construction, not all imaginable matrix actions.

## Exact stress tests (none is a counterexample)

Primality, factorization, all displayed strict inequalities, and both fraction identities per row were independently checked using integer factorization and exact `fractions.Fraction` arithmetic. The three `Good q` instances are also `norm_num`-checked in `PrimeGreedyTransfer.lean`; `CoveringGap.lean` already proves `Good p` using the Type-II data in the rightmost column.

| `p` | `q=(p+3)/4` | ordered `Good q` triple `(s,t,u)` | `p` Type-II `(x,a,d)` | ordered `Good p` triple |
|---:|---:|---|---|---|
| 193 | `49=7²` | `(14,147,294)` | `(52,15,8)` | `(52,772,5018)` |
| 2521 | `631` prime | `(158,124662,497859)` | `(638,31,44)` | `(638,55462,804199)` |
| 66529 | `16633` prime | `(4160,10379200,207496675)` | `(17060,1711,50)` | `(17060,665290,226996948)` |

All prime factors of each `q` are `1 (mod 3)`, so neither **full** Type I nor Type II can work at first denominator `q`. The Lean theorem `no_greedy_fiber_of_prime_power` proves this for all prime powers of a prime `1 (mod 3)`; the three specializations `greedy_fiber_*_fails` certify the failures in the table (including primality of 631 and 16633). A later `x` works in each row, with `d|x²`, `0<d<x`, and `a|x+d`: for example `193` has `15|52+8`, `2521` has `31|638+44`, and `66529` has `1711|17060+50`. All these satisfy `p<4x` and `2x<p`. For the affine action, the three `(48s²,pq+12s)` pairs are `(9408,9625)`, `(1198272,1592647)` and `(830668800,1106626777)`.

A second natural action sends the source first denominator to `4s` (since `4(4s)−p=4(4s−q)+3`). For `p=193` it gives `x=56,a=31` with `x=2³·7`; for `2521` it gives `x=632,a=7` with `x=2³·79`. Both full types fail at those *individual* fibers, as every prime factor of `x` is a quadratic residue modulo the respective `a`, while both targets are nonresidues. The analogous fiber `x=16640` for `66529` does work: one cannot extrapolate the two failures to a general no-go theorem.

## Other global-looking input and the obstruction it leaves

* **Euclidean/continued fractions:** `4/p=[0;6k,4]` selects `x=q`, but the failed `x=q` fibers above have no positive divisors in the required residue class. Rational/local factorization `(ay−px)(az−px)=(px)²` must hit *positive integer divisors* congruent to `−px (mod a)`.
* **Norms and three triangular numbers:** the Gaussian norm coordinates of a hard prime contribute only prime factors that are quadratic residues modulo `p` (see `GaussianNormBarrier`), whereas a successful eligible first denominator needs a nonresidue factor. The split Eisenstein norms `q=1²+3·4²=49`, `q=22²+3·7²=631`, `q=85²+3·56²=16633` have only `1 (mod 3)` prime factors, which *prevents* the first-fiber split. Gauss's three-triangular theorem also gives `p+2` as three odd squares: `193+2=1²+5²+13²`, `2521+2=1²+11²+49²`, `66529+2=1²+97²+239²`. These additive representations coexist with the first-fiber failure and supply no congruence for a particular divisor of `x²`; they do not rule out a representation-dependent construction at some other `x`.
* **Analytic averages:** existing shifted-divisor constructions cover a density-one set of hard primes, not each prime. In fact `CoveringGap.hard_primes_escape_bounded_typeII` proves that for *every fixed* bound `B`, arbitrarily large hard primes admit no Type-II witness with modular parameter `m≤B`. Larger `m` or Type I can still succeed. A pointwise, all-prime existence theorem would need to control the exact divisor residues with unbounded parameters, not merely their average density or a character sign.

**Unproved arithmetic step.** `CoveringGap.all_good_iff_explicit_hard_cover` requires for **each** prime `p=24k+1` some `0≤j<6k`, `x=6k+1+j`, `a=4j+3`, and either `c>0, c|x², a|4c+1` or `0<d<x, d|x², a|x+d`. The equivalence proved here and the three worked examples do not furnish such a witness *for an arbitrary hard prime*, nor a prime missing both branches at every eligible `j`. Neither a proof nor a disproof has been found.

Verification: `lake env lean Submission/PrimeGreedyTransfer.lean` succeeds. No `sorry`, added axiom, or import/edit of `Spec.lean` occurs in the new Lean file.
