# The full `d∣m²` axis, versus the restricted B-axis

**Status: no universal theorem and no new counterexample prime.** The criterion in the question is **not** the B-axis of `BAxisInvestigation.md`/`BAxis*.cpp`: those files impose `d∣m`. The original modular construction in `Partial.lean` imposes `d∣m²`. The three reported `NO_B` primes are genuine exceptions **only to the former**, and are *not* exceptions to the stated `d∣m²`, `4d<p` condition. The concrete assertions and the bound below have sorry-free proofs in `FullSquareAxis.lean`; no `Spec.lean` edits or universal Erdős–Straus assertions are involved.

## Exact certificates correcting the claimed exceptions

Here `h=4m−1`, `a=(p+4d)/h`, and the resulting ordered denominators are `x=(pm+d)/h`, `y=pm`, `z=pmx/d`. Primality, `p≡1 (mod 24)`, `m≤(p−1)/6`, `d∣m²`, `4d<p`, `h∣p+4d`, and existence of strictly ordered solutions are certified by Lean; the specific displayed triples and their fraction identities were independently checked with exact rational arithmetic. In every row **`d∤m`**, which explains why the restricted B-axis misses it.

| prime `p` | `m` | `d` | `m²/d` | `h` | `a` | `(x,y,z)` |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 193 | 4 | 8 | 2 | 15 | 15 | `(52, 772, 5018)` |
| 2521 | 12 | 16 | 9 | 47 | 55 | `(644, 30252, 1217643)` |
| 66529 | 10 | 50 | 2 | 39 | 1711 | `(17060, 665290, 226996948)` |

For example `193+4·8=225=15·15`, `2521+4·16=2585=47·55`, and `66529+4·50=66729=39·1711`. The existing `good_of_shifted_offset` in `ReciprocityFamilies.lean` produces strictly ordered solutions from each certificate. The known Type-I certificates at `x=50,636,16637`, respectively, are additional solutions, not substitutes for checking the stated condition.

**Search-code caveat.** `BAxisDirectSearch.cpp` and `BAxisCertificate.cpp` use a one-proper-divisor shortcut which is exact for `d∣m`, but false for `d∣m²`: for the prime `337` and `m=8`, both `d=1` and `d=32` divide `m²=64`, meet `4d<337`, and give `31∣337+4d` (`341=31·11`, `465=31·15`). Their `NO_B` reports therefore cannot certify failure of the full condition. Conversely, every *positive* restricted B witness is a full square-divisor witness because `d≤m≤(p−1)/6` implies `4d<p`. Even the certified prime `5179308386761`, whose *first restricted* witness is at `m=1586629` in the notes, has the full witness `(m,d)=(2,4)`: it is `5 (mod 7)` and `7∣p+16`.

## A valid deterministic bound, but not existence

For `p≡1 (mod 24)`, suppose `m>0`, `d>0`, `4d<p`, and `h∣p+4d`. The quotient `a=(p+4d)/h` satisfies `a≡3 (mod 4)`, hence `a≥3`. Thus

    3(4m−1) ≤ ah=p+4d < 2p.

Writing `p=24k+1` gives `m≤4k=(p−1)/6`. This is `full_square_axis_bound` in Lean: the question's `m` restriction is redundant under its other hypotheses. Also `x=(p+a)/4=(pm+d)/h>p/4>d`, so `d∣m²` yields an **ordered** Type-II solution by `good_of_shifted_offset`. The Lean theorem `all_good_of_full_square_axis` confirms that establishing this axis for every hard prime would imply the full ordered Erdős–Straus assertion via `good_of_hard_primes`. The remaining existence problem is to force *some* exact modular divisor; these inequalities do not do that.

For a fixed `m`, `4m≡1 (mod h)`, so the actual arithmetic test is

    d∣m²,    4d<p,    d≡−mp (mod h).                           (1)

Unlike `d∣m`, (1) can have several eligible `d` for one `m`. Any attempted complete `NO_FULL_SQUARE_AXIS` certificate must check **all** divisors of `m²` (or an equivalent complete divisor parametrization), and cover all `m≤(p−1)/6`. In particular, reinterpreting a `BAxis*.cpp` result as such a certificate is invalid.

## Coverage heuristics and what can actually be counted

For fixed `m`, let `A_m(p)` be the *distinct* residues `−4d (mod h)` with `d∣m²` and `4d<p`. In a random-prime model conditioned on `p≡1 (mod 24)`, the eligible probability is the fraction of these residues that are compatible with `p≡1 (mod gcd(24,h))`, **among compatible units modulo `h`**. Counting divisors rather than distinct residues, or using `τ(m²)/h` without these corrections, is not an exact prime probability.

For the coprime moduli at `m=2,3,4`, CRT and the PNT in fixed progressions *do* give independent events in relative-density sense: modulo `7`, the three allowed prime residues are `{3,5,6}` (probability `1/2`); modulo `11`, they are `{7,8,10}` (probability `3/10`); and at `m=4`, modulo `15` together with `p≡1 (mod 3)`, they are `{7,13}` (probability `1/2`). Thus these three tests cover `1−(1/2)(7/10)(1/2)=33/40` of hard primes in relative density: a rigorous lower bound `(33/40+o(1))π(X;24,1)` on primes with full witnesses up to `X`. The shifted-divisor subfamily of `Partial.lean` further gives density one, but neither lower bound covers every prime. For larger `m`, moduli share factors and local events cannot simply be multiplied.

An exact divisor-pair count for any `M≤(p−1)/6` is

    N₂(p;M) = Σ_{m≤M} Σ_{d∣m², 4d<p} [4m−1 ∣ p+4d]
            = D₂(p;M)+R₂(p;M),
    D₂(p;M) = Σ_{m≤M} τ_{<p/4}(m²)/(4m−1),
    R₂(p;M) = Σ_{m≤M} (1/(4m−1)) Σ_{r=1}^{4m−2} e(rp/(4m−1))
                              Σ_{d∣m², 4d<p} e(4rd/(4m−1)),

where `e(t)=exp(2πit)` and `τ_{<p/4}(m²)` counts the eligible divisors. This follows directly from additive-character orthogonality; its diagonal `D₂` is **not a pointwise lower bound**. If `M≤⌊√((p−1)/4)⌋`, there is no truncation and the standard Dirichlet series

    Σ_{m≥1} τ(m²)/m^s = ζ(s)^3/ζ(2s)

and partial summation give

    D₂(p;M) = (log M)^3/(24 ζ(2)) + O((log M)^2).             (2)

By comparison, the `d∣m` diagonal in `BAxisInvestigation.md` is only `Σ_{m≤M}τ(m)/(4m−1)=(log M)^2/8+O(log M)` (including a more precise next term there). Treating different moduli as independent therefore suggests a tiny zero-hit probability for either axis, potentially finite total exceptions. This is a **heuristic**, not a deterministic inequality for each prime. The exact remainder must be shown to exceed `−D₂` for each prescribed prime. `τ(m²)` can overcount residues, even a large divisor set can avoid the specified residue, and the oscillatory sum can cancel the entire positive diagonal.

## Rigorous obstructions to promoting averages to pointwise positivity

1. **Squares really fail the full axis, not just `d∣m`.** Since `gcd(m,h)=1`, each odd prime `r∣m` has Jacobi `(r/h)=(-1/r)(h/r)=(-1/r)^2=1`; when `2∣m`, `h≡7 (mod 8)` gives `(2/h)=1`. Therefore `(d/h)=1` for every `d∣m²`. A modular witness implies `gcd(p,h)=1` and `(p/h)=(-4d/h)=-1`. For `p=s²`, however, `(p/h)=(s/h)^2` is `0` or `1`: contradiction. Hence infinitely many odd composite squares `s²≡1 (mod 24)` are full-axis-free (e.g. `(1000001)²=1000002000001`). They are **not prime counterexamples** and need not be Erdős–Straus counterexamples. For these inputs `R₂=-D₂` for *every* `M`, showing why a uniform off-diagonal bound without a primality-specific ingredient is false.

2. **Prime obstructions at every fixed cutoff.** `Partial.not_one_modular_divisor` proves that `4m−1∤1+4d` for *every* positive `d∣m²`. Take `L_B=840·lcm(1,…,4B)` (the existing Lean theorem instead uses a factorial), and by Dirichlet choose arbitrarily large primes `p≡1 (mod L_B)`. Then every `m≤B` fails (1), with or without `4d<p`. For `p>4B²`, the diagonal in (2) is untruncated and again `R₂(p;B)=−D₂(p;B)` at these **prime** inputs. Chebyshev's `log L_B=O(B)` and Linnik's theorem even yield infinitely many such primes with `B≥c log p` for some absolute `c>0`. This is **not** a failure of the full search up to `m≈p/6`.

3. **Signs are weaker than exact residues.** Reciprocity requires `(h/p)=−1` for a prime witness. Pólya–Vinogradov gives `#{m≤M:( (4m−1)/p )=−1}=M/2+O(√p log p)` when `M≤(p−1)/6`. It shows plenty of *eligible signs* for large `M`, not that the demanded residue `−mp (mod h)` occurs among divisors of `m²`. Already `p=193,m=3,h=11` has `(p/h)=−1`, but `p mod 11=6` while `d∣9` permits only `{7,8,10}`.

4. **An upper-bound sieve is not a pointwise lower bound.** The B-axis shifted-factor and Selberg-sieve estimates in `BAxisInvestigation.md` apply to a **subfamily** of full witnesses. Therefore their upper bounds on the *number* of restricted B-free primes also bound the number of full-axis-free primes. In particular, the notes' bounds of the form `O_C(X/(log X)^C)` (each fixed `C`) and, with averaged prime progressions, `O(X exp(−c√log X))` still tend to infinity. The standard Selberg normalizer for that subfamily has `G(z)≤z`, so its main sifted-count term `X/G(z)≥X/z` cannot by itself fall below `1` in the applicable range `z<X`. Sieve density zero, mean count (2), finite scans, and a Jacobi sign do **not** give a cutoff or a deterministic `N₂(p;(p−1)/6)>0` inequality.

**Conclusion.** The assertion that the three named primes are exceptions to the formula *as written* is false; all three have exact, Lean-checked full-square-divisor witnesses. I found neither a proof that **every** larger hard prime has such a witness nor a new certified prime lacking one, so there is no new Type-I-versus-Type-II counterexample to report. A B-free **prime for the full square axis**, if found with a complete all-`m`, all-divisors certificate and a primality certificate, would refute this stronger claim but would still require a separate Type-I / full-Type-II analysis to address Erdős–Straus. No finite scan is extrapolated here.

Verification: `lake env lean Submission/FullSquareAxis.lean`. The named Lean results are `full_square_axis_bound`, `full_square_axis_193`, `full_square_axis_2521`, `full_square_axis_66529`, and `full_square_axis_two_divisors_at_m8`; no import or edit of `Submission/Spec.lean` was made.
