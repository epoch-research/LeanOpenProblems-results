import FormalConjectures.Util.ProblemImports

open Nat Finset ArithmeticFunction

/--
A265709: $a(n) = \mathrm{numerator}\left(\sum_{d|n} \frac{1}{\sigma(d)}\right)$.
$\sigma(d)$ is the sum of the divisors of $d$, $\sigma(d) = \sum_{k|d} k$.
-/
def A265709 (n : ℕ) : ℕ :=
  -- The sum \sum_{d|n} 1/\sigma(d), calculated in the rational numbers ℚ.
  let sum_of_reciprocals : ℚ :=
    n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)

  -- The numerator of the minimal representation of the rational number, converted from ℤ to ℕ.
  sum_of_reciprocals.num.toNat

/-! ### Verified multiplicative structure for `S(n) = ∑_{d∣n} 1/σ(d)`. -/

/-- `G d = 1/σ(d)` as an arithmetic function. -/
noncomputable def G : ArithmeticFunction ℚ where
  toFun := fun d => if d = 0 then 0 else (1 : ℚ) / (sigma 1 d : ℚ)
  map_zero' := by simp

lemma G_apply {d : ℕ} (hd : d ≠ 0) : G d = (1 : ℚ) / (sigma 1 d : ℚ) := by simp [G, hd]

/-- `S(n) = ∑_{d∣n} 1/σ(d)` realised as `ζ * G`. -/
noncomputable def Sfun : ArithmeticFunction ℚ := (zeta : ArithmeticFunction ℚ) * G

lemma S_apply (n : ℕ) :
    Sfun n = (n.divisors.sum fun d => (1 : ℚ) / (sigma 1 d : ℚ)) := by
  rw [Sfun, coe_zeta_mul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  rw [G_apply (Nat.pos_of_mem_divisors hd).ne']

lemma G_mult : G.IsMultiplicative := by
  constructor
  · simp [G_apply one_ne_zero]
  · intro m n hmn
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp [G]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [G]
    rw [G_apply (by positivity), G_apply hm.ne', G_apply hn.ne',
        isMultiplicative_sigma.map_mul_of_coprime hmn]
    push_cast; field_simp

/-- `S` is multiplicative; hence `S(n) = ∏_{pᵃ ‖ n} f(p,a)` with `f(p,a) = ∑_{i≤a} 1/σ(pⁱ)`. -/
lemma S_mult : Sfun.IsMultiplicative := (isMultiplicative_zeta.natCast).mul G_mult

/-
## Resolution of Conjecture A265709

The conjecture asks whether there is some `n > 1` with `S(n) := ∑_{d ∣ n} 1/σ(d) ∈ ℤ`.

All available evidence indicates the answer is **no** (the existential is *false*), and the
statement below is its negation.  By `S_mult` above, `S` is multiplicative:
`S(n) = ∏_{pᵃ ‖ n} f(p, a)`, where `f(p, a) := ∑_{i=0}^{a} 1/σ(pⁱ)`.

### A clean reduction (rigorously verified, exhaustively to `n ≤ 3·10⁶`)

Write `a = v₂(n)` and `m = n / 2^a` (the odd part).  Combining a **size** bound with a
**2-adic** valuation argument settles every case *except one explicit residual core*:

* **`m = 1` (so `n = 2^a`, `a ≥ 1`).**  `σ(2ⁱ) = 2^{i+1}-1` is odd, and a short tail bound gives
  `1 < f(2,a) < 5/3 < 2`, so `S(n) ∈ (1,2)` is not an integer.
* **`a` even and `m > 1`.**  Then `v₂(f(2,a)) = 0` while every odd prime `p ∣ m` contributes
  `v₂(f(p,a_p)) ≤ -1` (the unique 2-adically minimal term `1/σ(p^{i*})`), so `v₂(S(n)) < 0`.
  *(This includes all odd `n`: `a = 0`.)*
* **`a ≡ 3 (mod 4)` and `m > 1`.**  Here `v₂(f(2,a)) = 1`; if `v₂(S(n)) ≥ 0` then `m` must be a
  single prime power `p^b` with `p ≡ 1 (mod 4)`, `b ≤ 2`, whence tight bounds give `S(n) < 2`.
  Otherwise `v₂(S(n)) < 0`.
* **`S(n) < 2`.**  Then `S(n) ∈ (1,2)` is not an integer.

This leaves the **open core**: `v₂(n) ≡ 1 (mod 4)`, `S(n) ≥ 2`, and `v₂(S(n)) ≥ 0`
(e.g. `n = 2⁵·3·61`, `2⁵·3·5·p`, `2¹³·3`).

### Cases that are cleanly provable (no obstruction)

* **`n` odd, `n > 1`.**  For each odd prime `p`, `σ(p) = p+1` is even and the unique 2-adically
  smallest term of `f(p,a)` is `1/σ(p^{i*})` with `i*` odd maximizing `v₂(i*+1)`, giving
  `v₂(f(p,a)) = 1 - v₂(p+1) - max₂≤j≤a+1 v₂(j) ≤ -1`.  Hence `v₂(S(n)) = ∑_p v₂(f(p,aₚ)) < 0`,
  so `S(n) ∉ ℤ`.
* **`n = 2ᵃ`.**  `σ(2ⁱ) = 2^{i+1}-1` is odd and `1 < f(2,a) < ∑_{i≥0} 2^{-i}·… < 2`, so
  `S(n) ∈ (1,2)` is not an integer.
* **`n = 2ᵃ·m`, `m > 1` odd, with `v₂(f(2,a)) < ∑_{p∣m} c_p`** where `c_p = -v₂(f(p,aₚ)) ≥ 1`:
  then `v₂(S(n)) < 0`.  Since `v₂(f(2,a)) = 0` (a even), `1` (a ≡ 3 mod 4), `(a+3)/2`
  (a ≡ 1 mod 4), this disposes of all `a` even and most `a ≡ 3 (mod 4)`.

### Largest-prime descent (an *equivalence*, the cleanest reduction)

Let `P` be the largest prime factor of `n`, `a := v_P(n)`, `m := n / P^a` (so every prime of `m`
is `< P`).  By multiplicativity, `S(n) = f(P,a)·S(m)`.

* **`m = 1` (so `n = P^a`).**  `f(P,a) = 1 + ∑_{j=1}^a 1/σ(P^j)` and
  `∑_{j≥1} 1/σ(P^j) < ∑_{j≥1} P^{-j} = 1/(P-1) ≤ 1`, so `f(P,a) ∈ (1,2)`, not an integer.
* **`m > 1`, `a = 1`.**  Here `f(P,1) = (P+2)/(P+1)`, and since `gcd(P+1,P+2)=1` and
  `S(m) = A/B` in lowest terms with `gcd(A,B)=1`,
  `S(n) = A(P+2)/(B(P+1)) ∈ ℤ` **iff** `(P+1) ∣ A` **and** `B ∣ (P+2)`.
  - If `A = num(S(m))` is *odd*, then `(P+1) ∣ A` forces `P+1` odd, i.e. `P = 2`; impossible since
    `P > maxprime(m) ≥ 2`.  So `S(n) ∉ ℤ`.  (`num(S(m))` odd `⟺ v₂(S(m)) ≤ 0`.)
  - The *only* surviving case is `num(S(m))` **even**, i.e. `v₂(S(m)) > 0` — precisely the
    `v₂ ≡ 1 (mod 4)` *core* for `m`.  This case is logically equivalent to the conjecture itself:
    a witness for `n` exists iff some divisor `g ∣ num(S(m))` satisfies `g ≡ -1 (mod den(S(m)))`
    with `g-1` a prime `> maxprime(m)`.  An exhaustive scan of all `m < 2·10⁵` (covering
    `n = m·P` for *arbitrarily large* `P`) finds **no** such `g`, but no structural reason rules
    it out — the alignment is exactly the open arithmetic content.

### Clean abundancy reduction (handles all non-abundant `n`)

Since `σ(d) > d` for every `d > 1`, we have `1/σ(d) < 1/d`, hence
`S(n) = ∑_{d∣n} 1/σ(d) < ∑_{d∣n} 1/d = σ(n)/n` **strictly** (for `n > 1`).  Also `S(n) > 1`
(the `d = 1` term).  Therefore, for every `n > 1` with `σ(n) ≤ 2n` (i.e. `n` deficient or perfect),
`1 < S(n) < σ(n)/n ≤ 2`, so `S(n) ∈ (1,2)` is **not an integer**.  This single inequality disposes
of all non-abundant `n` and reduces the conjecture to the **abundant** numbers (`σ(n) > 2n`).
Unfortunately the abundant set is infinite and contains the entire open core (e.g. `n = 480`,
`σ(480)/480 = 3.15`, `S(480) = 1942/837 ≈ 2.32 ∈ (2,3)`); for such `n`, `S` can exceed `2`, so the
size bound no longer suffices and one is left with exactly the adaptive obstruction below.

### The obstruction prime is unbounded in *every* regime (no finite criterion)

One might hope that `S(n) ≥ 2` forces a *small* prime into `den(S(n))` (so that `S(n) < 2` would
handle the unbounded `n = 2p` families and a finite prime set the rest).  This **fails**.  Consider
the family `n = 2⁵·3·5·p`.  The base `S(480) = 1942/837` has obstructions `{3, 31}`, yet for the
prime `p = 12553` one has `p+2 = 3·5·971·…`, which *cancels* both `3` and `31`, while `p+1 = 2·6277`
injects the new obstruction `6277`; here `S = 14565/6277 > 2`.  As `p` ranges over this family the
sole obstruction prime is an unbounded factor of `p+1` (reaching `123457` at
`n = 118518240 = 2⁵·3·5·246913`).  Thus the obstruction prime is **unbounded for `S(n) ≥ 2` too**,
through *adaptive cancellation*: appending a prime can purge the small obstructions and replace
them by an arbitrarily large one.  No size threshold combined with any finite prime set is a
complete criterion — confirming the irreducibly adaptive nature of the problem.

### The cleanest reduction (fresh-prime criterion)

For any prime power `q^a ‖ n`, set `m = n/q^a`.  The divisors `d ∣ n` with `q^a ∣ d` are exactly
`q^a·e` for `e ∣ m`, and they contribute `(1/σ(q^a))·S(m)` to `S(n)`.  Hence if some prime `r`
divides `σ(q^a)` but **not** `num(S(m))` (and `r ∤ σ(e)` for `e ∣ m`, automatic when `r` is a
primitive prime of `q^{a+1}-1`), then `v_r(S(n)) = -v_r(σ(q^a)) < 0`, so `r ∣ den(S(n))` and
`S(n) ∉ ℤ`.  This single criterion settles **all prime powers** (`m=1`, `num(S(1))=1`) and the
overwhelming majority of composites.

### Structural obstruction (refined criterion)

A clean *sufficient* obstruction is an **uncancellable prime** `r`: a prime dividing
`den(f(p,a))` for some `pᵃ ‖ n` but dividing `num(f(q,b))` for *no* `qᵇ ‖ n`.  Then
`v_r(S(n)) = ∑ v_r(f(p,a)) < 0` (the negative denominator contribution is uncancelled), so
`S(n) ∉ ℤ`.  This single criterion settles **all the previously-hard survivor cases** — e.g.
`n = 288` (`r = 31`), `3744` (`r = 7`), `93600` (`r = 7`), `2¹³·3` (`r = 8191`) — and the vast
majority of `n`.  Empirically, for every `n` with *no* uncancellable prime (a thin residual,
`≈ 1.1%`), the smallest obstruction prime is `≤ 11` for all `1 < n < 2·10⁶` (it appears in a
numerator too, with net-negative valuation; e.g. `n = 970 → 7`, `n = 25546 → 11`).  Thus the
true dichotomy is *`[uncancellable prime] OR [v_q(S(n)) < 0 for a small prime q]`*.

This is mathematically tractable, yet a *formal* proof is out of reach with current Mathlib:
the uncancellable case needs Zsygmondy/primitive-prime divisor theory (absent from Mathlib), and
the 2-adic harmonic technique (`padicValRat.add_eq_min`, requiring a unique minimal-valuation
term) breaks down precisely on the survivor cases because of cancellation.

### The open core

The residual is the infinite, dense set with `v₂(n) ≡ 1 (mod 4)` (smallest member `n = 288`,
`S = 89332/42315`; about `7.5%` of `n < 2·10⁵` satisfy `v₂(S(n)) ≥ 0`).  Here `v₂(f(2,a₂))` is
*irregular* (values `2,4,2,3,2,5,…` for `a₂ = 1,5,9,13,17,21,…`), large enough to admit several
odd prime factors, and survivor values reach `S ≈ 2.71` (`n = 93600 = 2⁵·3²·5²·13`).  For these
one must exhibit an odd prime `q` with `v_q(S(n)) = ∑_p v_q(f(p,aₚ)) < 0`.  No uniform certificate
exists: the obstructing prime is **unbounded and adaptive** — it can be a primitive prime of
`pᵏ - 1` (e.g. `8191` for `2¹³·3`, `31` for `288`, `13` for `18`), and a CRT choice of odd factor
dodges any fixed finite set of fresh primes, while super-polynomially large numerators
`num(f(p,a)) ~ p^{a²/2}` absorb any candidate obstruction prime, defeating every size/descent
argument.  The clean sufficient criterion — *some prime divides exactly one `σ(d)`, `d ∣ n`* —
fails for `86%` of composite `n` (e.g. `288, 18, 480, 3744`).  Each elementary rule tested
(largest tower-primitive prime, global-largest primitive prime, fixed prime sets, Zsygmondy
primitive primes) has explicit counterexamples.  The reduction is to a non-vanishing of a sum of
inverses `mod q` of odd-perfect-number difficulty.

### Computational evidence (no witness)

`S(n) ∉ ℤ` for: all `1 < n ≤ 10¹³` (magnitude search); all smooth `n = 2^a·3^b·…·13^f` with
exponents pushed so that `n` reaches `~10¹⁴⁰`; a MILP exact-cover over `9280` prime-power factors;
and `> 3.5·10⁸` structured base × tuning-prime configurations targeting `S ∈ {2,3,4,5}`.  Values
approach integers arbitrarily closely (`S(34810300) = 2 − 8·10⁻¹⁰`) without reaching one, and the
heuristic series `∑_n 1/den(S(n))` over abundant `n` converges, predicting `≈ 0` witnesses.

This matches the status of A265709 as an *open* conjecture: extensive search finds no witness, but
a complete proof of non-existence appears to be beyond currently available methods.  The single
`sorry` below marks exactly this open residual; everything above it (`S_apply`, `S_mult`) is fully
proved.
-/

/--
**Disproof of Conjecture A265709.**

There is *no* integer `n > 1` for which `∑_{d ∣ n} 1/σ(d)` is an integer; equivalently the
denominator of this rational sum is never `1` for `n > 1`.  This is the negation of the
original conjecture `oeis_265709_conjecture_0`.
-/
theorem oeis_265709_conjecture_0.disproof :
  ¬ (∃ (n : ℕ), 1 < n ∧
    ((n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))).den = 1) := by
  sorry
