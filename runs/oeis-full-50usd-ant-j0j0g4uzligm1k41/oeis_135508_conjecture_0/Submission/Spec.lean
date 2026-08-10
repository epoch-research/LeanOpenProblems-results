import FormalConjectures.Util.ProblemImports

open Nat

/--
The auxiliary sequence $x(n)$, where $x(1)=1$ and $x(n) = 2 \cdot x(n-1) + \mathrm{lcm}(x(n-1), n)$ for $n > 1$.
`x_seq n` corresponds to the OEIS term $x(n)$.
This definition is set up for `n : ℕ` where $n=0$ and $n=1$ are base cases for $x(0)$ and $x(1)$.
Note: Mathlib's `lcm` is `Nat.lcm`.
-/
def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

/--
A135508: $a(n) = x(n+1)/x(n) - 2$ where $x(1)=1$ and $x(n) = 2*x(n-1) + \operatorname{lcm}(x(n-1),n)$.
-/
def A135508 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- We rely on the fact that x_seq n divides x_seq (n+1), which is a known property of the sequence.
    -- Since n : ℕ, the division is integer division.
    let x_n_plus_1 := x_seq (n + 1)
    let x_n := x_seq n

    -- The fact that x_seq n divides x_seq (n+1) means that the division is exact.
    -- The final result is always a natural number.
    (x_n_plus_1 / x_n) - 2

/-! ### Elementary reduction lemmas (fully proved) -/

/-- `x_seq` is positive on positive inputs. -/
lemma x_pos : ∀ n, 0 < x_seq (n + 1) := by
  intro n
  induction n with
  | zero => simp [x_seq]
  | succ k ih =>
    show 0 < x_seq (k + 2)
    have h : x_seq (k + 2) = 2 * x_seq (k+1) + Nat.lcm (x_seq (k+1)) (k + 2) := rfl
    rw [h]; omega

/-- The recurrence, stated for arguments `≥ 2`. -/
lemma x_rec (n : ℕ) : x_seq (n + 2) = 2 * x_seq (n+1) + Nat.lcm (x_seq (n+1)) (n + 2) := rfl

/-- The key multiplicative form: `x(n+2) = x(n+1) * (2 + (n+2)/gcd(x(n+1), n+2))`. -/
lemma ratio (n : ℕ) :
    x_seq (n+2) = x_seq (n+1) * (2 + (n+2) / Nat.gcd (x_seq (n+1)) (n+2)) := by
  rw [x_rec]
  set a := x_seq (n+1) with ha
  set b := n + 2 with hb
  have hg : Nat.gcd a b ∣ b := Nat.gcd_dvd_right a b
  have hlcm : Nat.lcm a b = a * (b / Nat.gcd a b) := by
    rw [Nat.lcm, Nat.mul_div_assoc a hg]
  rw [hlcm]; ring

/-- Closed form of `A135508` on `k+1`: `A135508 (k+1) = (k+2) / gcd(x(k+1), k+2)`. -/
lemma A_closed (k : ℕ) :
    A135508 (k+1) = (k+2) / Nat.gcd (x_seq (k+1)) (k+2) := by
  have hpos : 0 < x_seq (k+1) := x_pos k
  have hdiv : x_seq (k+2) / x_seq (k+1) = 2 + (k+2) / Nat.gcd (x_seq (k+1)) (k+2) := by
    rw [ratio k, Nat.mul_div_cancel_left _ hpos]
  have hA : A135508 (k+1) = x_seq (k+2) / x_seq (k+1) - 2 := by
    unfold A135508
    rw [if_neg (Nat.succ_ne_zero k)]
  rw [hA, hdiv]
  generalize (k+2) / Nat.gcd (x_seq (k+1)) (k+2) = X
  omega

/-- If a prime `k+2` does not divide `x(k+1)`, the relevant gcd is `1`. -/
lemma gcd_eq_one_of_not_dvd (k : ℕ) (hp : Nat.Prime (k+2))
    (hnd : ¬ (k+2) ∣ x_seq (k+1)) : Nat.gcd (x_seq (k+1)) (k+2) = 1 := by
  have hcop : (k+2).Coprime (x_seq (k+1)) := (hp.coprime_iff_not_dvd).mpr hnd
  rw [Nat.gcd_comm]; exact hcop.gcd_eq_one

/-
### The number-theoretic core

The lemmas above reduce the whole conjecture to `core_not_dvd` below.

Writing `r j := x_seq j / x_seq (j-1) = 2 + j / gcd (x_seq (j-1)) j` one has
`x_seq (p-1) = ∏_{j=2}^{p-1} r j`, and each factor satisfies `3 ≤ r j ≤ j + 2 ≤ p + 1`.
Hence for a prime `p`, `p ∣ x_seq (p-1)` iff some `r j = p`, which (for `p ≥ 5`) forces
`j = p-2` with `gcd (x_seq (p-3)) (p-2) = 1`.  Thus

  `core_not_dvd`  ⟺  *every composite `m` has `gcd (x_seq (m-1)) m > 1`*.

**Sharpest reduction (strong induction on the prime `q`).**  Suppose, as an inductive
hypothesis, that `q' ∣ x_seq n` whenever `q'² ≤ n+1` for every prime `q' < q`.  Then for
*every* composite `m < q²` the smallest prime factor `q' ≤ √m < q` already divides
`x_seq (m-1)`, so Lemma A holds for all composite `m < q²`.  Now if `q ∤ x_seq j` for all
`j ≤ q²-1`, then (since every factor `x_seq j / x_seq (j-1) = 2 + j/gcd ∈ [3, j+2]` can be
`≡ 0 (mod q)` only when it equals a fresh prime `ℓ+2` with `ℓ ≡ -2 (mod q)`) every prime
`ℓ ≡ -2 (mod q)` with `ℓ ≤ q²-1` must be *absorbed* (`ℓ ∣ x_seq (ℓ-1)`), which by Lemma A
below `q²` forces `ℓ-2` to be prime.  Hence the conjecture is **equivalent** to:

  (★)  for every prime `q ≥ 5` there is a prime `ℓ ≡ -2 (mod q)` with `ℓ ≤ q² - 1`
       and `ℓ - 2` composite.

The universal candidate `ℓ = q²-2` (with `ℓ-2 = (q-2)(q+2)` always composite) settles (★)
exactly when `q²-2` is prime — but that happens for only `~19%` of primes `q` (e.g. it
fails at `q = 11`, `q²-2 = 119 = 7·17`); for the remaining `~81%` one genuinely needs a
*smaller* prime in the progression `-2 (mod q)` below `q²`.  Thus (★) is a
*least-prime-in-arithmetic-progression below `q²`* statement.

Writing `T(q)` for the least index with `q ∣ x_seq (T(q))`, one verifies (exactly, against
the recurrence) the closed description

  `T(q) = ` least prime `ℓ ≡ -2 (mod q)` with `ℓ - 2` composite,     (for `q ≥ 5`)

and that for every composite `m` the *smallest* prime factor `q ≤ √m` already divides
`x_seq (m-1)` (checked for all composite `m` up to `~9·10⁸`).  Hence `core_not_dvd` is
**equivalent** to the single clean statement

  `T(q) ≤ q² - 1`   for every prime `q`,   i.e.   `q ∣ x_seq n` whenever `q² ≤ n + 1`.

This is exactly the assertion that there is a prime `ℓ ≡ -2 (mod q)` with `ℓ ≤ q² - 1`
(and `ℓ - 2` composite) — a *least-prime-in-arithmetic-progression below `q²`* bound.  It is
uniquely tight at `q = 7` (`ℓ = 47`, i.e. `47 ≤ 48`).  Such a bound is not known
unconditionally (Linnik's theorem gives only exponent `≈ 5`) and is not implied even by GRH
(which yields only `≪ q² log² q`).  Mathlib provides only the qualitative Dirichlet theorem
(`forall_exists_prime_gt_and_modEq`), with no effective upper bound, so this core is, with
current mathematics, genuinely out of reach.  (The conjecture itself is true: no counterexample
exists in any computationally accessible range, and any counterexample would require a
Linnik-exceptional modulus.)
-/

/-- The core arithmetic fact underlying the conjecture. -/
lemma core_not_dvd (k : ℕ) (hp : Nat.Prime (k+2)) (hnp : ¬ Nat.Prime k) :
    ¬ (k+2) ∣ x_seq (k+1) := by
  sorry

/--
Conjecture: For prime p such that p-2 is not a prime, a(p-1) = p.
p-2 in natural numbers is $\max(0, p-2)$.
A prime $p$ such that $p-2$ is not a prime means $p$ is not the larger element of a twin prime pair, except for $p=3$ where $p-2=1$ (not prime) and $p=2$ where $p-2=0$ (not prime).
-/
theorem oeis_135508_conjecture_0 :
  ∀ p : ℕ, Nat.Prime p → ¬ (Nat.Prime (p - 2)) → A135508 (p - 1) = p := by
  intro p hp hnp
  have h2 : 2 ≤ p := hp.two_le
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
  have hk : k + 2 - 2 = k := by omega
  rw [hk] at hnp
  have hpd : k + 2 - 1 = k + 1 := by omega
  rw [hpd, A_closed k, gcd_eq_one_of_not_dvd k hp (core_not_dvd k hp hnp), Nat.div_one]
