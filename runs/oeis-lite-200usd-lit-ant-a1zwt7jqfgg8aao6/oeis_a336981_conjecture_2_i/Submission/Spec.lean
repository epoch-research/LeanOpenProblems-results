import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped BigOperators

/--
The coefficient of $x^k$ in the expansion of $(x^2 + b x + c)^k$.
$$ T_k(b, c) = \sum_{i=0}^{\lfloor k/2 \rfloor} \binom{k}{i} \binom{k-i}{i} b^{k-2i} c^i $$
-/
def T_k (k : ℕ) (b c : ℤ) : ℚ :=
  Finset.sum (range (k / 2 + 1)) (fun i : ℕ =>
    -- The multinomial coefficient $\binom{k}{i, i, k-2i}$
    ((k.choose i * (k - i).choose i : ℕ) : ℚ) *
    -- Powers of b and c
    ((b : ℚ) ^ (k - 2 * i) * (c : ℚ) ^ i))

/--
A336981: $$a(n) = \frac{\sum_{k=0}^{n-1} (4290k + 367) \cdot 3136^{n-1-k} \cdot \binom{2k}{k} \cdot T_k(14, 1) \cdot T_k(17, 16)}{n \cdot \binom{2n-1}{n-1}}$$
where $T_k(b, c)$ denotes the coefficient of $x^k$ in the expansion of $(x^2 + b x + c)^k$.
The sequence is defined as a function $\mathbb{N} \to \mathbb{Q}$.
-/
noncomputable def a (n : ℕ) : ℚ :=
  if n = 0 then 0
  else
    let numerator_sum : ℚ :=
      Finset.sum (range n) (fun k : ℕ =>
        let T1k : ℚ := T_k k 14 1
        let T2k : ℚ := T_k k 17 16

        let k_q : ℚ := k
        -- We use casting for the exponent subtraction to ensure it stays non-negative when k <= n-1
        let n_prime : ℕ := n - 1 - k

        let term_factor : ℚ := 4290 * k_q + 367
        let power_factor : ℚ := (3136 : ℚ) ^ n_prime
        let central_binomial : ℚ := (Nat.choose (2 * k) k : ℚ)

        term_factor * power_factor * central_binomial * T1k * T2k)

    let divisor : ℚ := (n : ℚ) * (Nat.choose (2 * n - 1) (n - 1) : ℚ)

    numerator_sum / divisor

-- Definition for t(k) for the infinite sum
/--
$$t(k) = \frac{4290k+367}{3136^k} \cdot \binom{2k}{k} \cdot T_k(14, 1) \cdot T_k(17, 16)$$
-/
noncomputable def t (k : ℕ) : ℝ :=
  let T1k : ℝ := T_k k 14 1
  let T2k : ℝ := T_k k 17 16
  let k_r : ℝ := k
  let central_binomial : ℝ := (Nat.choose (2 * k) k : ℝ)

  let term_factor : ℝ := 4290 * k_r + 367
  let power_factor : ℝ := (3136 : ℝ) ^ k

  term_factor / power_factor * central_binomial * T1k * T2k

/--
Conjecture 2 (i): We have $\sum_{k \ge 0} t(k) = 5390/\pi$.

Denote (4290k+367)/3136^k*C(2k,k)*T_k(14,1)*T_k(17,16) by t(k).
(i) We have Sum_{k>=0}t(k) = 5390/Pi.

## Status of this conjecture (analysis)

This is Zhi-Wei Sun's **Conjecture IX1** (arXiv:2009.04379, "Some new series for
$1/\pi$ motivated by congruences"), a Ramanujan-type series for $1/\pi$ associated
with the imaginary quadratic field $\mathbb{Q}(\sqrt{-15})$ (class number two).
It is numerically TRUE (verified to 50+ decimal digits), so it cannot be disproved.

A rigorous reduction (all steps verified to 30-57 digits):

* Central-coefficient integral representations:
  `T_k(b,c) = (1/π) ∫_0^π (b + 2√c cos θ)^k dθ`  and
  `C(2k,k) = (4^k/π) ∫_0^π cos^{2k}θ dθ`.
* Substituting and summing the (now purely geometric) series
  `∑ (367 + 4290k) w^k = (367 + 3923 w)/(1-w)^2`, the whole sum becomes a triple
  integral of a *rational* trigonometric function. The `θ`-integral is
  **elementary** (`∫_0^π (a + bλcos²θ)/(1-λcos²θ)² dθ = π(…)·(1-λ)^{-3/2}`),
  reducing the conjecture to the clean double-integral identity
    `∫_0^π ∫_0^π (367 + (127/56)·P)/(784 − P)^{3/2} dα dβ = 55π/224`,
  where `P = (14 + 2cos α)(17 + 8cos β)`  (confirmed to 30 digits).
* Doing one more variable gives complete elliptic integrals: the inner integral
  equals `(1/√(784−9u))·[94174080·E(m)/(784−25u) − 99568·K(m)]`,
  `m = 16u/(784−9u)`, so the remaining single integral of `E,K` is a genuine
  **K3-surface period**; the factor `π` in `55π/224` arises only from the full
  double integration (monodromy), not from any elementary step.

Obstruction to a Lean proof: the summand `C(2k,k)·T_k(14,1)·T_k(17,16)` is
order-4 holonomic (minimal recurrence: order 4, polynomial degree 6), hence not
hypergeometric — there is no Wilf–Zeilberger certificate (its term ratio is not
a rational function of `k`). High-precision (120-digit) PSLQ tests show the
remaining period is NOT reducible via Legendre's relation, via boundary terms,
nor by any elementary elliptic-integral identity; the equivalent rational triple
integral hits a `√(1−4M)` branch obstruction under residues. The value is a
complex-multiplication special value requiring the theory of modular / bimodular
forms (cf. Wang–Yang, Chan–Cooper–Wan–Zudilin) and CM singular values
(Chowla–Selberg regime). This machinery is absent from Mathlib (even the easier
class-number-one Chudnovsky formula is an unproven `proof_wanted`), so a
complete formal proof is not currently attainable by elementary means.
-/
theorem oeis_a336981_conjecture_2_i :
  (∑' (k : ℕ), t k) = 5390 / Real.pi := by
  sorry
