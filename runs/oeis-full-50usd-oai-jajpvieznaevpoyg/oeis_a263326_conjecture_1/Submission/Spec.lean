import FormalConjectures.Util.ProblemImports


set_option maxRecDepth 10000

open Nat Rat Finset

/--
A263326: Denominator of the rational number $\sum_{d|n} \frac{1}{d+1}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if hn : n > 0 then
    (Finset.sum (Nat.divisors n) fun d : ℕ => (d.cast + 1 : ℚ)⁻¹).den
  else 0

-- Definition of the generalized sum from the conjecture
/--
The generalized sum $\sum_{d|n} \frac{1}{(d+k)^s}$ for $n, k, s \in \mathbb{N}$.
We require $n>0$ for the set of divisors to be non-empty, and $k, s > 0$ from the conjecture's context.
Since $d \ge 1$ for $d \in \mathrm{divisors}(n)$ when $n>0$, the denominator $d+k$ is non-zero.
-/
noncomputable def sum_divisors_inv_pow (n k s : ℕ) : ℚ :=
  Finset.sum (Nat.divisors n) fun d : ℕ => (d.cast + k.cast : ℚ)⁻¹ ^ s

/--
A263326 Conjecture: For any positive integers k and s, all the numbers
$\sum_{d|n} \frac{1}{(d+k)^s}$ (n = 1,2,3,...) have pairwise distinct fractional parts,
and none of them is an integer.
-/
theorem oeis_a263326_conjecture_1.disproof :
  ¬ (∀ (k s : ℕ), k > 0 ∧ s > 0 →
  (∀ n : ℕ, n > 0 →
    -- The value is not an integer
    (Int.fract (sum_divisors_inv_pow n k s) ≠ 0))
  ∧
  -- The fractional parts are distinct for distinct n
  (∀ n₁ n₂ : ℕ, n₁ > 0 → n₂ > 0 → Int.fract (sum_divisors_inv_pow n₁ k s) = Int.fract (sum_divisors_inv_pow n₂ k s) → n₁ = n₂)) := by
  intro h
  obtain ⟨_, hdist⟩ := h 31 1 (by norm_num)
  have hdiv5 : Nat.divisors 5 = {1, 5} := by
    decide
  have hdiv1829 : Nat.divisors 1829 = {1, 31, 59, 1829} := by
    decide
  have hfract :
      Int.fract (sum_divisors_inv_pow 5 31 1) =
        Int.fract (sum_divisors_inv_pow 1829 31 1) := by
    norm_num [sum_divisors_inv_pow, hdiv5, hdiv1829]
  have hbad : (5 : ℕ) = 1829 := hdist 5 1829 (by norm_num) (by norm_num) hfract
  norm_num at hbad
